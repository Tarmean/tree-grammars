{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Fuse foldr/map" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
-- | A Tree grammar closely corresponds to haskell data-types.
-- Each rules maps to a set of constructors:
--
--
-- @
-- data Tree = Leaf | Node Tree Tree
--
-- 0 -> Leaf() | Node(0, 0)
-- @
--
-- Each symbol/type produces a family of terms:
--
-- @
-- 0 -> Leaf() | Node(Leaf(), Leaf()) | Node(Leaf(), Node(Leaf(), Leaf())) | ...
-- @
--
-- The constructor names are important, but type-names are not. If two types
-- have the same structure, we treat them as equivalent.
--
-- Tree-Grammar support many algorithms regular grammars allow:
--
-- - union
-- - intersection
-- - minimization
--
-- If we add a rule:
--
-- @
-- 1 -> Leaf() | Node(1,0)
-- @
--
-- We can minimize the grammar to learn that 1 is equivalent to 0, e.g. produces the same family of terms.
module Data.TreeGrammars (module Data.TreeGrammars) where


import qualified Data.Vector.Unboxed as V
import qualified Data.Map.Strict as M
import Control.Monad.State
import qualified Data.List as List
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM

import qualified Data.Graph as Gr
import qualified Data.IntSet as IS
import Control.Applicative
import Data.Ord (comparing)
import Data.Foldable (minimumBy)
import Control.Arrow ((&&&))

type NonTerminal = Int
type ComponentId = Int

data Cons f a
   = Cons
   { consTag :: !a
   , argTags :: f
   , consArgs :: {-#UNPACK #-}!(V.Vector NonTerminal)
   } deriving (Eq, Ord, Show)

-- data Tagged f = Tagged { tag' :: !f, nonTerminal' :: !NonTerminal } deriving (Eq, Ord, Show)

-- | A collection of gree grammar rules
type TGRules f a = IM.IntMap (M.Map a (Cons f a))

-- | A summary of a strongly connected component
newtype ComponentMeta f a = CM { consCounts :: M.Map (a,f) Int }
  deriving (Eq, Ord, Show)
-- | Content of a strongly connected component
data Component = Component { componentId :: ComponentId, componentRefs :: IS.IntSet, memberNodes :: {-#UNPACK#-}!(V.Vector NonTerminal) }
  deriving (Eq, Ord, Show)
type TGComponents f a = M.Map (ComponentMeta f a) [Component]

data TreeGrammar f a = TG { tgRules :: !(TGRules f a), tgComponents :: !(TGComponents f a) }
  deriving (Eq, Ord, Show)

toGraph :: TGRules f a -> (Gr.Graph, Gr.Vertex -> (M.Map a (Cons f a), NonTerminal, [NonTerminal]), NonTerminal -> Maybe Gr.Vertex)
toGraph rules = Gr.graphFromEdges $ do
    (nt, cons) <- IM.toList rules
    pure (cons, nt, V.toList . consArgs =<< M.elems cons)

sccs :: TGRules f a -> [[NonTerminal]]
sccs tg = fmap vtnt . preorder <$> Gr.scc g
  where
    (g, v2c, _c2v) = toGraph tg
    vtnt v = case v2c v of
      (_, nt, _) -> nt
    preorder a = preorder' a []
    preorder' :: Gr.Tree a -> [a] -> [a]
    preorder' (Gr.Node a ts) = (a :) . preorderF' ts
    preorderF' :: [Gr.Tree a] -> [a] -> [a]
    preorderF' ts = foldr (.) id $ map preorder' ts

showCons :: (Show f, Show a) => Cons f a -> String
showCons (Cons tag tags args)
    = show tag <> "[" <> show tags <> "](" <> List.intercalate "," (map show $ V.toList args) <> ")"
 
toTreeGrammar :: (Ord a, Ord f) => TGRules f a -> (IM.IntMap NonTerminal, TreeGrammar f a)
toTreeGrammar tgRules = (mappings, TG { tgRules = tgRules', tgComponents = meta })
  where
    (mappings, tgRules') = minimizeGrammar tgRules
    meta = M.fromListWith (<>) [(computeMeta tgRules c, [toComponent cid c]) | (cid, cs) <- zip [0..] (sccs tgRules'), let c = V.fromList cs]

    outgoing :: NonTerminal -> [NonTerminal]
    outgoing nt = case IM.lookup nt tgRules' of
      Nothing -> []
      Just cons -> V.toList . consArgs =<< M.elems cons
    toComponent :: ComponentId -> V.Vector NonTerminal -> Component
    toComponent cid cs = Component {
        componentId = cid,
        componentRefs = IS.fromList (V.toList cs >>= outgoing) IS.\\ IS.fromList (V.toList cs),
        memberNodes = cs
     }
computeMeta :: forall f a. (Ord f, Ord a) => TGRules f a -> V.Vector NonTerminal -> ComponentMeta f a
computeMeta rules = CM . M.fromListWith (+) . map (,1) . concatMap getCons . V.toList
  where
    getCons :: NonTerminal -> [(a, f)]
    getCons nt = do
      cons <- M.elems $ rules IM.! nt
      pure (consTag cons, argTags cons)

showRule :: (Show a, Show f) => (NonTerminal, M.Map a (Cons f a)) -> String
showRule (nt, cons) = show nt <> " -> " <> List.intercalate " | " (map showCons (M.elems cons))

showTG :: (Show a, Show f) => TreeGrammar f a -> String
showTG (TG rules _) = unlines (map showRule (IM.toList rules))


makeTreeGrammar :: (Ord a, Ord f) => [(IS.Key, a, f, [NonTerminal])] -> (IM.IntMap NonTerminal, TreeGrammar f a)
makeTreeGrammar rules = toTreeGrammar nodes
  where
    toVec = M.fromList . fmap (consTag &&& id) . S.toAscList
    nodes = IM.map toVec $ IM.fromListWith (<>) $ do
        (nt, tag, tags, args) <- rules
        return (nt, S.singleton $ Cons tag tags $ V.fromList args)


type UnifyEnv f a = (TreeGrammar f a, IM.IntMap NonTerminal, Int)

mapComponent :: (NonTerminal -> NonTerminal) -> Component -> Component
mapComponent f c = c { memberNodes = V.map f (memberNodes c), componentRefs = IS.map f (componentRefs c) }

insertGrammar :: forall f a. (Ord a, Ord f) => TreeGrammar f a -> TreeGrammar f a -> UnifyEnv f a
insertGrammar t1@(TG rules1 comps1) (TG rules2 comps2) = flip execState (t1, IM.empty, IM.size rules1) $ do
    forM_ (M.toList comps2) $ \(k,vs) -> do
       forM_ vs $ \v -> do
        outs <- tryS $ do
          Just os <- pure $ M.lookup k comps1
          o <- asum (map pure os)
          unifyComponents v o
        case outs of
          Just () -> pure ()
          Nothing -> do
            forM_ (V.toList $ memberNodes v) $ \nt -> do
              nt' <- genUniq
              setMapping nt nt'
            copyComponent k v
            forM_ (V.toList $ memberNodes v) $ \nt -> do
               (_,mappings,_) <- get
               let cons = rules2 IM.! nt
                   cons' = M.map (mapNTs (mappings IM.!)) cons
               nt' <- getNT nt
               modify $ \(TG rules comps, mappings, next) -> (TG (IM.insert nt' cons' rules) comps, mappings, next)

  where
    copyComponent k v = do
        (_, mappings, _) <- get
        modify $ \(tg, m, i) -> (tg { tgComponents = M.insertWith (<>) k [mapComponent (mappings IM.!) v] (tgComponents tg) }, m, i)
    tryS :: StateT s [] x -> State s (Maybe x)
    tryS m = do
        s <- get
        case runStateT m s of
            [] -> pure Nothing
            (a, s'):_ -> put s' >> pure (Just a)
    lookupNT :: NonTerminal -> StateT (UnifyEnv f a) [] NonTerminal
    lookupNT nt 
      | IM.notMember nt rules2 = pure nt
      | otherwise = do
        (_,m,_) <- get
        maybe empty pure (IM.lookup nt m)
    getNT :: MonadState (UnifyEnv f a) m => NonTerminal -> m NonTerminal
    getNT nt
      | IM.notMember nt rules2 = pure nt
      | otherwise = do
        (_,m,_) <- get
        pure (m IM.! nt)
    unifyComponents :: Component -> Component -> StateT (UnifyEnv f a) [] ()
    unifyComponents scc1 scc2 = do
        let traverseIntSet f = fmap IS.fromList . traverse f . IS.toList
        lhs <- traverseIntSet lookupNT (componentRefs scc1)
        guard (lhs == componentRefs scc2)
        let n2 = memberNodes scc2 V.! 0
        n1 <- pick $ V.toList (memberNodes scc1)
        tryUnify n1 n2

    tryUnify :: NonTerminal -> NonTerminal -> StateT (UnifyEnv f a) [] ()
    tryUnify n1 n2 
      | IM.notMember n2 rules2 = guard (n1 == n2)
      | otherwise = do
        gets ((IM.!? n2) . (\(_,a,_) -> a)) >>= \case
          Just n1' -> guard (n1 == n1')
          Nothing -> do
            setMapping n2 n1
            let cons2 = rules2 IM.! n2
                cons1 = rules1 IM.! n1
            let inters = M.intersectionWith (,) cons1 cons2
            guard (M.size cons1 == M.size inters)
            guard $ and $ do
                (c1, c2) <- M.elems inters
                pure $ consTag c1 == consTag c2 && argTags c1 == argTags c2
            forM_ (M.elems inters) $ \(c1, c2) -> do
               forM_ (zip (V.toList (consArgs c1)) (V.toList (consArgs c2))) $ \(a1, a2) -> do
                 tryUnify a1 a2
    genUniq = do
      (_,_,next) <- get
      modify $ \(t, m, n) -> (t, m, n+1)
      pure next
    setMapping nt nt' = do
       modify $ \(t, m, n) -> (t, IM.insert nt nt' m, n)

    pick = asum . map pure
          -- (consTag cons1 == consTag cons2 && argTags cons1 == argTags cons2)

bestGroup :: ComponentMeta f a -> (a,f)
bestGroup cm = fst $ minimumBy (comparing snd) $ M.toList (consCounts cm)

exampleGrammar :: TreeGrammar () String
exampleGrammar = snd $ makeTreeGrammar
  [ (0, "cons", (), [1, 2])
  , (0, "nil", (), [])
  , (1, "cons", (), [0, 2])
  , (1, "nil", (), [])
  , (2, "c", (), [])
  ]


{-# INLINE count #-}
count :: Ord a => [a] -> M.Map a Int
count = List.foldl' (\m x -> M.insertWith (+) x 1 m) M.empty


{-# INLINE groupBy #-}
groupBy :: Ord b => (Int -> b) -> [Int] -> IM.IntMap Int
groupBy f ls = IM.fromList $ evalState (traverse resolveMapping ls) M.empty
   where 
     resolveMapping i = gets (M.lookup tag) >>= \case
       Just j -> pure (i,j)
       Nothing -> do
         gen <- gets M.size
         modify (M.insert tag gen)
         pure (i,gen)
       where tag = f i

{-# INLINE mapNTs #-}
mapNTs :: (NonTerminal -> NonTerminal) -> Cons f a -> Cons f a
mapNTs f (Cons tag dec args) = Cons tag dec (V.map f args)


-- | Rename non-terminals in a TreeGrammar
--
-- @
-- >>> g
-- 0 -> Leaf() | Node(0, 0)
-- 1 -> Leaf() | Node(1,0)
--
-- >>> applyTransform (const 0) g
-- 0 -> Leaf() | Node(0, 0)
-- @
applyTransform :: (NonTerminal -> NonTerminal) -> TreeGrammar f a -> TreeGrammar f a
applyTransform f (TG rules components) = TG (transformRules f rules) (transformComponents f components)

transformComponents :: (NonTerminal -> NonTerminal) -> TGComponents f a -> TGComponents f a
transformComponents f = M.map (fmap (mapComponent f))

transformRules :: (NonTerminal -> NonTerminal) -> TGRules f a -> TGRules f a
transformRules f = IM.map (M.map (mapNTs f)) . IM.mapKeys f


-- | Minimize a tree grammar.
--
-- Moore's algorithm but adapted to tree grammars:
--
-- Try to rename all non-terminals into a single state. Then
--
-- - Do a bucket-sort using the renamed outgoing transitions as key
-- - Distinct buckets mean states are distinguishable, try making each bucket a separate state
--
-- Repeat until a fixpoint is reached.
--
--
-- @
-- 0 -> Leaf()) | Node(0, 0)
-- 1 -> Leaf() | Node(1,0)
-- @
--
-- map `0 -> 0, 1 -> 0`
--
-- @
-- {Leaf()|Node(0,0) -> 0,1}
-- @
--
-- Only one bucket, fixpoint reached.
minimizeGrammar :: (Ord a, Ord f) => TGRules f a -> (IM.IntMap NonTerminal, TGRules f a)
minimizeGrammar tg = (trans, transformRules (trans IM.!)  tg)
  where trans = minimizeGrammar' tg
minimizeGrammar' :: forall a f. (Ord a, Ord f) => TGRules f a -> IM.IntMap NonTerminal
minimizeGrammar' m0 = go initial
  where
    initial = IM.fromList [(nt, 0) | nt <- IM.keys m0]
    translateNTs :: IM.IntMap Int -> NonTerminal -> S.Set (Cons f a)
    translateNTs m nt = S.fromList $ mapNTs (normTag m) <$> M.elems (m0 IM.! nt)
    go mappings
      | mappings == mappings' = mappings
      | otherwise = go mappings'
      where mappings' = groupBy (translateNTs mappings) (IM.keys m0)
    normTag m nt = IM.findWithDefault nt nt m

-- [Note: Non-Terminal union and intersection]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- We can union and intersect non-terminals by unioning and intersecting the languages they produce.
-- For union, we generate a new graph where nodes stands for a set of non-terminals. The outgoing transitions are the union of the outgoing transitions of the nodes in the set.
--
-- For top-down tree automata this loses some information:
--
-- @
-- a -> f(d,d)
-- b -> f(c,c)
--
-- a|b -> f(c|d,c|d)
-- @
--
-- Here, we have phantom-transitions even though @a|b -> f(c,d)@ are not in the original graph.

-- [Note: Graph Isomorphisms]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~
-- Often, we want to extend a minimal grammar. There are a couple approaches:
-- - Naive union+minimize
-- - Product construction similar to DFA union
-- - Find a partial graph isomorphism between the two grammars
--
-- Sub-graph isomorphisms are NP-hard, but because the grammars are minimal we get cheaper runtimes.
-- Each node in the pattern graph can match at most one node in the target graph.
-- This makes the problem quite tractable in practice.
--
-- Approach:
--
-- Assume wlg that we match a single strongly connected component.
-- For each pattern node, find a set of possible graph nodes.
-- Try each substitution in order.
--
-- - If we match @a@ with @x@, we go through the rule pairs, e.g. @a -> f(b,c,d)@ and  @x -> f(y,z,w)@. We add mappings @a -> x, b -> y, c -> z, d -> w@ to the substitution.
-- - Repeat until all pattern nodes are mapped to target nodes.
-- - If we run out of possible substitutions, we backtrack to the last node that has more than one possible mapping.
-- - If we run out of nodes to backtrack to, we must add new nodes
--
-- This nested search runs fairly quickly if we search nodes with low branching factors first.

-- -- | Union two nonterminals in a tree-grammar
-- unionNT :: (Ord a, Ord f) => NonTerminal -> NonTerminal -> TreeGrammar f a -> (NonTerminal, TreeGrammar f a)
-- unionNT l r s = do
