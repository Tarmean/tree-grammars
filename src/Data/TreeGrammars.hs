{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import qualified Data.Vector as BV
import qualified Data.Map.Strict as M
import Control.Monad.State
import qualified Data.List as List
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import Algebra.Lattice



type NonTerminal = Int
data Cons a = Cons { consTag :: !a, consArgs :: {-#UNPACK #-}!(V.Vector NonTerminal) }
  deriving (Eq, Ord, Show)



showCons :: Show a => Cons a -> String
showCons (Cons tag args) = show tag <> "(" <> List.intercalate "," (map show (V.toList args)) <> ")"


showRule :: Show a => (NonTerminal, BV.Vector (Cons a)) -> String
showRule (nt, cons) = show nt <> " -> " <> List.intercalate " | " (map showCons (BV.toList cons))

showTG :: Show a => TreeGrammar a -> String
showTG (TG rules) = unlines (map showRule (M.toList rules))


makeTreeGrammar :: Ord a => [(NonTerminal, a, [NonTerminal])] -> TreeGrammar a
makeTreeGrammar rules = TG (M.map toVec $ M.fromListWith (<>) (map (\(nt, tag, args) -> (nt, S.singleton (Cons tag (V.fromList args)))) rules))
  where
    toVec = BV.fromList . S.toAscList


exampleGrammar :: TreeGrammar Int
exampleGrammar = makeTreeGrammar
  [ (0, 0, [0, 0])
  , (0, 1, [])
  , (1, 0, [1, 0])
  , (1, 1, [])
  ]

newtype TreeGrammar a = TG { tgRules :: M.Map NonTerminal (BV.Vector (Cons a)) }
  deriving (Eq, Ord, Show)

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
mapNTs :: (Int -> Int) -> Cons a -> Cons a
mapNTs f (Cons tag args) = Cons tag (V.map f args)


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
applyTransform :: (NonTerminal -> NonTerminal) -> TreeGrammar a -> TreeGrammar a
applyTransform f (TG rules) = TG $ M.map (BV.map (mapNTs f)) (M.mapKeys f rules)



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
minimizeGrammar :: Ord a => TreeGrammar a -> (IM.IntMap NonTerminal, TreeGrammar a)
minimizeGrammar tg = (trans, applyTransform (trans IM.!)  tg)
  where trans = minimizeGrammar' tg
minimizeGrammar' :: forall a. Ord a => TreeGrammar a -> IM.IntMap NonTerminal
minimizeGrammar' (TG m0) = go initial
  where
    initial = IM.fromList [(nt, 0) | nt <- M.keys m0]
    translateNTs :: IM.IntMap Int -> NonTerminal -> S.Set (Cons a)
    translateNTs m nt = S.fromList $ mapNTs (normTag m) <$> BV.toList (m0 M.! nt)
    go mappings
      | mappings == mappings' = mappings
      | otherwise = go mappings'
      where mappings' = groupBy (translateNTs mappings) (M.keys m0)
    normTag m nt = IM.findWithDefault nt nt m



-- | Union two nonterminals in a tree-grammar
unionNT :: (MonadState (TreeGrammar a) m, Ord a) => (a -> a -> Maybe a) -> NonTerminal -> NonTerminal -> m NonTerminal
unionNT l r = do
