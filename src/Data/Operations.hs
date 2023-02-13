{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
module Operations where


import Control.Monad.State
import qualified Data.Map as M

import Data.TreeGrammars
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Merge.Strict as M
import qualified Data.Vector.Unboxed as V

type OldL = NonTerminal
type OldR = NonTerminal
type New = NonTerminal
data MergeEnv f a = MEnv { mergeMappings :: M.Map (OldL,OldR) New, mergeRules :: M.Map New (M.Map a (Cons f a)) }

type M f a = State (MergeEnv f a)
tgUnion :: (Ord a) => (f -> f -> Maybe f) -> TreeGrammar f a -> OldL -> OldR -> M f a New
tgUnion mergeAttr tg = go
  where
    go x y
      | x == y = pure x
      | x > y = go y x
    go x y = do
      loookupMapping x y >>= \case
        Just z -> pure z
        Nothing -> do
          let l = tgRules tg IM.! x
              r = tgRules tg IM.! y
          merged <- M.mergeA M.preserveMissing M.preserveMissing (M.zipWithMaybeAMatched (const zipChildren)) l r
          z <- newNode merged
          addMapping x y z
          pure z
    zipChildren (Cons {consTag=c1, argTags=a1, consArgs=args1}) (Cons {consTag=c2, argTags=a2, consArgs=args2})
      | c1 /= c2 = pure Nothing
      | otherwise = case mergeAttr a1 a2  of
           Nothing -> pure Nothing
           Just a -> do
             args <- traverse (uncurry go) (zip (V.toList args1) (V.toList args2))
             pure $ Just $ Cons c1 a (V.fromList args)


newNode :: M.Map a (Cons f a) -> M f a New
newNode children = do
  MEnv{..} <- get
  let new = M.size mergeRules
      rules = M.insert new children mergeRules
  put $ MEnv mergeMappings rules
  pure new

addMapping :: OldL -> OldR -> New -> M f a ()
addMapping l r z = do
  MEnv{..} <- get
  let mappings = M.insert (l,r) z mergeMappings
  put $ MEnv mappings mergeRules

loookupMapping :: OldL -> OldR -> M f a (Maybe New)
loookupMapping l r = do
  MEnv{..} <- get
  pure $ M.lookup (l,r) mergeMappings

