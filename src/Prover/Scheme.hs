{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Prover.Scheme where

import Prover.System as Y
import Prover.Property
import Control.Lens
import Data.HashMap.Strict as HM
import qualified Data.Text as T
import Data.Maybe (catMaybes)
import Prover.Reason
import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Class (lift)

type Clue = (Geom, Name)
-- type Scheme a r = StateT (System a) Maybe r

(&!!) = flip retrieveUnsafe
retrieveUnsafe :: Clue -> System a -> Id
retrieveUnsafe c s = head (retrieveAll c s)

retrieve :: Clue -> Scheme a Id
retrieve c = do
  s <- get
  let l = retrieveAll c s
  if Prelude.null l then lift Nothing
  else return $ head l

retrieveAll :: Clue -> System a -> [Id]
retrieveAll (g, n) s = catMaybes (simple : others)
  where simple = HM.lookup n (s ^. nameId)
        others = (flip HM.lookup $ (s ^. referencedBy)) <$> (g,) <$> (nameToRefs n s)

nameToRefs :: Name -> System a -> [Ref Id]
nameToRefs n s = catMaybes [(Cyc . cycStandard) <$> idList, Ord <$> idList, Ref <$> (HM.lookup n nMap)]
  where nMap   = s ^. nameId
        idList = traverse (flip HM.lookup $ nMap) $ T.singleton <$> (T.unpack n)

recentId :: Scheme a Id
recentId = get >>= \s -> return (s ^. nextId - 1)

seize :: Clue -> Scheme a Id
seize c = do
  s <- get
  let l = retrieveAll c s
  if not $ Prelude.null l then retrieve c
  else do case c of {
    (Point, n)   -> modify (insertWithName Point n) >> recentId;
    (Polygon, n) -> if T.length n < 3
      then modify (insertWithName Polygon n) >> recentId
      else mapM seize (fmap ((Point,) . T.singleton) $ T.unpack n) >>=
           \pts -> modify (insertWithProps Polygon $ [mkRelR Bounded $ Cyc pts]) >> recentId;
  }

-- Testing --

nsass = (nameObjs [1, 2, 3, 7] ["A", "B", "C", "D"]) sass
