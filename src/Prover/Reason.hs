{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

module Prover.Reason where

import Prover.Property
import Prover.System as Y
import Data.Foldable (toList)
import Data.Sequence ( Seq, (><), (!?))
import qualified Data.Sequence as S
import Data.HashMap.Strict ( (!) )
import qualified Data.HashMap.Strict as HM
import Control.Lens
import Control.Applicative
import qualified Data.Text as T
import Control.Monad.Trans.State.Lazy

type Assertion a = (Id, Property a)

data Reason a = Reason { _name :: T.Text
                       , _systems :: [System a]} deriving Show
makeLenses ''Reason

type Scheme a r = StateT (System a) Maybe r

assertEq :: Eq a => Assertion a -> Assertion a -> Bool
assertEq (a, Concretely x) (b, Concretely y) = (b == a) && (x == y)
assertEq (a, Relation pa ra sa) (b, Relation pb rb sb) =
  (a == b) && (pa == pb) && (ra =~= rb) && (sa =~~= sb)

implications :: System a -> Seq (Assertion a)
implications s = foldr (><) S.empty $ objimps <$> (s ^. objs)
  where objimps o = ((,) (o ^. ident)) <$> (S.filter (isImplication.ptype) $ o ^. props)

mapAssertion :: Mapping -> Assertion a -> Assertion a
mapAssertion m (i, Relation pt j s) = (m ! i, Relation pt ((m!) <$> j) ((m!) <$> s))
mapAssertion m (i, c) = (m ! i, c)

mapImply :: Mapping -> Assertion a -> Assertion a
mapImply m (i, Relation (Implies pt) j s) = mapAssertion m (i, Relation pt j s)
mapImply m p = mapAssertion m p

validateOne :: Eq a => System a -> Assertion a -> Scheme a ()
validateOne r a = StateT $ \s ->
  if any goodmap (systemMatch r s) then Just ((), (uncurry addProperty) a s) else Nothing
  where goodmap m = any (assertEq a) $ toList $ (mapImply m) <$> implications r

validate :: Eq a => Reason a -> Assertion a -> Scheme a ()
validate r a = StateT $ go (r ^. systems) a
  where go (rr:rrs) a s = (runStateT (validateOne rr a) s) <|> (go rrs a s)
        go _ a s = Nothing

-- Reasons --
rightAngles :: Reason a
rightAngles = Reason "Right angles are congruent" $ [
  ((insertWithProps Angle [mkRelN IsRight, mkRel (Implies Congruent) 0]).
  (insertWithProps Angle [mkRelN IsRight]))
  Y.empty]

--reflexive :: Reason a
--reflexive = Reason "Reflexive property of congruence" $

sideAngleSide :: Reason a
sideAngleSide = Reason "SAS Postulate" $ [
  ((addProperty 0 $ Relation (Implies Congruent) (Ref 7) (Spec (Cyc [1, 2, 3]) (Cyc [8, 9, 10]))).
  (insertWithProps Angle [mkRelR Bounded (Cyc [11, 12]), mkRel Congruent 14]).
  (insertWithProps Angle [mkRelR Bounded (Cyc [4, 5])]).
  (addProperty 4 $ mkRel Congruent 11).(addProperty 5 $ mkRel Congruent 12).
  (insertPolygon 3).(insertPolygon 3))
  Y.empty]

-- Testing --

ras :: System a
ras = ((insertWithProps Angle [mkRelN IsRight, mkRelR Bounded (Cyc [4, 5])]).
      (insertWithProps Angle [mkRelN IsRight, mkRelR Bounded (Cyc [4, 5])]).
      (insertWithProps Segment [mkRelR Bounded (Cyc [2, 3])]).
      (insertWithProps Segment [mkRelR Bounded (Cyc [0, 1]), mkRel Contains 2]).
      (insert Point).(insert Point).(insert Point).(insert Point))
      Y.empty

sass :: System a
sass = ((addProperty 4 $ mkRel Congruent 4).
       (insertWithProps Angle [mkRelR Bounded (Cyc [4, 5]), mkRel Congruent 11]).
       (insertWithProps Angle [mkRelR Bounded (Cyc [4, 9])]).
       (insertWithProps Polygon [mkRelR Bounded (Cyc [2, 7, 3])]).
       (insertWithProps Segment [mkRelR Bounded (Cyc [2, 7]), mkRel Congruent 5]).
       (insertWithProps Segment [mkRelR Bounded (Cyc [3, 7])]).
       (insert Point).(insertPolygon 3))
       Y.empty

reasonList :: [String]
reasonList = [
  "Corresponding Parts of Congruent Triangles are Congruent (CPCTC)",
  "All Right Angles Are Congruent",
  "Vertical Angles Theorem",
  "Given"
  ]
