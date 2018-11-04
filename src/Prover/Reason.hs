module Prover.Reason where

import Prover.Property
import Prover.System as Y
import Data.Foldable (toList)
import Data.Sequence ( Seq, (><), (!?))
import qualified Data.Sequence as S
import Data.HashMap.Strict ( (!) )
import qualified Data.HashMap.Strict as HM
import Control.Lens

type Reason a = System a
type Assertion a = (Id, Property a)

implications :: Reason a -> Seq (Assertion a)
implications s = foldr (><) S.empty $ objimps <$> (s ^. objs)
  where objimps o = ((,) (o ^. ident)) <$> (S.filter (isImplication.ptype) $ o ^. props)

mapAssertion :: Mapping -> Assertion a -> Assertion a
mapAssertion m (i, Relation pt j (as, bs)) = (m ! i, Relation pt (m ! j) ((m!) <$> as, (m!) <$> bs))
mapAssertion m (i, c) = (m ! i, c)

mapImply :: Mapping -> Assertion a -> Assertion a
mapImply m (i, Relation (Implies pt) j s) = mapAssertion m (i, Relation pt j s)
mapImply m p = mapAssertion m p

validate :: Eq a => System a -> Assertion a -> Reason a -> Maybe (System a)
validate s a r = result
  where mappings  = systemMatch r s
        goodmap m = elem a $ toList $ (mapImply m) <$> implications r
        result = if any goodmap mappings then Just $ (uncurry addProperty) a s else Nothing

-- Testing --
rightAngles :: Reason a
rightAngles = insertWithProps Angle [mkRel IsRight 1, mkRel (Implies Congruent) 0] s
  where s = insertWithProps Angle [mkRel IsRight 0] Y.empty

ras :: System a
ras = ((insertWithProps Angle [mkRel IsRight 7, mkRel Bounded 4, mkRel Bounded 5]).
      (insertWithProps Angle [mkRel IsRight 6, mkRel Bounded 5, mkRel Bounded 4]).
      (insertWithProps Segment [mkRel Endpoint 2, mkRel Endpoint 3]).
      (insertWithProps Segment [mkRel Endpoint 0, mkRel Endpoint 1, mkRel Contains 2]).
      (insert Point).(insert Point).(insert Point).(insert Point))
      Y.empty

-- ([4, 5, 6], [11, 12, 13])
sideAngleSide :: Reason a
sideAngleSide = ((addProperty 0 $ mkRel (Implies Congruent) 7).
                (insertWithProps Angle [mkRel Bounded 8, mkRel Bounded 9, mkRel Congruent 14]).
                (insertWithProps Angle [mkRel Bounded 1, mkRel Bounded 2]).
                (addProperty 1 $ mkRel Congruent 8).(addProperty 2 $ mkRel Congruent 9).
                (insertPolygon 3).(insertPolygon 3))
                Y.empty

sass :: System a
sass = ((addProperty 1 $ mkRel Congruent 1).
       (insertWithProps Angle [mkRel Bounded 1, mkRel Bounded 9, mkRel Congruent 11]).
       (insertWithProps Angle [mkRel Bounded 3, mkRel Bounded 1]).
       (insertWithProps Polygon [mkRel Bounded 8, mkRel Bounded 9, mkRel Bounded 1]).
       (insertWithProps Line [mkRel Endpoint 6, mkRel Endpoint 7, mkRel Congruent 3]).
       (insertWithProps Line [mkRel Endpoint 5, mkRel Endpoint 7]).
       (insert Point).(insertPolygon 3))
       Y.empty

reasonList :: [String]
reasonList = [
  "Corresponding Parts of Congruent Triangles are Congruent (CPCTC)",
  "All Right Angles Are Congruent",
  "Vertical Angles Theorem",
  "Given"
  ]
