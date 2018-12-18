{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

module Prover.Reason where

import Prover.Property
import Prover.System as Y
import Prover.Scheme

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

data Reason a = Given |
                Reason { _name :: T.Text
                       , _systems :: [System a]} deriving Show
makeLenses ''Reason

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
validate Given a = StateT $ \s -> Just ((), (uncurry addProperty) a s)
validate r a = StateT $ go (r ^. systems) a
  where go (rr:rrs) a s = (runStateT (validateOne rr a) s) <|> (go rrs a s)
        go _ a s = Nothing

-- Reasons --

rightAngles :: Reason a
rightAngles = Reason "Right angles are congruent" [buildSchemeUnsafe $ do
    modify $ insertWithProps Angle [mkRelN IsRight]
    modify $ insertWithProps Angle [mkRelN IsRight]
    modify $ addProperty 0 $ mkRel (Implies Congruent) 1
  ]

sideAngleSide :: Eq a => Reason a
sideAngleSide = Reason "SAS Postulate" $ [buildSchemeUnsafe $ do
    [tABC, tDEF] <- seizesG Polygon ["ABC", "DEF"]
    [sAB, sDE, sBC, sEF] <- seizesG Segment ["AB", "DE", "BC", "EF"]
    [aABC, aDEF] <- seizesG Angle ["ABC", "DEF"]
    [a, b, c, d, e, f] <- seizesG Point $ T.singleton <$> "ABCDEF"
    modify $ addProperty sAB $ mkRel Congruent sDE
    modify $ addProperty sBC $ mkRel Congruent sEF
    modify $ addProperty aABC $ mkRel Congruent aDEF
    modify $ addProperty tABC $
      Relation (Implies Congruent) (Ref tDEF) $ Spec (Cyc [a, b, c]) (Cyc [d, e, f])
  ]

reflexive :: Eq a => Reason a
reflexive = Reason "Reflexive Property" $ go <$> enumFrom (toEnum 0 :: Geom)
  where go g = buildSchemeUnsafe $ do {
    modify $ insert g;
    modify $ addProperty 0 $ mkRel (Implies Congruent) 0;
  }

-- Testing --

testGetProp :: Eq a => Maybe (System a)
testGetProp = buildScheme $ do
  seizeValG Length Segment "AB"

testProof :: Eq a => Maybe (System a)
testProof = buildScheme $ do
  [tABC, tBCD] <- seizesG Polygon ["ABC", "BCD"]
  [sAB, sBC, sBD] <- seizesG Segment ["AB", "BC", "BD"]
  [aABC, aDBC] <- seizesG Angle ["ABC", "DBC"]
  modify $ addProperty sAB $ mkRel Congruent sBD
  modify $ addProperty aABC $ mkRel Congruent aDBC
  ptsABC <- seizesG Point $ T.singleton <$> "ABC"
  ptsDBC <- seizesG Point $ T.singleton <$> "DBC"
  validate reflexive
    (sBC, mkRel Congruent sBC)
  validate sideAngleSide
    (tABC, Relation Congruent (Ref tBCD) $ Spec (Cyc ptsABC) (Cyc ptsDBC))

reasonList :: [String]
reasonList = [
  "Corresponding Parts of Congruent Triangles are Congruent (CPCTC)",
  "All Right Angles Are Congruent",
  "Vertical Angles Theorem",
  "Given"
  ]
