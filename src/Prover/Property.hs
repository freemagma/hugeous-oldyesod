{-# LANGUAGE TemplateHaskell #-}

module Prover.Property where

type Id = Int

data Geom = Point
          | Line
          | Segment
          | Circle
          | Angle
          | Value
          | Polygon
          deriving (Show, Eq)

data PType = Length
           | Radius
           | Degree
           | Equals
           | Congruent
           | Contains
           | Endpoint
           | Bounded
           | IsRight
           | Implies PType
           | Not PType
           deriving (Show, Eq)

isImplication :: PType -> Bool
isImplication (Implies pt') = True
isImplication _ = False

data PropertyG r a = Concretely a
                   | Relation { ptype :: PType, ref :: r, specs :: ([r], [r])}
                   deriving Eq

instance (Show a, Show r) => Show (PropertyG r a) where
  show (Concretely a) = "Concretely " ++ (show a)
  show (Relation pt r _) = (show pt) ++ " " ++ (show r)

type Property a = PropertyG Id a

mkRel :: PType -> r -> PropertyG r a
mkRel pt r = Relation pt r ([],[])

inconcrete :: PropertyG r a -> Bool
inconcrete (Concretely a) = False
inconcrete _ = True

antiparallelPTypes :: PType -> [PType]
antiparallelPTypes Congruent = [Congruent]
antiparallelPTypes Equals = [Equals]
antiparallelPTypes (Not pt) = Not <$> antiparallelPTypes pt
antiparallelPTypes (Implies pt) = Implies <$> antiparallelPTypes pt
antiparallelPTypes _ = []

parallelPTypes :: PType -> [PType]
parallelPTypes Bounded = [Contains]
parallelPTypes Endpoint = [Contains]
parallelPTypes (Not pt) = Not <$> parallelPTypes pt
parallelPTypes (Implies pt) = Implies <$> parallelPTypes pt
parallelPTypes _ = []

additionalProps :: (r, PropertyG r a) -> [(r, PropertyG r a)]
additionalProps (i, Relation pt r (as, bs)) = para ++ anti
  where para = (\pt -> (i, Relation pt r (as, bs))) <$> (parallelPTypes pt)
        anti = (\pt -> (r, Relation pt i (bs, as))) <$> (antiparallelPTypes pt)
additionalProps _ = []
