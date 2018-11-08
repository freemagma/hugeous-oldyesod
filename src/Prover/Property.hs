{-# LANGUAGE TemplateHaskell #-}

module Prover.Property where

import Data.Hashable

type Id = Int

data Geom = Point
          | Line
          | Segment
          | Circle
          | Angle
          | Value
          | Polygon
          deriving (Show, Eq, Enum)

instance Semigroup Geom where
  (<>) a b = a
instance Monoid Geom where
  mempty = Point
instance Hashable Geom where
  hashWithSalt salt g = hashWithSalt salt (fromEnum g)

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

data Spec r = Spec (Info r) (Info r)
  deriving (Eq)
data Info r = None | Cyc [r] | Ord [r]
  deriving (Eq)

instance Functor Spec where
  fmap f (Spec a b) = Spec (f <$> a) (f <$> b)
instance Functor Info where
  fmap f None = None
  fmap f (Cyc as) = Cyc $ f <$> as
  fmap f (Ord as) = Ord $ f <$> as

swap :: Spec r -> Spec r
swap (Spec a b) = Spec b a

(=~=) :: Eq r => (Spec r) -> (Spec r) -> Bool
Spec None None =~= Spec None None = True
u@(Spec (Ord as) (Ord bs)) =~= v@(Spec (Ord cs) (Ord ds)) = u == v
Spec (Cyc as) (Cyc bs) =~= Spec (Cyc cs) (Cyc ds) =
  elem (cs, ds) $ zip (cycPermute as) (cycPermute bs)
_ =~= _ = False

cycPermute :: [a] -> [[a]]
cycPermute as = (uniPermutes as) ++ (uniPermutes $ reverse as)
  where takeDrop as t d = take t $ drop d as
        uniPermutes as = takeDrop (cycle as) (length as) <$> [0..(length as - 1)]

data PropertyG r a = Concretely a
                   | Relation { ptype :: PType, ref :: r, spec :: Spec r}
                   deriving Eq

instance (Show a, Show r) => Show (PropertyG r a) where
  show (Concretely a) = "Concretely " ++ (show a)
  show (Relation pt r _) = (show pt) ++ " " ++ (show r)

type Property a = PropertyG Id a

mkRel :: PType -> r -> PropertyG r a
mkRel pt r = Relation pt r (Spec None None)

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
additionalProps (i, Relation pt r s) = para ++ anti
  where para = (\pt -> (i, Relation pt r s)) <$> (parallelPTypes pt)
        anti = (\pt -> (r, Relation pt i (swap s))) <$> (antiparallelPTypes pt)
additionalProps _ = []
