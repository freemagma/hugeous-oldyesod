{-# LANGUAGE TemplateHaskell #-}

module Prover.Property where

import Data.Hashable
import Data.Foldable (toList)

type Id = Int

data Geom = Point
          | Line
          | Segment
          | Ray
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
           | Bounded
           | IsRight
           | Implies PType
           | Not PType
           deriving (Show, Eq)

isImplication :: PType -> Bool
isImplication (Implies pt') = True
isImplication _ = False

data Spec r = Spec (Ref r) (Ref r)
  deriving (Eq, Show)
data Ref r = None | Ref r | Cyc [r] | Ord [r]
  deriving (Eq)

instance Show a => Show (Ref a) where
  show None = ""
  show (Ref a) = show a
  show (Cyc a) = "<" ++ show a ++ ">"
  show (Ord a) = show a
instance Functor Spec where
  fmap f (Spec a b) = Spec (f <$> a) (f <$> b)
instance Functor Ref where
  fmap f None = None
  fmap f (Ref r) = Ref $ f r
  fmap f (Cyc as) = Cyc $ f <$> as
  fmap f (Ord as) = Ord $ f <$> as
instance Foldable Ref where
  foldMap f None = mempty
  foldMap f (Ref r) = f r
  foldMap f (Cyc as) = foldMap f as
  foldMap f (Ord as) = foldMap f as
  foldr f b None = b
  foldr f b (Ref a) = f a b
  foldr f b (Cyc as) = foldr f b as
  foldr f b (Ord as) = foldr f b as

swap :: Spec r -> Spec r
swap (Spec a b) = Spec b a

(=~=) :: Eq r => (Ref r) -> (Ref r) -> Bool
(Cyc as) =~= (Cyc bs) = elem as $ cycPermute bs
ra =~= rb = ra == rb

(=~~=) :: Eq r => (Spec r) -> (Spec r) -> Bool
Spec (Cyc as) (Cyc bs) =~~= Spec (Cyc cs) (Cyc ds) =
  elem (cs, ds) $ zip (cycPermute as) (cycPermute bs)
Spec a b =~~= Spec c d = (a =~= c) && (b =~= d)

cycPermute :: [a] -> [[a]]
cycPermute as = (uniPermutes as) ++ (uniPermutes $ reverse as)
  where takeDrop as t d = take t $ drop d as
        uniPermutes as = takeDrop (cycle as) (length as) <$> [0..(length as - 1)]

cycStandard :: Ord a => [a] -> [a]
cycStandard [a] = [a]
cycStandard xs  = if last mf < (mf !! 1) then (head mf) : (reverse $ tail mf) else mf
  where mf = take (length xs) $ dropWhile (/= (minimum xs)) $ cycle xs

data PropertyG r a = Concretely a
                   | Relation { ptype :: PType, ref :: (Ref r), spec :: (Spec r)}
                   deriving Eq

instance (Show a, Show r) => Show (PropertyG r a) where
  show (Concretely a) = "Concretely " ++ (show a)
  show (Relation pt r _) = (show pt) ++ " " ++ (show r)

type Property a = PropertyG Id a

mkRel :: PType -> r -> PropertyG r a
mkRel pt r = Relation pt (Ref r) (Spec None None)

mkRelR :: PType -> Ref r -> PropertyG r a
mkRelR pt r = Relation pt r (Spec None None)

mkRelN :: PType -> PropertyG r a
mkRelN pt = Relation pt None (Spec None None)

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
parallelPTypes (Not pt) = Not <$> parallelPTypes pt
parallelPTypes (Implies pt) = Implies <$> parallelPTypes pt
parallelPTypes _ = []

additionalProps :: (r, PropertyG r a) -> [(r, PropertyG r a)]
additionalProps (i, Relation pt rr s) = para ++ anti
  where para = (\r pt -> (i, Relation pt (Ref r) s)) <$> (toList rr) <*> (parallelPTypes pt)
        anti = (\r pt -> (r, Relation pt (Ref i) (swap s))) <$> (toList rr) <*> (antiparallelPTypes pt)
additionalProps _ = []
