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

data PropertyG r a = Concretely a
                   | Length r
                   | Radius r
                   | Degree r
                   | Intersect r r
                   | Equals r
                   | Congruent r
                   | Endpoint r
                   | Contains r
                   | Bounded [r]
                   | Implies (PropertyG r a)
                   | Not (PropertyG r a)
                   deriving (Show, Eq)

type Property a = PropertyG Id a

data PType = ConcretelyP
           | LengthP
           | RadiusP
           | DegreeP
           | IntersectP
           | EqualsP
           | CongruentP
           | ContainsP
           | EndpointP
           | BoundedP
           | ImpliesP PType
           | NotP PType
           deriving (Show, Eq)

references :: PropertyG r a -> [r]
references (Length a)      = [a]
references (Length a)      = [a]
references (Radius a)      = [a]
references (Degree a)      = [a]
references (Intersect a b) = [a, b]
references (Equals a)      = [a]
references (Congruent a)   = [a]
references (Contains a)    = [a]
references (Endpoint a)    = [a]
references (Bounded xs)    = xs
references (Implies p')    = references p'
references (Not p')        = references p'

ptypeOf :: PropertyG r a -> PType
ptypeOf p = case p of
  (Concretely _)  -> ConcretelyP
  (Length _)      -> LengthP
  (Radius _)      -> RadiusP
  (Degree _)      -> DegreeP
  (Intersect _ _) -> IntersectP
  (Equals _)      -> EqualsP
  (Congruent _)   -> CongruentP
  (Contains _)    -> ContainsP
  (Endpoint _)    -> EndpointP
  (Bounded _)     -> BoundedP
  (Not p')        -> NotP (ptypeOf p')
  (Implies p')    -> ImpliesP (ptypeOf p')

replaceRefsEnum :: (Enum e) => PropertyG r a -> e -> PropertyG e a
replaceRefsEnum p e = case p of
  (Concretely a)  -> Concretely a
  (Length _)      -> Length e
  (Radius _)      -> Radius e
  (Degree _)      -> Degree e
  (Intersect _ _) -> Intersect e (succ e)
  (Equals _)      -> Equals e
  (Congruent _)   -> Congruent e
  (Contains _)    -> Contains e
  (Endpoint _)    -> Endpoint e
  (Bounded xs)    -> Bounded $ enumFromTo e (toEnum $ ((length xs) - 1) + fromEnum e)
  (Implies p')    -> Implies $ replaceRefsEnum p' e
  (Not p')        -> Not $ replaceRefsEnum p' e

requireds :: (r, PropertyG r a) -> [(r, PropertyG r a)]
requireds (_, Concretely _)  = []
requireds (_, Length _)      = []
requireds (_, Radius _)      = []
requireds (_, Degree _)      = []
requireds (i, Intersect a b) = [(a, Intersect i b)]
requireds (i, Equals a)      = [(a, Equals i)]
requireds (i, Congruent a)   = [(a, Congruent i)]
requireds (_, Contains _)    = []
requireds (i, Endpoint a)    = [(i, Contains a)]
requireds (i, Bounded xs)   = [(i, Contains x) | x <- xs]
