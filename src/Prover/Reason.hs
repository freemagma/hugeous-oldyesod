module Prover.Reason where

import Prover.Property
import Prover.System as SY

type Reason a = System a  

reasonList :: [String]
reasonList = [
  "Corresponding Parts of Congruent Triangles are Congruent (CPCTC)",
  "All Right Angles Are Congruent",
  "Vertical Angles Theorem",
  "Given"
  ]
