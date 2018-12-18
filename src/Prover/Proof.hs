{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Prover.Proof where

import Prover.Scheme
import Prover.System as Y
import qualified Prover.System as Y
import Prover.Reason hiding (name)
import Prover.Property
import Prover.Inparse

import qualified Data.Text as T
import Data.Maybe (fromJust, isJust)
import Data.Either.Combinators (rightToMaybe)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Lazy

type Proof = [(T.Text, T.Text)]
type Statement = T.Text

proveBy :: Eq a => Reason a -> Statement -> Scheme a ()
proveBy r statement = do
  (c1, p, mc2) <- lift $ rightToMaybe $ regularParse proofLine $ T.unpack statement
  i1 <- seizeClue c1
  info1 <- traverse seizeName (textref c1)
  let mi2 = seizeClue <$> mc2
  ref <- if isJust mi2 then Ref <$> (fromJust mi2) else return None
  info2 <- if isJust mc2 then traverse seizeName (textref $ fromJust mc2) else return None
  validate r (i1, Relation p ref $ Spec info1 info2)

seizeClue :: Eq a => Clue -> Scheme a Id
seizeClue c = seize (mgetprop c) (mgeom c) (name c)

testProof1 :: Eq a => Maybe (System a)
testProof1 = buildScheme $ do
  proveBy Given "–AB ≅ –BD"
  proveBy Given "∠ABC ≅ ∠DBC"
  proveBy reflexive "–BC is congruent to –BC"
  proveBy sideAngleSide "ΔABC ≅ ΔDBC"
