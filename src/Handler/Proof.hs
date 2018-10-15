{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

module Handler.Proof where

import Import
import Prover.Reason
import Prover.Proof
import Text.Read
import Yesod.Form.Jquery
import qualified Data.Text as T (unpack)

getProofR :: Handler Html
getProofR = do
  rowsMaybe <- (fmap.fmap) T.unpack $ lookupGetParam "rows"
  let rows = (fromMaybe 5 $ join $ readMaybe <$> rowsMaybe)
  ((res, widget), enctype) <- runFormGet (proofForm rows)
  defaultLayout $ do
    $(widgetFile "proof")

proofForm :: Int -> Html -> MForm Handler (FormResult Proof, Widget)
proofForm rows extra = do
  sfields <- replicateM rows $ mreq (jqueryAutocompleteField ACStatementR) "" Nothing
  rfields <- replicateM rows $ mreq (jqueryAutocompleteField ACReasonsR) "" Nothing
  let (sresults,sviews) = unzip sfields
  let (rresults,rviews) = unzip rfields
  let results = zip sresults rresults
  let views   = zip sviews rviews
  let widget = $(widgetFile "proofForm")
  let resProof = sequenceA $ (\(a, b) -> (,) <$> a <*> b) <$> results
  return (resProof, widget)

getACStatementR :: Handler Value
getACStatementR = do
  term <- unpack <$> (runInputGet $ ireq textField "term")
  returnJson $ toJSONList [term ++ "≅" ++ term]

getACReasonsR :: Handler Value
getACReasonsR = do
  term <- unpack <$> (runInputGet $ ireq textField "term")
  returnJson $ toJSONList reasonList
