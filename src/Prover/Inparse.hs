{-# LANGUAGE OverloadedStrings #-}

module Prover.Inparse where

import Prover.Scheme
import Prover.System as Y hiding (name, geom, ptype)
import qualified Prover.System as Y
import Prover.Reason (Assertion)
import Prover.Property hiding (ptype)

import Text.Parsec (parse, ParseError)
import Text.Parsec.Prim (unexpected, try)
import Text.Parsec.String (Parser)
import Text.Parsec.Char (letter, char, digit, string, oneOf)
import Text.Parsec.Combinator (many1, manyTill, eof, choice, anyToken, optionMaybe, notFollowedBy)
import Control.Monad (void, guard)
import Control.Applicative ((<$>), (<*>), (<*), (<|>), many, (<$))
import qualified Data.Text as T

data Clue = Clue { mgetprop :: Maybe (PType, Geom)
                 , mgeom :: Maybe Geom
                 , name :: Name
                 , textref :: Ref T.Text } deriving (Show)

exClue s = regularParse clue s
exLine s = regularParse proofLine s

proofLine :: Parser (Clue, PType, Maybe Clue)
proofLine = (,,) <$> clue <*> ptype <*> (optionMaybe clue)

--TODO add "not" capabilities
ptype :: Parser PType
ptype = choice [
  try $ Length <$ parseLength,
  try $ Radius <$ parseRadius,
  try $ Degree <$ parseDegree,
  try $ Equals <$ parseEquals,
  try $ Congruent <$ parseCongruent,
  try $ Contains <$ parseContains,
  try $ Bounded <$ parseBounded,
  try $ IsRight <$ parseIsRight,
  Similar <$ parseSimilar ]

-- Clue Parsing --

clue :: Parser Clue
clue = choice [
  try segLengthClue,
  genericClue ]

segLengthClue :: Parser Clue
segLengthClue = do
  ns <- nameString
  if length ns /= 2
    then do unexpected "expecting a name length of 2"
    else do return $ Clue (Just (Length, Value)) (Just Segment) (T.pack ns) None

genericClue :: Parser Clue
genericClue = do
  p <- propPrefix
  g <- geom
  n <- T.pack <$> nameString
  return $ Clue p g n (makeInfo g n)

makeInfo :: (Maybe Geom) -> T.Text -> Ref T.Text
makeInfo _ n = Cyc $ T.singleton <$> (T.unpack n)

propPrefix :: Parser (Maybe (PType, Geom))
propPrefix = lexeme $ choice [
  Just (Degree, Value) <$ string "m",
  return Nothing ]

geom :: Parser (Maybe Geom)
geom = lexeme $ choice [
  Just Polygon <$ string "Δ",
  Just Line <$ string "↔️",
  Just Ray <$ string "→",
  Just Segment <$ string "–",
  Just Angle <$ string "∠",
  return Nothing ]

nameString :: Parser String
nameString = lexeme $ many1Till letter (void (oneOf " \t\n") <|> eof)

-- PType Parsers --

parseLength :: Parser String
parseLength = lexeme $ string "has length"
parseRadius :: Parser String
parseRadius = lexeme $ string "has radius"
parseDegree :: Parser String
parseDegree = lexeme $ string "has degree"
parseEquals :: Parser String
parseEquals = lexeme $ choice [
  string "=",
  string "is equal to" ]
parseCongruent :: Parser String
parseCongruent = lexeme $ choice [
  string "≅",
  string "is congruent to" ]
parseContains :: Parser String
parseContains = lexeme $ string "contains"
parseBounded :: Parser String
parseBounded = lexeme $ string "is bounded by"
parseIsRight :: Parser String
parseIsRight = lexeme $ string "is " >> choice [
  string "a right angle",
  string "right" ]
parseSimilar :: Parser String
parseSimilar = lexeme $ string "is similar to"

-- Helper Functions --

many1Till :: Show b => Parser a -> Parser b -> Parser [a]
many1Till p end = do
    notFollowedBy end
    p1 <- p
    ps <- manyTill p end
    return (p1:ps)

whitespace :: Parser ()
whitespace = void $ many $ oneOf " \n\t"

lexeme :: Parser a -> Parser a
lexeme p = p <* whitespace

regularParse :: Parser a -> String -> Either ParseError a
regularParse p = parse p ""

parseWithEof :: Parser a -> String -> Either ParseError a
parseWithEof p = parse (p <* eof) ""

parseWithLeftOver :: Parser a -> String -> Either ParseError (a,String)
parseWithLeftOver p = parse ((,) <$> p <*> leftOver) ""
  where leftOver = manyTill anyToken eof
