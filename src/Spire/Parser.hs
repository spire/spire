module Spire.Parser where
import Spire.Surface
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language
import Data.Functor.Identity(Identity)

----------------------------------------------------------------------

ops = ["->", ",", ":", "$"]
keywords = [
  "Unit", "Bool", "Type",
  "Pi", "Sg",
  "tt", "true", "false",
  "caseBool", "if", "then", "else",
  "proj1", "proj2"
  ]

def = emptyDef {
  commentStart = "{-"
, commentEnd = "-}"
, commentLine = "--"
, opStart = oneOf (map head ops)
, opLetter = oneOf (concat ops)
, reservedOpNames = ops
, reservedNames = keywords
}

type MParser a = ParsecT [Char] () Identity a

tokenizer = makeTokenParser def
parseOp = reservedOp tokenizer
parseKeyword = reserved tokenizer
parseSpaces = whiteSpace tokenizer

parseParens:: MParser a -> MParser a
parseParens = parens tokenizer

parseTerm :: String -> Either ParseError Check
parseTerm = parse (parseSpaces >> parseCheck) "(unknown)"

----------------------------------------------------------------------

parseCheck:: MParser Check
parseCheck = do
      try (parseParens parseCheck)
  <|> try parsePair
  <|> try parseLam
  <|> (return . Infer =<< try parseInfer)

parseInfer:: MParser Infer
parseInfer = do
      try parseAnn
  <|> try parseApp
  <|> try (parseParens parseInfer)
  <|> parseTT
  <|> parseTrue
  <|> parseFalse
  <|> parseUnit
  <|> parseBool
  <|> parseType
  <|> try parsePi
  <|> try parseSg
  <|> try parseVar
  <|> try parseIf
  <|> try parseCaseBool
  <|> try parseProj1
  <|> try parseProj2

----------------------------------------------------------------------

parsePair = parseParens $ do
  x <- parseCheck
  parseOp ","
  y <- parseCheck
  return $ CPair x y

parseLam = do
  parseOp "->"
  tm <- parseCheck
  return $ CLam tm

----------------------------------------------------------------------

parseTT = parseKeyword "tt" >> return ITT
parseTrue = parseKeyword "true" >> return ITrue
parseFalse = parseKeyword "false" >> return IFalse
parseUnit = parseKeyword "Unit" >> return IUnit
parseBool = parseKeyword "Bool" >> return IBool
parseType = parseKeyword "Type" >> return IType

parsePi = do
  parseKeyword "Pi"
  a <- parseCheck
  b <- parseCheck
  return $ IPi a b

parseSg = do
  parseKeyword "Sg"
  a <- parseCheck
  b <- parseCheck
  return $ ISg a b

parseVar = do
  i <- natural tokenizer
  return $ IVar i

parseIf = do
  parseKeyword "if"
  b <- parseCheck
  parseKeyword "then"
  c1 <- parseInfer
  parseKeyword "else"
  c2 <- parseInfer
  return $ IIf b c1 c2

parseCaseBool = do
  parseKeyword "caseBool"
  p <- parseCheck
  pt <- parseCheck
  pf <- parseCheck
  b <- parseCheck
  return $ ICaseBool p pt pf b

parseProj1 = do
  parseKeyword "proj1"
  ab <- parseInfer
  return $ IProj1 ab

parseProj2 = do
  parseKeyword "proj2"
  ab <- parseInfer
  return $ IProj2 ab

parseApp = parseParens $ do
  f <- parseInfer
  parseOp "$"
  a <- parseCheck
  return $ IApp f a

parseAnn = parseParens $ do
  tm <- parseCheck
  parseOp ":"
  tp <- parseCheck
  return $ IAnn tm tp

----------------------------------------------------------------------