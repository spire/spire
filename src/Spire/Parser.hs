module Spire.Parser where
import Spire.Surface
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language

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

tokenizer = makeTokenParser def
parseOp = reservedOp tokenizer
parseKeyword = reserved tokenizer
parseSpaces = whiteSpace tokenizer

parseParens p = do
  char '('
  spaces
  tm <- p
  spaces
  char ')'
  return tm

parseTerm :: String -> Either ParseError Check
parseTerm tm = parse parseExpr "(unknown)" tm

----------------------------------------------------------------------

parseExpr = do
  parseSpaces
  parseCheck

parseCheck = do
      try (parseParens parseCheck)
  <|> try parsePair
  <|> try parseLam
  <|> (return . Infer =<< try parseInfer)

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

parsePair = do
  parseParens $ do
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

parseApp = do
  parseParens $ do
    f <- parseInfer
    parseOp "$"
    a <- parseCheck
    return $ IApp f a

parseAnn = do
  parseParens $ do
    tm <- parseCheck
    parseOp ":"
    tp <- parseCheck
    return $ IAnn tm tp

----------------------------------------------------------------------