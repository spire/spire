module Spire.Parser where
import Spire.Surface
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Combinator
import Text.Parsec.Language
import Data.Functor.Identity(Identity)

----------------------------------------------------------------------

ops = ["\\", "->", "*", ",", ":", "$", "in", "="]
keywords = [
  "Unit", "Bool", "Type",
  "tt", "true", "false",
  "caseBool", "if", "then", "else",
  "proj1", "proj2"
  ]

def = emptyDef {
  commentStart = "{-"
, commentEnd = "-}"
, commentLine = "--"
, identStart = letter
, identLetter = alphaNum
, opStart = oneOf (map head ops)
, opLetter = oneOf (concat ops)
, reservedOpNames = ops
, reservedNames = keywords
}

type MParser a = ParsecT [Char] () Identity a

tokenizer = makeTokenParser def
parseOp = reservedOp tokenizer
parseKeyword = reserved tokenizer
parseIdent = identifier tokenizer
parseToken = symbol tokenizer
parseSpaces = whiteSpace tokenizer
parseParens :: MParser a -> MParser a
parseParens = parens tokenizer

parseTerm :: String -> Either ParseError Check
parseTerm = parse (parseSpaces >> parseCheck) "(unknown)"

parseProgram :: String -> Either ParseError Defs
parseProgram = parse (parseSpaces >> parseDefs) "(unknown)"

----------------------------------------------------------------------

parseCheck :: MParser Check
parseCheck = do
      try (parseParens parseCheck)
  <|> try parsePair
  <|> try parseLam
  <|> (return . Infer =<< try parseInfer)

parseInfer :: MParser Infer
parseInfer = do
      try parsePi
  <|> try parseSg
  <|> try parseCaseBool
  <|> try parseApp
  <|> try parseAnn
  <|> try (parseParens parseInfer)
  <|> parseTT
  <|> parseTrue
  <|> parseFalse
  <|> parseUnit
  <|> parseBool
  <|> parseType
  <|> try parseVar
  <|> try parseIf
  <|> try parseProj1
  <|> try parseProj2

----------------------------------------------------------------------

parseDefs :: MParser Defs
parseDefs = do
  d <- parseDef
  return (d : [])

-- parseDefs = do
--       (eof >> return [])
--   <|> parseAllDefs

parseAllDefs :: MParser Defs
parseAllDefs = do
  ds <- parseDefs
  d <- parseDef
  return (d : ds)

parseDef :: MParser Def
parseDef = do
  l <- parseIdent
  parseOp ":"
  tp <- parseCheck
  parseToken l
  parseOp "="
  tm <- parseCheck
  return (l , IAnn tm tp)

----------------------------------------------------------------------

parsePair = parseParens $ do
  x <- parseCheck
  parseOp ","
  y <- parseCheck
  return $ CPair x y

parseLam = do
  parseOp "\\"
  l <- parseIdent
  parseOp "->"
  tm <- parseCheck
  return $ CLam l tm

----------------------------------------------------------------------

parseTT = parseKeyword "tt" >> return ITT
parseTrue = parseKeyword "true" >> return ITrue
parseFalse = parseKeyword "false" >> return IFalse
parseUnit = parseKeyword "Unit" >> return IUnit
parseBool = parseKeyword "Bool" >> return IBool
parseType = parseKeyword "Type" >> return IType

parsePi = do
  (l , a) <- parseParens $ do
    l <- parseIdent
    parseOp ":"
    a <- parseCheck
    return (l , a)
  parseOp "->"
  b <- parseCheck
  return $ IPi a l b

parseSg = do
  (l , a) <- parseParens $ do
    l <- parseIdent
    parseOp ":"
    a <- parseCheck
    return (l , a)
  parseOp "*"
  b <- parseCheck
  return $ ISg a l b

parseVar = do
  l <- parseIdent
  return $ IVar l

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
  (l , p) <- parseParens $ do
    l <- parseIdent
    parseOp "in"
    p <- parseCheck
    return (l , p)
  pt <- parseCheck
  pf <- parseCheck
  b <- parseCheck
  return $ ICaseBool l p pt pf b

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