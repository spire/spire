module Spire.Surface.Parsing (parseProgram , parseTerm , formatParseError) where
import Spire.Canonical.Types
import Spire.Expression.Types
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.Error
import Text.Printf
import Data.Functor.Identity(Identity)


parseProgram :: FilePath -> String -> Either ParseError [Def]
parseProgram = parse (parseSpaces >> parseDefs)

parseTerm :: String -> Either ParseError Check
parseTerm = parse (parseSpaces >> parseCheck) "(unknown)"

-- Format error message so that Emacs' compilation mode can parse the
-- location information.
formatParseError :: ParseError -> String
formatParseError error = printf "%s:%i:%i:\n%s" file line col msg
  where
  file = sourceName . errorPos $ error
  line = sourceLine . errorPos $ error
  col = sourceColumn . errorPos $ error
  -- Copied from 'Show' instance for 'ParseError':
  -- http://hackage.haskell.org/packages/archive/parsec/latest/doc/html/src/Text-Parsec-Error.html#ParseError
  msg = showErrorMessages "or" "unknown parse error"
          "expecting" "unexpected" "end of input"
          (errorMessages error)

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
  <|> try parseLamAnn
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

parseDefs :: MParser [Def]
parseDefs = many parseDef

parseDef :: MParser Def
parseDef = do
  l <- parseIdent
  parseOp ":"
  tp <- parseCheck
  parseToken l
  parseOp "="
  tm <- parseCheck
  return (l , tm , tp)

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
  return $ CLam (Bound (l , tm))

parseLamAnn = do
  parseOp "\\"
  (l , aT) <- parseParens $ do
    l <- parseIdent
    parseOp ":"
    aT <- parseCheck
    return (l , aT)
  parseOp "->"
  a <- parseInfer
  return $ ILamAnn aT (Bound (l , a))

----------------------------------------------------------------------

parseTT = parseKeyword "tt" >> return ITT
parseTrue = parseKeyword "true" >> return ITrue
parseFalse = parseKeyword "false" >> return IFalse
parseUnit = parseKeyword "Unit" >> return IUnit
parseBool = parseKeyword "Bool" >> return IBool
parseType = parseKeyword "Type" >> return IType

-- (x : t1) -> t2
parsePi = do
  (l , a) <- parseParens $ do
    l <- parseIdent
    parseOp ":"
    a <- parseCheck
    return (l , a)
  parseOp "->"
  b <- parseCheck
  return $ IPi a (Bound (l , b))

-- (x : t1) * t2
parseSg = do
  (l , a) <- parseParens $ do
    l <- parseIdent
    parseOp ":"
    a <- parseCheck
    return (l , a)
  parseOp "*"
  b <- parseCheck
  return $ ISg a (Bound (l , b))

parseVar = do
  l <- parseIdent
  return $ IVar l

-- if c then t else f
parseIf = do
  parseKeyword "if"
  b <- parseCheck
  parseKeyword "then"
  c1 <- parseInfer
  parseKeyword "else"
  c2 <- parseInfer
  return $ IIf b c1 c2

-- caseBool (x in M) t f b
parseCaseBool = do
  parseKeyword "caseBool"
  (l , pT) <- parseParens $ do
    l <- parseIdent
    parseOp "in"
    pT <- parseCheck
    return (l , pT)
  pt <- parseCheck
  pf <- parseCheck
  b <- parseCheck
  return $ ICaseBool (Bound (l , pT)) pt pf b

parseProj1 = do
  parseKeyword "proj1"
  ab <- parseInfer
  return $ IProj1 ab

parseProj2 = do
  parseKeyword "proj2"
  ab <- parseInfer
  return $ IProj2 ab

-- f $ x
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