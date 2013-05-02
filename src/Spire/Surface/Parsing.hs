module Spire.Surface.Parsing
  (parseProgram, parseTerm, wildcard, formatParseError)
where
import Spire.Surface.Types
import Spire.Canonical.Types
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.Error
import Text.Printf
import Data.Functor.Identity(Identity)

----------------------------------------------------------------------

parseProgram :: FilePath -> String -> Either ParseError Statements
parseProgram = parse (parseSpaces >> parseDefs)

parseTerm :: FilePath -> String -> Either ParseError Syntax
parseTerm = parse (parseSpaces >> parseSyntax)

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

wildcard = "_"
ops = ["\\", "->", "*", ",", ":", "$", "=", "++", "==",
       "|", "#", "=>"]
keywords = [
  "in", "if", "then", "else",
  "Unit", "Bool", "String", "Type",
  "tt", "true", "false",
  "caseBool",
  "proj1", "proj2",
  "Done", "Rec"
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
parseStringLit = try $ stringLiteral tokenizer
parseParens :: MParser a -> MParser a
parseParens = try . parens tokenizer

----------------------------------------------------------------------

parseDefs :: MParser Statements
parseDefs = many parseDef

parseDef :: MParser Statement
parseDef = do
  l <- parseIdent
  parseOp ":"
  tp <- parseSyntax
  parseToken l
  parseOp "="
  tm <- parseSyntax
  return $ SDef l tm tp

----------------------------------------------------------------------

parseSyntax :: MParser Syntax
parseSyntax = buildExpressionParser table parseChoice

parseChoice :: MParser Syntax
parseChoice = try $ choice [
    parseParens parseSyntax
  , parseUnit
  , parseBool
  , parseString
  , parseDesc
  , parseType
  , parseTT
  , parseTrue
  , parseFalse
  , parseQuotes
  , parseDUnit
  , parseDRec
  , parseIf
  , parseCaseBool
  , parseProj1
  , parseProj2
  , parseVar
  , parseLam
  , parseAnn
  ]

failIfStmt =
  -- definition type declaration or assignment is next
  try . notFollowedBy $ parseIdent >> (parseOp ":" <|> parseOp "=")

table = [
    [Infix parseSpaceApp AssocLeft]
  , [Infix (parseInfix "++" SStrAppend) AssocRight]
  , [Infix (parseInfix "==" SStrEq) AssocNone,
     Infix (parseInfix "," SPair) AssocRight]
  , [Infix (parseInfix "$" SApp) AssocRight]
  , [Infix (parseInfix "*" (boundInfix SSg)) AssocRight]
  , [Infix (parseInfix "->" (boundInfix SPi)) AssocRight]
  , [  Infix (parseInfix "=>" (boundInfix SDPi)) AssocRight
     , Infix (parseInfix "#" (boundInfix SDSg)) AssocRight]
  , [Infix (parseInfix "|" SDSum) AssocRight]
  ] where
  parseSpaceApp = failIfStmt >> return SApp
  parseInfix op con = parseOp op >> return con

  boundInfix con = \ aT bT -> case aT of
    SAnn (SVar l) aT' -> con aT' $ Bound (l , bT)
    _ -> con aT $ Bound (wildcard , bT)

----------------------------------------------------------------------

parseIf = do
  parseKeyword "if"
  b <- parseSyntax
  parseKeyword "then"
  c1 <- parseSyntax
  parseKeyword "else"
  c2 <- parseSyntax
  return $ SIf b c1 c2

parseCaseBool = try $ do
  parseKeyword "caseBool"
  (l , pT) <- parseParens $ do
    l <- parseIdent
    parseKeyword "in"
    pT <- parseSyntax
    return (l , pT)
  b <- parseSyntax
  parseKeyword "then"
  pt <- parseSyntax
  parseKeyword "else"
  pf <- parseSyntax
  return $ SCaseBool (Bound (l , pT)) pt pf b

parseProj1 = try $ do
  parseKeyword "proj1"
  ab <- parseSyntax
  return $ SProj1 ab

parseProj2 = try $ do
  parseKeyword "proj2"
  ab <- parseSyntax
  return $ SProj2 ab

parseLam = try $ do
  parseOp "\\"
  l <- parseIdent
  parseOp "->"
  tm <- parseSyntax
  return $ SLam (Bound (l , tm))

parseAnn = parseParens $ do
  --    binding   or  annotation
  a <- parseVar <|> parseSyntax
  parseOp ":"
  b <- parseSyntax
  return $ SAnn a b

----------------------------------------------------------------------

parseTT = parseKeyword "tt" >> return STT
parseTrue = parseKeyword "true" >> return STrue
parseFalse = parseKeyword "false" >> return SFalse
parseUnit = parseKeyword "Unit" >> return SUnit
parseBool = parseKeyword "Bool" >> return SBool
parseString = parseKeyword "String" >> return SString
parseDesc = parseKeyword "Desc" >> return SDesc
parseType = parseKeyword "Type" >> return SType
parseDUnit = parseKeyword "Done" >> return SDUnit
parseDRec = parseKeyword "Rec" >> return SDRec

parseQuotes = do
  s <- parseStringLit
  return $ SQuotes s

parseVar = do
  l <- parseIdent
  return $ SVar l

----------------------------------------------------------------------