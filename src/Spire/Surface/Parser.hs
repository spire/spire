{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  #-}

module Spire.Surface.Parser where
import Spire.Surface.Types
import Spire.Canonical.Types
import Unbound.LocallyNameless (bind , s2n)
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.Error
import Text.Printf
import Data.Functor.Identity (Identity)
import Control.Applicative ((<$>))

----------------------------------------------------------------------

parseProgram :: FilePath -> String -> Either ParseError SProg
parseProgram = parse (parseSpaces >> parseProg)

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

ops = ["\\", "->", "*", ",", ":", "$", "=", "++", "==",
       "|", "#", "=>", "?", "."]
keywords = [
  "if", "then", "else",
  "Unit", "Bool", "String", "Type",
  "tt", "true", "false",
  "caseBool",
  "proj1", "proj2",
  "Fix", "Desc" , "Done", "Rec" ,
  wildcard
  ]

def = emptyDef {
  commentStart = "{-"
, commentEnd = "-}"
, commentLine = "--"
, identStart = letter
, identLetter = alphaNum <|> char '\''
, opStart = oneOf (map head ops)
, opLetter = oneOf (concat ops)
, reservedOpNames = ops
, reservedNames = keywords
}

type ParserM a = ParsecT [Char] () Identity a

tokenizer = makeTokenParser def
parseOp = reservedOp tokenizer
parseKeyword = reserved tokenizer
-- Excludes keywords.
parseIdent = identifier tokenizer
parseWildOrIdent = (parseKeyword wildcard >> return wildcard) <|> parseIdent
parseToken = symbol tokenizer
parseSpaces = whiteSpace tokenizer
parseStringLit = try $ stringLiteral tokenizer
parseParens :: ParserM a -> ParserM a
parseParens = try . parens tokenizer
parseAngles :: ParserM a -> ParserM a
parseAngles = try . angles tokenizer

----------------------------------------------------------------------

parseProg :: ParserM SProg
parseProg = many parseDef

parseDef :: ParserM SDef
parseDef = do
  l <- parseIdent
  parseOp ":"
  tp <- parseSyntax
  parseToken l
  parseOp "="
  tm <- parseSyntax
  return $ SDef (s2n l) tm tp

----------------------------------------------------------------------

parseSyntax :: ParserM Syntax
parseSyntax = buildExpressionParser table parseChoice

parseChoice :: ParserM Syntax
parseChoice = try $ choice [
    parseAtom
  , parseIf
  , parseCaseBool
  , parseProj1
  , parseProj2
  , parseLam
  , parseBindMeta
  ]

parseAtom = choice
  [ parseParens parseSyntax
  , parseVar
  , parseAnn

  , parseTT
  , parseTrue
  , parseFalse
  , parseUnit
  , parseBool
  , parseType
  , parseWildCard
  ]

failIfStmt =
  -- a type declaration or assignment (as part of a definition) is next
  try . notFollowedBy $ parseIdent >> (parseOp ":" <|> parseOp "=")

table = [
    [Infix parseSpaceApp AssocLeft]
  , [Infix (parseInfix "," SPair) AssocRight]
  , [Infix (parseInfix "$" SApp) AssocRight]
  , [Infix (parseInfix "*" infixSg) AssocRight]
  , [Infix (parseInfix "->" infixPi) AssocRight]
  ] where

  parseSpaceApp = failIfStmt >> return SApp

  parseInfix op con = parseOp op >> return con

  infixSg (SAnn (SVar nm) _A) _B = SSg _A (bind nm _B)
  infixSg _A                  _B = sSg _A wildcard _B

  infixPi (SAnn (SVar nm) _A) _B = SPi _A (bind nm _B)
  infixPi _A                  _B = sPi _A wildcard _B

----------------------------------------------------------------------

parseIf = do
  parseKeyword "if"
  b <- parseSyntax
  parseKeyword "then"
  c1 <- parseSyntax
  parseKeyword "else"
  c2 <- parseSyntax
  return $ SIf b c1 c2

parseCaseBool = do
  parseKeyword "caseBool"
  SLam m <- parseParens parseLam <?> "expecting motive \"(\\ x -> e)\""
  pt <- parseAtom
  pf <- parseAtom
  b <- parseAtom
  return $ SCaseBool m pt pf b

parseProj1 = try $ do
  parseKeyword "proj1"
  ab <- parseAtom
  return $ SProj1 ab

parseProj2 = try $ do
  parseKeyword "proj2"
  ab <- parseAtom
  return $ SProj2 ab

-- \ x -> e
-- \ _ -> e
parseLam = try $ do
  parseOp "\\"
  l <- parseWildOrIdent
  parseOp "->"
  tm <- parseSyntax
  return $ sLam l tm

-- ? x : T . e
-- ? x : T = t . e
--
-- I was going to use the "->" in place of ".", to be closer to the
-- lambda syntax, but that creates problems: should
--
--   ?x:Type = A -> B -> C
--
-- parse as
--
--   ?x:Type = (A -> B) -> C
--
-- or
--
--   ?x:Type = A -> (B -> C)
--
-- ? Compare with
--
--   ?x:Type = A -> B . C
--
-- which can only mean
--
--   ?x:Type = (A -> B) . C
--
-- There will be more problem if/when equality is itself a type ... on
-- the other hand, it's not clear the user is actually expected to
-- ever input meta variable bindings, but rather just wild cards "_",
-- which elaborate to bindings ...
parseBindMeta = try $ do
  parseOp "?"
  x <- parseIdent
  parseOp ":"
  _T <- parseSyntax
  t <- choice [ parseOp "=" >> Just <$> parseSyntax
              , return Nothing ]
  parseOp "."
  e <- parseSyntax
  return $ sBindMeta x _T t e

parseAnn = parseParens $ do
  --    binding   or  annotation
  a <- parseVar <|> parseSyntax
  parseOp ":"
  b <- parseSyntax
  return $ SAnn a b

----------------------------------------------------------------------

parseTT    = parseKeyword "tt"    >> return STT
parseTrue  = parseKeyword "true"  >> return STrue
parseFalse = parseKeyword "false" >> return SFalse
parseUnit  = parseKeyword "Unit"  >> return SUnit
parseBool  = parseKeyword "Bool"  >> return SBool
parseType  = parseKeyword "Type"  >> return SType
parseWildCard = parseKeyword wildcard >> return SWildCard

parseVar = return . sVar =<< parseIdent

----------------------------------------------------------------------