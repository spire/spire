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
import Control.Applicative ((<*))

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

ops = ["\\", "->", "*", ",", ":", "$", "=", "::" , "[]", "=="]
keywords = [
  "if", "then", "else",
  "Unit", "Bool", "List", "Tag", "String", "Type", "Branches",
  "tt", "true", "false", "refl", "here", "there",
  "elimBool", "elimList", "subst", "case",
  "proj1", "proj2",
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
parseProg = many parseDef <* eof

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
  , parseElimBool
  , parseProj1
  , parseProj2
  , parseThere
  , parseList
  , parseTag
  , parseLam
  ]

parseAtom = choice
  [ parseParens parseSyntax
  , parseVar
  , parseAnn

  , parseQuotes
  , parseTT
  , parseTrue
  , parseFalse
  , parseNil
  , parseRefl
  , parseHere
  , parseUnit
  , parseBool
  , parseString
  , parseType
  , parseWildCard
  ]

failIfStmt =
  -- a type declaration or assignment (as part of a definition) is next
  try . notFollowedBy $ parseIdent >> (parseOp ":" <|> parseOp "=")

table = [
    [Infix parseSpaceApp             AssocLeft]
  , [Infix (parseInfix "::" SCons)   AssocRight]
  , [Infix (parseInfix ","  SPair)   AssocRight]
  , [Infix (parseInfix "$"  SApp)    AssocRight]
  , [Infix (parseInfix "*"  infixSg) AssocRight]
  , [Infix (parseInfix "->" infixPi) AssocRight]
  , [Infix (parseInfix "==" SEq)     AssocNone]
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

parseElimBool = do
  parseKeyword "elimBool"
  SLam m <- parseParens parseLam <?> "expecting motive \"(\\ x -> e)\""
  pt <- parseAtom
  pf <- parseAtom
  b <- parseAtom
  return $ SElimBool m pt pf b

parseProj1 = try $ do
  parseKeyword "proj1"
  ab <- parseAtom
  return $ SProj1 ab

parseProj2 = try $ do
  parseKeyword "proj2"
  ab <- parseAtom
  return $ SProj2 ab

parseThere = try $ do
  parseKeyword "there"
  t <- parseAtom
  return $ SThere t

parseList = try $ do
  parseKeyword "List"
  _A <- parseAtom
  return $ SList _A

parseTag = try $ do
  parseKeyword "Tag"
  _E <- parseAtom
  return $ STag _E

-- \ x -> e
-- \ _ -> e
parseLam = try $ do
  parseOp "\\"
  l <- parseWildOrIdent
  parseOp "->"
  tm <- parseSyntax
  return $ sLam l tm

parseAnn = parseParens $ do
  --    binding   or  annotation
  a <- parseVar <|> parseSyntax
  parseOp ":"
  b <- parseSyntax
  return $ SAnn a b

----------------------------------------------------------------------

parseNil      = parseOp      "[]"     >> return SNil

parseTT       = parseKeyword "tt"     >> return STT
parseTrue     = parseKeyword "true"   >> return STrue
parseFalse    = parseKeyword "false"  >> return SFalse
parseRefl     = parseKeyword "refl"   >> return SRefl
parseHere     = parseKeyword "here"   >> return SHere
parseUnit     = parseKeyword "Unit"   >> return SUnit
parseBool     = parseKeyword "Bool"   >> return SBool
parseString   = parseKeyword "String" >> return SString
parseType     = parseKeyword "Type"   >> return SType
parseWildCard = parseKeyword wildcard >> return SWildCard

parseQuotes = return . SQuotes =<< parseStringLit
parseVar    = return . sVar =<< parseIdent

----------------------------------------------------------------------
