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
import Control.Applicative ((<*))
import Control.Monad (replicateM)

----------------------------------------------------------------------

parseProgram :: FilePath -> String -> Either ParseError SProg
parseProgram = parse (parseSpaces >> parseProg)

-- Format error message so that Emacs' compilation mode can parse the
-- location information.
formatParseError :: ParseError -> String
formatParseError error = printf "%s:%i:%i:\n%s" file line col msg
  where
  file = sourceName   . errorPos $ error
  line = sourceLine   . errorPos $ error
  col  = sourceColumn . errorPos $ error
  -- Copied from 'Show' instance for 'ParseError':
  -- http://hackage.haskell.org/packages/archive/parsec/latest/doc/html/src/Text-Parsec-Error.html#ParseError
  msg = showErrorMessages "or" "unknown parse error"
          "expecting" "unexpected" "end of input"
          (errorMessages error)

----------------------------------------------------------------------

ops = ["\\", "->", "*", ",", ":", "$", "=", "::" , "[]", "==", "=>"]
keywords = [
  "data", "where", "end", "let", "in",
  "refl", "here", "there", "init",
  "End", "Rec", "Arg",

  "if", "then", "else",
  wildcard
  ]

def = emptyDef {
  commentStart = "{-"
, commentEnd = "-}"
, commentLine = "--"
, identStart = letter
, identLetter = alphaNum <|> char '-' <|> char '\''
, opStart = oneOf (map head ops)
, opLetter = oneOf (concat ops)
, reservedOpNames = ops
, reservedNames = keywords
}

type ParserM a = Parsec String () a

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
parseProg = many parseStmt <* eof

parseStmt :: ParserM Stmt
parseStmt = parseData <|> parseDef

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
  , parseThere
  , parseEnd
  , parseRec
  , parseInit
  , parseLam
  , parseArg
  ]

parseAtom = choice
  [ parseParens parseSyntax
  , parseVar
  , parseAnn

  , parseQuotes
  , parseNil
  , parseRefl
  , parseHere
  , parseWildCard
  ]

failIfStmt =
  -- a type declaration or assignment (as part of a definition) is next
  try . notFollowedBy $ parseOp "=>" <|> parseKeyword "data" <|> parseKeyword "end" <|> (parseIdent >> (parseOp ":" <|> (parseOp "=")))

table = [
    [Infix parseSpaceApp             AssocLeft]
  , [Infix (parseInfix "::" sCons)   AssocRight]
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

parseData = try $ do
  parseKeyword "data"
  _N <- parseIdent
  _P <- many parseParam
  parseOp ":"
  _I <- parseIndices
  parseKeyword "where"
  cs <- many $ parseConstr _N _P _I
  parseKeyword "end"
  return $ SData _N _P _I cs

parseParam = parseParens $ do
  l <- parseIdent
  parseOp ":"
  a <- parseSyntax
  return $ (l , a)

parseIndices = do
  _I <- sepBy (parseNamedIndex <|> parseUnnamedIndex) (parseOp "=>")
  return $ init _I

parseUnnamedIndex = try $ do
  a <- parseSyntax
  return $ (wildcard , a)

parseNamedIndex = try . parseParens $ do
  l <- parseIdent
  parseOp ":"
  a <- parseSyntax
  return $ (l , a)

parseConstr _N _P _I = try $ do
  l <- parseIdent
  parseOp ":"
  cs <- sepBy (parseFix _N _P _I <|> parseNamedArg <|> parseUnnamedArg) (parseOp "=>")
  return $ (l , cs)

parseNamedArg = try . parseParens $ do
  l <- parseIdent
  parseOp ":"
  _A <- parseSyntax
  return $ Arg l _A

parseUnnamedArg = try $ do
  _A <- parseSyntax
  return $ Arg wildcard _A

parseFix _N _P _I = try $ do
  parseToken _N
  mapM_ parseToken (map fst _P)
  i <- replicateM (length _I) parseAtom
  return $ Fix i

----------------------------------------------------------------------

parseIf = do
  parseKeyword "if"
  b <- parseSyntax
  parseKeyword "then"
  c1 <- parseSyntax
  parseKeyword "else"
  c2 <- parseSyntax
  return $ SIf b c1 c2

parseThere = try $ do
  parseKeyword "there"
  t <- parseAtom
  return $ SThere t

parseEnd = try $ do
  parseKeyword "End"
  i <- parseAtom
  return $ SEnd i

parseRec = try $ do
  parseKeyword "Rec"
  i  <- parseAtom
  _D <- parseAtom
  return $ SRec i _D

parseInit = try $ do
  parseKeyword "init"
  xs <- parseAtom
  return $ SInit xs

parseAnn = parseParens $ do
  --    binding   or  annotation
  a <- parseVar <|> parseSyntax
  parseOp ":"
  b <- parseSyntax
  return $ SAnn a b

-- \ x -> e
-- \ _ -> e
parseLam = try $ do
  parseOp "\\"
  ls <- many1 parseWildOrIdent
  parseOp "->"
  tm <- parseSyntax
  return $ foldr sLam tm ls

parseLamArg = do
  SLam _P <- parseParens parseLam <?> "expecting motive \"(\\ x -> e)\""
  return _P

parseArg = do
  parseKeyword "Arg"
  _A <- parseAtom
  _B <- parseLamArg
  return $ SArg _A _B

----------------------------------------------------------------------

parseNil      = parseOp      "[]"     >> return sNil

parseRefl     = parseKeyword "refl"   >> return SRefl
parseHere     = parseKeyword "here"   >> return SHere
parseWildCard = parseKeyword wildcard >> return SWildCard

parseQuotes = return . SQuotes =<< parseStringLit
parseVar    = return . sVar =<< parseIdent

----------------------------------------------------------------------
