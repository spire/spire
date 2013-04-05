module Spire.Parser where
import Spire.Surface
import Text.ParserCombinators.Parsec

----------------------------------------------------------------------

parseExpr = do
  spaces
  tm <- parseCheck
  spaces
  xs <- many anyChar
  if null xs
  then return tm
  else fail $ "Leftover input:\n" ++ xs

parseCheck = do
      try (parseParens parseCheck)
  <|> try parsePair
  <|> try parseLam
  <|> (return . Infer =<< try parseInfer)

parseInfer = do
      try parseAnn
  <|> try parseApp
  <|> try (parseParens parseInfer)
  <|> try parseTT
  <|> try parseTrue
  <|> try parseFalse
  <|> try parseUnit
  <|> try parseBool
  <|> try parseType
  <|> try parsePi
  <|> try parseSg
  <|> try parseVar
  <|> try parseIf
  <|> try parseProj1
  <|> try parseProj2

----------------------------------------------------------------------

parsePair = do
  char '('
  spaces
  x <- parseCheck
  spaces1
  char ','
  spaces1  
  y <- parseCheck
  spaces
  char ')'
  return $ CPair x y

parseLam = do
  string "->"
  spaces1
  tm <- parseCheck
  return $ CLam tm

----------------------------------------------------------------------

parseTT = string "tt" >> return ITT
parseTrue = string "true" >> return ITrue
parseFalse = string "false" >> return IFalse
parseUnit = string "Unit" >> return IUnit
parseBool = string "Bool" >> return IBool
parseType = string "Type" >> return IType

parsePi = do
  string "Pi"
  spaces1
  a <- parseCheck
  spaces1
  b <- parseCheck
  return $ IPi a b

parseSg = do
  string "Sg"
  spaces1
  a <- parseCheck
  spaces1
  b <- parseCheck
  return $ ISg a b

parseVar = do
  i <- many1 digit
  return $ IVar (read i)

parseIf = do
  string "if"
  spaces1
  b <- parseCheck
  spaces1
  string "then"
  spaces1
  c1 <- parseInfer
  spaces1
  string "else"
  spaces1
  c2 <- parseInfer
  return $ IIf b c1 c2

parseProj1 = do
  string "proj1"
  spaces1
  ab <- parseInfer
  return $ IProj1 ab

parseProj2 = do
  string "proj2"
  spaces1
  ab <- parseInfer
  return $ IProj2 ab

parseApp = do
  char '('
  spaces
  f <- parseInfer
  spaces1
  char '$'
  spaces1
  a <- parseCheck
  spaces
  char ')'
  return $ IApp f a

parseAnn = do
  char '('
  spaces
  tm <- parseCheck
  spaces1
  char ':'
  spaces1
  tp <- parseCheck
  spaces
  char ')'
  return $ IAnn tm tp

----------------------------------------------------------------------

parseParens p = do
  char '('
  spaces
  tm <- p
  spaces
  char ')'
  return tm

spaces1 = many1 space >> return ()

----------------------------------------------------------------------

parseTerm :: String -> Either ParseError Check
parseTerm tm = parse parseExpr "(unknown)" tm

----------------------------------------------------------------------