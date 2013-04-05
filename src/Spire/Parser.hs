module Spire.Parser where
import Spire.Surface
import Text.ParserCombinators.Parsec

----------------------------------------------------------------------

pTerm = do
  spaces
  tm <- pCheck
  spaces
  xs <- many anyChar
  if null xs
  then return tm
  else fail $ "Leftover input:\n" ++ xs

pCheck = do
      try (pParens pCheck)
  <|> try pPair
  <|> try pLam
  <|> (return . Infer =<< try pInfer)

pInfer = do
      try pAnn
  <|> try pApp
  <|> try (pParens pInfer)
  <|> try pTT
  <|> try pTrue
  <|> try pFalse
  <|> try pUnit
  <|> try pBool
  <|> try pType
  <|> try pPi
  <|> try pSg
  <|> try pVar
  <|> try pIf
  <|> try pProj1
  <|> try pProj2

----------------------------------------------------------------------

pPair = do
  char '('
  spaces
  x <- pCheck
  spaces1
  char ','
  spaces1  
  y <- pCheck
  spaces
  char ')'
  return $ CPair x y

pLam = do
  string "->"
  spaces1
  tm <- pCheck
  return $ CLam tm

----------------------------------------------------------------------

pTT = string "tt" >> return ITT
pTrue = string "true" >> return ITrue
pFalse = string "false" >> return IFalse
pUnit = string "Unit" >> return IUnit
pBool = string "Bool" >> return IBool
pType = string "Type" >> return IType

pPi = do
  string "Pi"
  spaces1
  a <- pCheck
  spaces1
  b <- pCheck
  return $ IPi a b

pSg = do
  string "Sg"
  spaces1
  a <- pCheck
  spaces1
  b <- pCheck
  return $ ISg a b

pVar = do
  i <- many1 digit
  return $ IVar (read i)

pIf = do
  string "if"
  spaces1
  b <- pCheck
  spaces1
  string "then"
  spaces1
  c1 <- pInfer
  spaces1
  string "else"
  spaces1
  c2 <- pInfer
  return $ IIf b c1 c2

pProj1 = do
  string "proj1"
  spaces1
  ab <- pInfer
  return $ IProj1 ab

pProj2 = do
  string "proj2"
  spaces1
  ab <- pInfer
  return $ IProj2 ab

pApp = do
  char '('
  spaces
  f <- pInfer
  spaces1
  char '$'
  spaces1
  a <- pCheck
  spaces
  char ')'
  return $ IApp f a

pAnn = do
  char '('
  spaces
  tm <- pCheck
  spaces1
  char ':'
  spaces1
  tp <- pCheck
  spaces
  char ')'
  return $ IAnn tm tp

----------------------------------------------------------------------

pParens p = do
  char '('
  spaces
  tm <- p
  spaces
  char ')'
  return tm

spaces1 = many1 space >> return ()

----------------------------------------------------------------------

parseTerm :: String -> Either ParseError Check
parseTerm tm = parse pTerm "(unknown)" tm

----------------------------------------------------------------------