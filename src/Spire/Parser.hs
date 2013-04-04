module Spire.Parser where
import Spire.Surface
import Text.ParserCombinators.Parsec

----------------------------------------------------------------------

pTerm = do
  spaces
  tm <- pCheck
  spaces
  return tm

pCheck = do
      try (pParens pCheck)
  <|> try pTrue
  <|> try pFalse
  <|> try pPair
  <|> try pLam
  <|> (return . Infer =<< try pInfer)
  <|> fail "Could not parse checked term."

pInfer = do
      try (pParens pInfer)
  <|> try pBool
  <|> try pType
  <|> try pPi
  <|> try pSg
  <|> try pVar
  <|> try pIf
  <|> try pAnn
  <|> try pProj1
  <|> try pProj2
  <|> fail "Could not parse inferred term."

----------------------------------------------------------------------

pTrue = string "true" >> return CTrue
pFalse = string "false" >> return CFalse

pPair = do
  x <- pCheck
  spaces1
  char ','
  spaces1  
  y <- pCheck
  return $ CPair x y

pLam = do
  string "->"
  spaces1
  tm <- pCheck
  return $ CLam tm

----------------------------------------------------------------------

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
  f <- pInfer
  spaces1
  char '$'
  spaces1
  a <- pCheck
  return $ IApp f a

pAnn = do
  tm <- pCheck
  spaces1
  char ':'
  spaces1
  tp <- pCheck
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