module Spire.Surface.Elaborating where
import Spire.Surface.Types
import Spire.Surface.Parsing
import Spire.Expression.Types
import Spire.Canonical.Types
import Control.Monad.Error

----------------------------------------------------------------------

elabS :: Statements -> Result Defs
elabS [] = return []
elabS (SDef l a aT : ds) = do
  a' <- elabC a
  aT' <- elabC aT
  ds' <- elabS ds
  return ((l , a' , aT') : ds')

----------------------------------------------------------------------

elabC :: Syntax -> Result Check
elabC (SPair a b) = do
  a' <- elabC a
  b' <- elabC b
  return $ CPair a' b'
elabC (SLam b) = do
  b' <- elabBC b
  return $ CLam b'
elabC a = do
  a' <- elabI a
  return $ Infer a'

----------------------------------------------------------------------

elabI :: Syntax -> Result Infer
elabI SUnit = return IUnit
elabI SBool = return IBool
elabI SString = return IString
elabI SDesc = return IDesc
elabI SType = return IType
elabI STT = return ITT
elabI STrue = return ITrue
elabI SFalse = return IFalse
elabI (SQuotes str) = return $ IQuotes str
elabI (SVar i) = return $ IVar i

elabI SDUnit = return IDUnit
elabI SDRec = return IDRec
elabI (SDSum d e) = do
  d' <- elabC d
  e' <- elabC e
  return $ IDSum d' e'
elabI (SDProd d e) = do
  d' <- elabC d
  e' <- elabC e
  return $ IDProd d' e'
elabI (SDPi aT fD) = do
  aT' <- elabC aT
  fD' <- elabBC fD
  return $ IDPi aT' fD'
elabI (SDSg aT fD) = do
  aT' <- elabC aT
  fD' <- elabBC fD
  return $ IDSg aT' fD'

elabI (SPi aT bT) = do
  aT' <- elabC aT
  bT' <- elabBC bT
  return $ IPi aT' bT'
elabI (SSg aT bT) = do
  aT' <- elabC aT
  bT' <- elabBC bT
  return $ ISg aT' bT'
elabI (SStrAppend a b) = do
  a' <- elabC a
  b' <- elabC b
  return $ IStrAppend a' b'
elabI (SStrEq a b) = do
  a' <- elabC a
  b' <- elabC b
  return $ IStrEq a' b'
elabI (SIf b c1 c2) = do
  b' <- elabC b
  c1' <- elabI c1
  c2' <- elabI c2
  return $ IIf b' c1' c2'
elabI (SCaseBool pT pt pf b) = do
  pT' <- elabBC pT
  pt' <- elabC pt
  pf' <- elabC pf
  b' <- elabC b
  return $ ICaseBool pT' pt' pf' b'
elabI (SProj1 ab) = do
  ab' <- elabI ab
  return $ IProj1 ab'
elabI (SProj2 ab) = do
  ab' <- elabI ab
  return $ IProj2 ab'
elabI (SApp f a) = do
  f' <- elabI f
  a' <- elabC a
  return $ IApp f' a'
elabI (SAnn a aT) = do
  a' <- elabC a
  aT' <- elabC aT
  return $ IAnn a' aT'
elabI a@(SPair _ _) = failUnannotated a
elabI a@(SLam _) = failUnannotated a

----------------------------------------------------------------------

elabBC :: Bound Syntax -> Result (Bound Check)
elabBC (Bound (l , a)) = do
  a' <- elabC a
  return $ Bound (l , a')

failUnannotated :: Syntax -> Result Infer
failUnannotated a = throwError $
  "Failed to infer the type of this term, please annotate it:\n" ++
  show a

----------------------------------------------------------------------