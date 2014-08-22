module Spire.Surface.Elaborator (elabProg) where
import Control.Monad.Except
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Applicative
import Unbound.LocallyNameless
import Spire.Canonical.Types
import Spire.Surface.Types
import Spire.Expression.Types

----------------------------------------------------------------------

elabProg :: SProg -> SpireM CProg
elabProg [] = return []
elabProg (SData _N _As _I cs : xs) = let
  _N' = elabName _N
  _E = elabEnum _N (map fst cs)
  in elabProg (_N' : _E : xs)
elabProg (SDef nm a _A : xs) = do
  _A' <- elab _A
  a'  <- elab a
  xs' <- elabProg xs
  return (CDef nm a' _A' : xs')

elabName :: String -> SDecl
elabName _N = let nm = _N ++ "N"
  in sDef nm (SQuotes _N) sString

elabEnum :: String -> [String] -> SDecl
elabEnum _N _E = let
  nm = _N ++ "E"
  _E' = foldr (sCons . SQuotes) sNil _E
  in sDef nm _E' sEnum

----------------------------------------------------------------------

elab :: Syntax -> SpireM Check
elab s = flip runReaderT [] . elabC $ s

type SpireM' = ReaderT [Nom] SpireM

elabC :: Syntax -> SpireM' Check

elabC SRefl          = return CRefl
elabC SHere          = return CHere
elabC (SThere t)     = CThere <$> elabC  t
elabC (SEnd   i)     = CEnd   <$> elabC  i
elabC (SRec   i  _D) = CRec   <$> elabC  i  <*> elabC  _D
elabC (SInit  xs)    = CInit  <$> elabC  xs
elabC (SArg   _A _B) = CArg   <$> elabC  _A <*> elabBC _B
elabC (SPair  a b)   = CPair  <$> elabC  a  <*> elabC  b
elabC (SLam   b)     = CLam   <$> elabBC b

elabC x@(SQuotes _)         = elabIC x
elabC x@(SPi _ _)           = elabIC x
elabC x@(SSg _ _)           = elabIC x
elabC x@(SEq _ _)           = elabIC x
elabC x@(SVar _)            = elabIC x
elabC x@(SIf _ _ _)         = elabIC x
elabC x@(SApp _ _)          = elabIC x
elabC x@(SAnn _ _)          = elabIC x
elabC x@(SWildCard)         = elabIC x

----------------------------------------------------------------------

elabI :: Syntax -> SpireM' Infer

elabI (SQuotes s) = return $ IQuotes s
elabI (SVar nm)   = return $ IVar nm

elabI SWildCard = return $ IVar (s2n wildcard)

elabI (SApp f a)    = IApp   <$> elabI f <*> elabC a
elabI (SIf b ct cf) = IIf    <$> elabC b <*> elabI ct <*> elabI cf
elabI (SAnn a _A)   = IAnn   <$> elabC a <*> elabC _A

elabI (SPi _A _B)       = IPi       <$> elabC _A <*> elabBC _B
elabI (SSg _A _B)       = ISg       <$> elabC _A <*> elabBC _B
elabI (SEq a b)         = IEq       <$> elabI a  <*> elabI b

-- once we have meta variables, we should always be able to infer a type for 
-- a lambda, by inserting a meta variable to type the domain of the lambda,
-- but a pair will still fail because any inferred type for the RHS
-- is a specialized version of a more general type (in which a universal variable
-- standing for the LHS is free).
elabI x@SRefl       = failUnannotated x
elabI x@SHere       = failUnannotated x
elabI x@(SThere _)  = failUnannotated x
elabI x@(SEnd   _)  = failUnannotated x
elabI x@(SRec  _ _) = failUnannotated x
elabI x@(SInit _)   = failUnannotated x
elabI x@(SArg  _ _) = failUnannotated x
elabI x@(SPair _ _) = failUnannotated x
elabI x@(SLam _)    = failUnannotated x

----------------------------------------------------------------------

elabBC :: Bind Nom Syntax -> SpireM' (Bind Nom Check)
elabBC bnd = do
  (nm , a) <- unbind bnd
  -- Store names in binding order.
  a'       <- local (++ [nm]) $ elabC a
  return   $  bind nm a'

elabBC3 :: Bind Nom3 Syntax -> SpireM' (Bind Nom3 Check)
elabBC3 bnd = do
  ((nm1 , nm2 , nm3) , a) <- unbind bnd
  -- Store names in binding order.
  a'       <- local (++ [nm1 , nm2 , nm3]) $ elabC a
  return   $  bind (nm1 , nm2 , nm3) a'

failUnannotated :: Syntax -> SpireM' Infer
failUnannotated a = throwError $
  "Failed to infer the type of this term, please annotate it:\n" ++
  show a

elabIC :: Syntax -> SpireM' Check
elabIC x = Infer <$> elabI x

----------------------------------------------------------------------
