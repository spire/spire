module Spire.Surface.Elaborator (elabProg) where
import Control.Monad.Error
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
elabProg (SDef nm a _A : xs) = do
  (_A' , _A'vs) <- elab _A
  (a' , a'vs)   <- elab a
  xs'           <- elabProg xs
  return (CDef nm a' a'vs _A' _A'vs : xs')

----------------------------------------------------------------------

elab :: Syntax -> SpireM (Check , MVarDecls)
elab s = runWriterT . flip runReaderT [] . elabC $ s

type SpireM' = ReaderT [Nom] (WriterT MVarDecls SpireM)

elabC :: Syntax -> SpireM' Check

elabC (SPair a b) = CPair <$> elabC  a <*> elabC b
elabC (SLam b)    = CLam  <$> elabBC b

elabC x@STT         = elabIC x
elabC x@STrue       = elabIC x
elabC x@SFalse      = elabIC x
elabC x@SUnit       = elabIC x
elabC x@SBool       = elabIC x
elabC x@SType       = elabIC x
elabC x@(SPi _ _)   = elabIC x
elabC x@(SSg _ _)   = elabIC x
elabC x@(SVar _)    = elabIC x
elabC x@(SProj1 _)  = elabIC x
elabC x@(SProj2 _)  = elabIC x
elabC x@(SIf _ _ _) = elabIC x
elabC x@(SApp _ _)  = elabIC x
elabC x@(SAnn _ _)  = elabIC x
elabC x@(SWildCard) = elabIC x
elabC x@(SCaseBool _ _ _ _) = elabIC x

----------------------------------------------------------------------

elabI :: Syntax -> SpireM' Infer

elabI STT       = return ITT
elabI STrue     = return ITrue
elabI SFalse    = return IFalse
elabI SUnit     = return IUnit
elabI SBool     = return IBool
elabI SType     = return IType
elabI (SVar nm) = return $ IVar nm

elabI SWildCard = do
  w <- fresh $ s2n "WILD"
  wT <- fresh $ s2n "WILD_T"
  -- I believe the order here is irrelevant, at least for Gundry ...
  tell [(wT , VType) , (w , vVar wT)]
  vs <- ask
  return $ cApps w vs
  where
  cApps w vs = foldl IApp (IVar w) args
    where
    args = map (Infer . IVar) $ vs

elabI (SProj1 ab)   = IProj1 <$> elabI ab
elabI (SProj2 ab)   = IProj2 <$> elabI ab
elabI (SApp f a)    = IApp   <$> elabI f <*> elabC a
elabI (SIf b ct cf) = IIf    <$> elabC b <*> elabI ct <*> elabI cf
elabI (SAnn a _A)   = IAnn   <$> elabC a <*> elabC _A

elabI (SCaseBool _P ct cf b) =
  ICaseBool <$> elabBC _P <*> elabC ct <*> elabC cf <*> elabC b

elabI (SPi _A _B) = IPi <$> elabC _A <*> elabBC _B
elabI (SSg _A _B) = ISg <$> elabC _A <*> elabBC _B

-- Once we have meta variables, we should always be able to infer a type for 
-- a lambda, by inserting a meta variable to type the domain of the lambda,
-- but a pair will still fail because any inferred type for the RHS
-- is a specialized version of a more general type (in which a universal variable
-- standing for the LHS is free).
elabI x@(SPair _ _) = failUnannotated x
elabI x@(SLam _)    = failUnannotated x

----------------------------------------------------------------------

elabBC :: Bind Nom Syntax -> SpireM' (Bind Nom Check)
elabBC bnd = do
  (nm , a) <- unbind bnd
  -- Store names in binding order.
  a'       <- local (++ [nm]) $ elabC a
  return   $  bind nm a'

failUnannotated :: Syntax -> SpireM' Infer
failUnannotated a = throwError $
  "Failed to infer the type of this term, please annotate it:\n" ++
  show a

elabIC :: Syntax -> SpireM' Check
elabIC x = Infer <$> elabI x

----------------------------------------------------------------------
