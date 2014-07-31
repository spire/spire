module Spire.Surface.Elaborator (elabProg) where
import Control.Monad.Error
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Applicative
import Unbound.LocallyNameless
import Spire.Canonical.Types
import Spire.Canonical.Unification
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
elabC x@(SEl _ _ _)         = elabIC x
elabC x@(SFix _ _)          = elabIC x
elabC x@(SEq _ _)           = elabIC x
elabC x@(SVar _)            = elabIC x
elabC x@(SProj1 _)          = elabIC x
elabC x@(SProj2 _)          = elabIC x
elabC x@(SIf _ _ _)         = elabIC x
elabC x@(SApp _ _)          = elabIC x
elabC x@(SAnn _ _)          = elabIC x
elabC x@(SWildCard)         = elabIC x
elabC x@(SSubst _ _ _)      = elabIC x

----------------------------------------------------------------------

elabI :: Syntax -> SpireM' Infer

elabI (SQuotes s) = return $ IQuotes s
elabI (SVar nm)   = return $ IVar nm

elabI SWildCard = do
  -- Hack: get fresh integer from 'Fresh' monad.
  n <- name2Integer <$> fresh (s2n "" :: Name ())
  w <- freshMV $ "w" ++ show n
  -- We don't run the declaration yet, because we want the mvars to be
  -- scoped to the current definition.
  tell . MkMVarDecls $ [declareMV w]
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

elabI (SSubst _P q p) =
  ISubst <$> elabBC _P <*> elabI q <*> elabC p

elabI (SPi _A _B)       = IPi       <$> elabC _A <*> elabBC _B
elabI (SSg _A _B)       = ISg       <$> elabC _A <*> elabBC _B
elabI (SEq a b)         = IEq       <$> elabI a  <*> elabI b
elabI (SEl  _D _X i)    = IEl       <$> elabI _D <*> elabBC _X  <*> elabC i
elabI (SFix _D i)       = IFix      <$> elabC _D <*> elabI i

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
