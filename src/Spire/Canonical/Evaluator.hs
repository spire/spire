{-# LANGUAGE MultiParamTypeClasses
           , FlexibleInstances
           , ViewPatterns
           , TupleSections
           #-}

module Spire.Canonical.Evaluator (lookupValAndType , lookupType , sub , elim) where
import PatternUnify.Context
import Unbound.LocallyNameless hiding ( Spine )
import Spire.Unbound.SubstM
import Spire.Canonical.Types
import Spire.Canonical.Unification
import Spire.Surface.PrettyPrinter
import Control.Applicative ((<$>))
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

----------------------------------------------------------------------

instance SubstM SpireM Value Spine
instance SubstM SpireM Value Elim
instance SubstM SpireM Value Value where
  substHookM (VNeut nm fs) = Just f
    where
    f nm' e = do
      fs' <- substM nm' e fs
      let head = if nm == nm' then e else vVar nm
      elims head fs'
  substHookM _ = Nothing

----------------------------------------------------------------------

sub :: Bind Nom Value -> Value -> SpireM Value
sub b x = do
  (nm , f) <- unbind b
  substM nm x f

elim :: Value -> Elim -> SpireM Value
elim (VNeut nm fs) f        = return $ VNeut nm (Pipe fs f)
elim (VLam f)      (EApp a) = f `sub` a
elim _             (EApp _) = throwError "Ill-typed evaluation of ($)"
elim (VPair a _)   EProj1   = return a
elim _             EProj1   = throwError "Ill-typed evaluation of proj1"
elim (VPair _ b)   EProj2   = return b
elim _             EProj2   = throwError "Ill-typed evaluation of proj2"

elim VTrue  (ECaseBool _P ct _) = return ct
elim VFalse (ECaseBool _P _ cf) = return cf
elim _      (ECaseBool _P _  _) = throwError "Ill-typed evaluation of if"

elims :: Value -> Spine -> SpireM Value
elims x Id = return x
elims x (Pipe fs f) = do
  x' <- elims x fs
  elim x' f

----------------------------------------------------------------------
-- Exported lookup functions.

lookupValAndType :: Nom -> SpireM (Value , Type)
lookupValAndType nm = do
  ctx <- asks ctx
  lookupCtx nm ctx

lookupType :: Nom -> SpireM Type
lookupType nm = snd <$> lookupValAndType nm

----------------------------------------------------------------------
-- Non-exported lookup functions.

lookupCtx :: Nom -> Tel -> SpireM (Value , Type)
lookupCtx nm (Extend (unrebind -> ((x , Embed _A) , xs))) =
  if nm == x
  then return (vVar nm , _A)
  else lookupCtx nm xs
lookupCtx nm Empty = do
  env <- asks env
  lookupEnv nm env

lookupEnv :: Nom -> Env -> SpireM (Value , Type)
lookupEnv nm (VDef x a _A : xs) =
  if nm == x
  then return (a , _A)
  else lookupEnv nm xs
lookupEnv nm [] = do
  uCtx <- gets unifierCtx
  lookupMV nm uCtx

lookupMV :: Nom -> UnifierCtx -> SpireM (Value , Type)
lookupMV nm (E x (_T , _) : es) =
  if nm == (translate x)
  then (vVar nm , ) <$> tm2Value _T
  else lookupMV nm es
lookupMV nm (Q _ _ : es) = lookupMV nm es
lookupMV nm [] = do
  env <- asks env
  ctx <- asks ctx
  uCtx <- gets unifierCtx
  throwError $
    "Variable not in context, environment, or unifier context!\n" ++
    "Referenced variable:\n" ++ prettyPrintError nm ++ "\n" ++
    "\nCurrent context:\n" ++ prettyPrintError ctx ++ "\n" ++
    "\nCurrent environment:\n" ++ prettyPrintError env ++ "\n" ++
    "\nCurrent unifier context:\n" ++ prettyPrintError uCtx

----------------------------------------------------------------------
