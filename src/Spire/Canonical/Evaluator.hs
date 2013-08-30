{-# LANGUAGE MultiParamTypeClasses
  , FlexibleInstances
  , ViewPatterns
  , FlexibleContexts #-}

module Spire.Canonical.Evaluator where
import Unbound.LocallyNameless hiding ( Spine )
import Spire.Unbound.SubstM
import Spire.Canonical.Types
import Control.Monad.Error
import Control.Monad.Reader

----------------------------------------------------------------------

instance SubstM SpireM Value Spine
instance SubstM SpireM Value Elim
instance SubstM SpireM Value Value where
  isVarM (VNeut nm fs) = Just $ SubstCoerceM nm (\x -> Just (elims x fs))
  isVarM _ = Nothing
instance (Alpha a, SubstM SpireM Value a) => SubstM SpireM Value (BindMeta a)

----------------------------------------------------------------------

sub :: Bind Nom Value -> Value -> SpireM Value
sub b x = do
  (nm , f) <- unbind b
  substM nm x f

elim :: Value -> Elim -> SpireM Value
elim (VNeut nm fs) f        = return $ VNeut nm (Pipe fs f)
elim (VLam f)      (EApp a) = f `sub` a
elim _             (EApp a) = throwError "Ill-typed evaluation of ($)"
elim (VPair a b)   EProj1   = return a
elim _             EProj1   = throwError "Ill-typed evaluation of proj1"
elim (VPair a b)   EProj2   = return b
elim _             EProj2   = throwError "Ill-typed evaluation of proj2"

elim VTrue  (ECaseBool _P ct cf) = return ct
elim VFalse (ECaseBool _P ct cf) = return cf
elim _      (ECaseBool _P ct cf) = throwError "Ill-typed evaluation of if"

elims :: Value -> Spine -> SpireM Value
elims x Id = return x
elims x (Pipe fs f) = do
  x' <- elims x fs
  elim x' f

----------------------------------------------------------------------

lookupCtx :: Nom -> Tel -> SpireM (Value , Type)
lookupCtx nm (Extend (unrebind -> ((x , Embed _A) , xs))) =
  if nm == x
  then return (vVar nm , _A)
  else lookupCtx nm xs
lookupCtx nm Empty = do
  env <- asks env
  lookupEnv nm env

----------------------------------------------------------------------

lookupEnv :: Nom -> Env -> SpireM (Value , Type)
lookupEnv nm (VDef x a _A : xs) =
  if nm == x
  then return (a , _A)
  else lookupEnv nm xs
lookupEnv nm [] = do
  env <- asks env
  ctx <- asks ctx
  throwError $
    "Variable not in context or environment!\n" ++
    "Referenced variable:\n" ++ show nm ++
    "\nCurrent context:\n" ++ show ctx ++
    "\nCurrent environment:\n" ++ show env

----------------------------------------------------------------------