{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , ViewPatterns
  #-}

module Spire.Expression.Checker where
import Unbound.LocallyNameless
import Control.Monad.Error
import Spire.Unbound.SubstM
import Spire.Canonical.Types
import Spire.Expression.Types
import Data.Functor.Identity

----------------------------------------------------------------------

type CheckM = ErrorT String FreshM

lookUp :: Nom -> Tel -> CheckM (Value , Type)
lookUp nm Empty = throwError $
  "Variable not in context:\n" ++ show nm
lookUp nm (Extend (unrebind -> ((x , Embed _A) , xs))) =
  if nm == x
  then let a = VElim nm [] in return (a , _A)
  else lookUp nm xs

----------------------------------------------------------------------

check :: Tel -> Check -> Type -> CheckM Value

check ctx (CPair a b) (VSg _A _B) = undefined

check ctx (CPair a b) _ = throwError "Ill-typed!"

check ctx (Infer a) _B = do
  (a' , _A) <- infer ctx a
  unless (aeq _A _B) $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ show _B ++
    "\n\nInferred type:\n" ++ show _A ++
    "\n\nContext:\n" ++ show ctx ++
    "\n\nUnevaluated value:\n" ++ show a
  return a'

check ctx a _A = undefined

infer :: Tel -> Infer -> CheckM (Value , Type)
infer ctx ITT   = return (VTT , VUnit)
infer ctx IType = return (VType , VType)

infer ctx (ISg _A _B) = do
  _A' <- check ctx _A VType
  _B' <- checkExtend ctx _A' _B VType
  return (VSg _A' _B' , VType)

infer ctx (IVar nm) = lookUp nm ctx

infer ctx (IAnn a _A) = do
  _A' <- check ctx _A VType
  a' <- check ctx a _A'
  return (a' , _A')

infer ctx i = undefined

----------------------------------------------------------------------

checkExtend :: Tel -> Type -> Bind Nom Check -> Type -> CheckM (Bind Nom Value)
checkExtend ctx _A bd _B = do
  (x , b) <- unbind bd
  b' <- check (snocTel ctx (x , Embed _A)) b _B
  return $ bind x b'


----------------------------------------------------------------------
