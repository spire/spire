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

lookUp :: Nom -> Tel -> CheckM Type
lookUp nm Empty = throwError $ "Not in context: " ++ show nm
lookUp nm (Extend (unrebind -> ((x , Embed _A) , xs))) =
  if nm == x
  then return _A
  else lookUp nm xs

----------------------------------------------------------------------

check :: Tel -> Check -> Type -> CheckM Value
check = undefined

infer :: Tel -> Infer -> CheckM (Value , Type)
infer ctx ITT   = return (VTT , VUnit)
infer ctx IType = return (VType , VType)

infer ctx (ISg _A _B) = do
  _A' <- check ctx _A VType
  _B' <- checkExtend ctx _A' _B VType
  return (VSg _A' _B' , VType)
infer ctx (IPi _A _B) = do
  _A' <- check ctx _A VType
  _B' <- checkExtend ctx _A' _B VType
  return (VPi _A' _B' , VType)

infer ctx i = undefined

----------------------------------------------------------------------

checkExtend :: Tel -> Type -> Bind Nom Check -> Type -> CheckM (Bind Nom Value)
checkExtend ctx _A bd _B = do
  (x , b) <- unbind bd
  b' <- check (snocTel ctx (x , Embed _A)) b _B
  return $ bind x b'


----------------------------------------------------------------------
