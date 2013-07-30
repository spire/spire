{-# LANGUAGE MultiParamTypeClasses , FlexibleInstances #-}

module Spire.Canonical.Evaluator where
import Unbound.LocallyNameless
import Spire.Unbound.SubstM
import Spire.Canonical.Types
import Control.Monad.Error

----------------------------------------------------------------------

snoc :: [a] -> a -> [a]
snoc xs x = xs ++ [x]

----------------------------------------------------------------------

($$) :: Bind Nom Value -> Value -> ContextM Value
($$) b x = do
  (nm , f) <- unbind b
  substM nm x f

elim :: Value -> Elim -> ContextM Value
elim (Elim nm fs) e         = return $ Elim nm $ snoc fs e
elim (VLam _A f)    (EApp a) = f $$ a
elim _              (EApp a) = throwError "Ill-typed evaluation of ($)"
elim (VPair a b _B) EProj1   = return a
elim _              EProj1   = throwError "Ill-typed evaluation of proj1"
elim (VPair a b _B) EProj2   = return b
elim _              EProj2   = throwError "Ill-typed evaluation of proj2"

elims :: Value -> [Elim] -> ContextM Value
elims = foldM elim

instance SubstM ContextM Value Elim
instance SubstM ContextM Value Value where
  isVarM (Elim nm fs) = Just $ SubstCoerceM nm (\x -> Just (elims x fs))
  isVarM _ = Nothing

----------------------------------------------------------------------