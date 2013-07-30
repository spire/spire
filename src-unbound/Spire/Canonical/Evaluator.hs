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

type EvalM = FreshM

($$) :: Bind Nom Value -> Value -> EvalM Value
($$) b x = do
  (nm , f) <- unbind b
  substM nm x f

elim :: Value -> Elim -> EvalM Value
elim (VElim nm fs) e         = return $ VElim nm $ snoc fs e
elim (VLam _A b)    (EApp x) = b $$ x
elim _              (EApp x) = error "Ill-typed evaluation of ($)"
elim (VPair a b _B) EProj1   = return a
elim _              EProj1   = error "Ill-typed evaluation of proj1"
elim (VPair a b _B) EProj2   = return b
elim _              EProj2   = error "Ill-typed evaluation of proj2"

elims :: Value -> [Elim] -> EvalM Value
elims = foldM elim

instance SubstM EvalM Value Elim

instance SubstM EvalM Value Value where
  isVarM (VElim nm fs) = Just $ SubstCoerceM nm (\x -> Just (elims x fs))
  isVarM _ = Nothing

----------------------------------------------------------------------