{-# LANGUAGE MultiParamTypeClasses , FlexibleInstances #-}

module Spire.Canonical.Evaluator where
import Unbound.LocallyNameless hiding ( Subst , subst, substs )
import Spire.Unbound.Subst
import Spire.Canonical.Types
import Control.Monad.Error

----------------------------------------------------------------------

type EvalM = FreshM

($$) :: Bind Nom Value -> Value -> EvalM Value
($$) b x = do
  (nm , f) <- unbind b
  subst nm x f

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

instance Subst EvalM Value Elim

instance Subst EvalM Value Value where
  isVar (VElim nm fs) = Just $ SubstCoerce nm (\x -> Just (elims x fs))
  isVar _ = Nothing

----------------------------------------------------------------------