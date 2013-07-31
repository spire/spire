{-# LANGUAGE MultiParamTypeClasses , FlexibleInstances #-}

module Spire.Canonical.Evaluator where
import Unbound.LocallyNameless
import Spire.Unbound.SubstM
import Spire.Canonical.Types
import Control.Monad.Error

----------------------------------------------------------------------

instance SubstM SpireM Value Elim
instance SubstM SpireM Value Value where
  isVarM (Elim nm fs) = Just $ SubstCoerceM nm (\x -> Just (elims x fs))
  isVarM _ = Nothing

----------------------------------------------------------------------

snoc :: [a] -> a -> [a]
snoc xs x = xs ++ [x]

----------------------------------------------------------------------

($$) :: Bind Nom Value -> Value -> SpireM Value
($$) b x = do
  (nm , f) <- unbind b
  substM nm x f

elim :: Value -> Elim -> SpireM Value
elim (Elim nm fs)   e           = return $ Elim nm $ snoc fs e
elim (VLam _A f)    (EApp a)    = f $$ a
elim _              (EApp a)    = return $ error "Ill-typed evaluation of ($)"
elim (VPair a b _B) EProj1      = return a
elim _              EProj1      = return $ error "Ill-typed evaluation of proj1"
elim (VPair a b _B) EProj2      = return b
elim _              EProj2      = return $ error "Ill-typed evaluation of proj2"
elim VTrue          (EIf ct cf) = return ct
elim VFalse         (EIf ct cf) = return cf
elim _              (EIf ct cf) = return $ error "Ill-typed evaluation of if"

elims :: Value -> [Elim] -> SpireM Value
elims = foldM elim

----------------------------------------------------------------------
