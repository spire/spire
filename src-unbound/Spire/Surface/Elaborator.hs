{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  #-}

module Spire.Surface.Elaborator where
import Control.Monad.Error
import Control.Applicative
import Unbound.LocallyNameless
import Spire.Canonical.Types
import Spire.Surface.Types
import Spire.Expression.Types

----------------------------------------------------------------------

elabC :: Syntax -> SpireM Check

elabC (SPair a b) = CPair <$> elabC a <*> elabC b
elabC (SLam b)    = CLam <$> elabBC b

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

----------------------------------------------------------------------

elabI :: Syntax -> SpireM Infer

elabI STT       = return ITT
elabI STrue     = return ITrue
elabI SFalse    = return IFalse
elabI SUnit     = return IUnit
elabI SBool     = return IBool
elabI SType     = return IType
elabI (SVar nm) = return $ IVar nm

elabI (SProj1 ab)   = IProj1 <$> elabI ab
elabI (SProj2 ab)   = IProj2 <$> elabI ab
elabI (SApp f a)    = IApp <$> elabI f <*> elabC a
elabI (SIf b ct cf) = IIf <$> elabC b <*> elabI ct <*> elabI cf
elabI (SAnn a _A)   = IAnn <$> elabC a <*> elabC _A

elabI (SPi _A _B) = IPi <$> elabC _A <*> elabBC _B
elabI (SSg _A _B) = IPi <$> elabC _A <*> elabBC _B

elabI x@(SPair _ _) = failUnannotated x
elabI x@(SLam _)    = failUnannotated x

----------------------------------------------------------------------

elabBC :: Bind Nom Syntax -> SpireM (Bind Nom Check)
elabBC bnd = do
  (nm , a) <- unbind bnd
  a'       <- elabC a
  return   $  bind nm a'

failUnannotated :: Syntax -> SpireM Infer
failUnannotated a = throwError $
  "Failed to infer the type of this term, please annotate it:\n" ++
  show a

elabIC :: Syntax -> SpireM Check
elabIC x = Infer <$> elabI x

----------------------------------------------------------------------
