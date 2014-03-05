{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  #-}

module Spire.Canonical.Checker where
import Control.Monad.Error
import Unbound.LocallyNameless hiding ( Spine )
import Spire.Canonical.Types
import Spire.Canonical.Evaluator

----------------------------------------------------------------------

recheckProg :: VProg -> SpireM ()
recheckProg [] = return ()
recheckProg (VDef _ a _A : xs) = do
  checkV _A VType
  checkV a _A
  recheckProg xs
  return ()

----------------------------------------------------------------------

checkV :: Value -> Type -> SpireM ()
checkV VTT    VUnit        = return ()
checkV VTT    _            = throwError "Ill-typed!"
checkV VTrue  VBool        = return ()
checkV VTrue  _            = throwError "Ill-typed!"
checkV VFalse VBool        = return ()
checkV VFalse _            = throwError "Ill-typed!"
checkV (VQuotes _) VString = return ()
checkV (VQuotes _) _       = throwError "Ill-typed!"
checkV VNil   (VList _)    = return ()
checkV VNil   _            = throwError "Ill-typed!"

checkV VUnit   VType = return ()
checkV VUnit   _     = throwError "Ill-typed!"
checkV VBool   VType = return ()
checkV VBool   _     = throwError "Ill-typed!"
checkV VString VType = return ()
checkV VString _     = throwError "Ill-typed!"
checkV VType   VType = return ()
checkV VType   _     = throwError "Ill-typed!"

checkV (VList _A) VType = checkV _A VType
checkV (VList _A) _     = throwError "Ill-typed!"

checkV (VSg _A _B) VType = do
  checkV _A VType
  checkVExtend _A _B VType
checkV (VSg _A _B) _ =
  throwError "Ill-typed!"

checkV (VPi _A _B) VType = do
  checkV _A VType
  checkVExtend _A _B VType
checkV (VPi _A _B) _ =
  throwError "Ill-typed!"

checkV (VCons a as) (VList _A) = do
  checkV a _A
  checkV as (VList _A)
checkV (VCons a as) _ =
  throwError "Ill-typed!"

checkV (VLam bnd_b) (VPi _A bnd_B) = do
  (nm_a , b) <- unbind bnd_b
  _B         <- bnd_B `sub` vVar nm_a
  extendCtx nm_a _A $ checkV b _B

checkV (VLam _) _ =
  throwError "Ill-typed!"

checkV (VPair a b) (VSg _A _B) = do
  checkV a _A
  checkV b =<< _B `sub` a
checkV (VPair _ _) _ =
  throwError "Ill-typed!"

checkV (VNeut nm fs) _B = do
  _B' <- inferN nm fs
  unless (_B == _B') $
    throwError "Ill-typed!"

----------------------------------------------------------------------

inferN :: Nom -> Spine -> SpireM Type
inferN nm Id = lookupType nm

inferN nm (Pipe fs (EApp a)) = do
  _AB <- inferN nm fs
  case _AB of
    VPi _A _B -> do
      checkV a _A
      _B `sub` a
    _         -> throwError "Ill-typed!"

inferN nm (Pipe fs EProj1) = do
  _AB <- inferN nm fs
  case _AB of
    VSg _A _B -> return _A
    _         -> throwError "Ill-typed!"

inferN nm (Pipe fs EProj2) = do
  _AB <- inferN nm fs
  case _AB of
    VSg _A _B -> _B `sub` VNeut nm (Pipe fs EProj1)
    _         -> throwError "Ill-typed!"

inferN nm (Pipe fs (EElimBool _P ptrue pfalse)) = do
  checkVExtend VBool _P VType
  checkV ptrue  =<< _P `sub` VTrue
  checkV pfalse =<< _P `sub` VFalse
  let b = VNeut nm fs
  checkV b VBool
  _P `sub` b

inferN nm (Pipe fs (EElimList _A _P pnil pcons)) = do
  checkV _A VType
  checkVExtend (VList _A) _P VType
  checkV pnil =<< _P `sub` VNil
  checkVPCons _A _P pcons
  let as = VNeut nm fs
  checkV as (VList _A)
  _P `sub` as where

  checkVPCons :: Type -> Bind Nom Type -> Bind (Nom , Nom , Nom) Value -> SpireM ()
  checkVPCons _A bnd_P bnd_pcons = do
    ((nm_a , nm_as , nm_pas) , pcons) <- unbind bnd_pcons
    _Pas   <- bnd_P `sub` vVar nm_as
    _Pcons <- bnd_P `sub` VCons (vVar nm_a) (vVar nm_as)
    extendCtx nm_a _A $ extendCtx nm_as (VList _A) $ extendCtx nm_pas _Pas $ checkV pcons _Pcons

----------------------------------------------------------------------

checkVExtend :: Type -> Bind Nom Value -> Type -> SpireM ()
checkVExtend _A bnd_b _B = do
  (x , b) <- unbind bnd_b
  extendCtx x _A $ checkV b _B

----------------------------------------------------------------------