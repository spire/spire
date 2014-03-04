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
checkV VTT    VUnit = return ()
checkV VTT    _     = throwError "Ill-typed!"
checkV VTrue  VBool = return ()
checkV VTrue  _     = throwError "Ill-typed!"
checkV VFalse VBool = return ()
checkV VFalse _     = throwError "Ill-typed!"
checkV VZero VNat   = return ()
checkV VZero _      = throwError "Ill-typed!"

checkV VUnit  VType = return ()
checkV VUnit  _     = throwError "Ill-typed!"
checkV VBool  VType = return ()
checkV VBool  _     = throwError "Ill-typed!"
checkV VNat   VType = return ()
checkV VNat   _     = throwError "Ill-typed!"
checkV VType  VType = return ()
checkV VType  _     = throwError "Ill-typed!"

checkV (VSuc n) VNat = do
  checkV n VNat
checkV (VSuc n) _ =
  throwError "Ill-typed!"

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

inferN nm (Pipe fs (EElimBool _P ct cf)) = do
  checkVExtend VBool _P VType
  checkV ct =<< _P `sub` VTrue
  checkV cf =<< _P `sub` VFalse
  let b = VNeut nm fs
  checkV b VBool
  _P `sub` b

inferN nm (Pipe fs (EElimNat _P cz cs)) = do
  checkVExtend VNat _P VType
  checkV cz =<< _P `sub` VZero
  checkVPSuc _P cs
  let n = VNeut nm fs
  checkV n VNat
  _P `sub` n where

  checkVPSuc :: Bind Nom Type -> Bind (Nom , Nom) Value -> SpireM ()
  checkVPSuc bnd_P bnd_ps = do
    ((nm_n , nm_pn) , ps) <- unbind bnd_ps
    _Pn    <- bnd_P `sub` vVar nm_n
    _Psucn <- bnd_P `sub` VSuc (vVar nm_n)
    extendCtx nm_n VNat $ extendCtx nm_pn _Pn $ checkV ps _Psucn

----------------------------------------------------------------------

checkVExtend :: Type -> Bind Nom Value -> Type -> SpireM ()
checkVExtend _A bnd_b _B = do
  (x , b) <- unbind bnd_b
  extendCtx x _A $ checkV b _B

----------------------------------------------------------------------