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

checkV (VDesc _I) VType = checkV _I VType
checkV (VDesc _I) _     = throwError "Ill-typed!"

checkV (VTag _E) VType = checkV _E vEnum
checkV (VTag _E) _     = throwError "Ill-typed!"

checkV VHere (VTag (VCons l _E)) = return ()
checkV VHere _ = throwError "Ill-typed!"

checkV (VThere t) (VTag (VCons l _E)) = checkV t (VTag _E)
checkV (VThere _) _ = throwError "Ill-typed!"

checkV (VEq _A a _B b) VType = do
  checkV _A VType
  checkV a _A
  checkV _B VType
  checkV b _B
checkV (VEq _ _ _ _) _ =
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

checkV (VFix _I _E _Ds i) VType = do
  checkV _I VType
  checkV _E vEnum
  checkV _Ds =<< _E `elim` eBranchesD _I
  checkV i _I
checkV (VFix _I _E _Ds i) _ =
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

checkV VRefl (VEq _A a _B b) = do
  unless (_A == _B) $
    throwError "Ill-typed!"
  unless (a == b) $
    throwError "Ill-typed!"
checkV VRefl _ =
  throwError "Ill-typed!"

checkV (VEnd i) (VDesc _I) = do
  checkV i _I
checkV (VEnd i) _ =
  throwError "Ill-typed!"

checkV (VRec i _D) (VDesc _I) = do
  checkV i _I
  checkV _D (VDesc _I)
checkV (VRec i _D) _ =
  throwError "Ill-typed!"

checkV (VArg _A _B) (VDesc _I) = do
  checkV _A VType
  checkVExtend _A _B (VDesc _I)
checkV (VArg _A _B) _ =
  throwError "Ill-typed!"

checkV (VInit t xs) (VFix _I _E _Ds i) = do
  checkV t (VTag _E)
  _D <- t `elim` eCaseD _I _E _Ds
  let _X = vBind (\j -> VFix _I _E _Ds j)
  checkV xs =<< _D `elim` EEl _I _X i
checkV (VInit t xs) _ =
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

inferN nm (Pipe fs (ESubst _A _P x y px)) = do
  checkV _A VType
  checkVExtend _A _P VType
  checkV x _A
  checkV y _A
  let q = VNeut nm fs
  checkV q (VEq _A x _A y)
  checkV px =<< _P `sub` x
  _P `sub` y

inferN nm (Pipe fs (EBranches _P)) = do
  let _E = VNeut nm fs
  checkV _E vEnum
  checkVExtend (VTag _E) _P VType
  return VType

inferN nm (Pipe fs (EEl _I _X i)) = do
  checkV _I VType
  let _D = VNeut nm fs
  checkV _D (VDesc _I)
  checkVExtend _I _X VType
  checkV i _I
  return VType

inferN nm (Pipe fs (ECase _E _P cs)) = do
  checkV _E vEnum
  checkVExtend (VTag _E) _P VType
  checkV cs =<< _E `elim` EBranches _P
  let t = VNeut nm fs
  checkV t (VTag _E)
  _P `sub` t

----------------------------------------------------------------------

checkVExtend :: Type -> Bind Nom Value -> Type -> SpireM ()
checkVExtend _A bnd_b _B = do
  (x , b) <- unbind bnd_b
  extendCtx x _A $ checkV b _B

----------------------------------------------------------------------