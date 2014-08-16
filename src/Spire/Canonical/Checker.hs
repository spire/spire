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
import Spire.Surface.PrettyPrinter
import Spire.Canonical.InitialEnv

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
checkV VNil   VEnum        = return ()
checkV VNil   _            = throwError "Ill-typed!"

checkV VUnit   VType = return ()
checkV VUnit   _     = throwError "Ill-typed!"
checkV VBool   VType = return ()
checkV VBool   _     = throwError "Ill-typed!"
checkV VString VType = return ()
checkV VString _     = throwError "Ill-typed!"
checkV VEnum   VType = return ()
checkV VEnum   _     = throwError "Ill-typed!"
checkV VTel    VType = return ()
checkV VTel    _     = throwError "Ill-typed!"
checkV VType   VType = return ()
checkV VType   _     = throwError "Ill-typed!"

checkV (VDesc _I) VType = checkV _I VType
checkV (VDesc _I) _     = throwError "Ill-typed!"

checkV (VTag _E) VType = checkV _E VEnum
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

checkV (VFix l _P _I _D p i) VType = do
  checkV l VString
  checkV _P VType
  checkV _I VType
  checkV _D $ VDesc _I
  checkV p _P
  checkV i _I
checkV (VFix l _P _I _D p i) _ =
  throwError "Ill-typed!"

checkV (VCons x xs) VEnum = do
  checkV x VString
  checkV xs VEnum
checkV (VCons x xs) _ =
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

checkV VEmp VTel = return ()
checkV VEmp _    = throwError "Ill-typed!"

checkV (VExt _A _B) VTel = do
  checkV _A VType
  checkVExtend _A _B VTel
checkV (VExt _A _B) _ =
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

checkV (VInit xs) (VFix l _P _I _D p i) = do
  let _X = vBind "i" (\j -> VFix l _P _I _D p j)
  checkV xs =<< _D `elim` EFunc _I _X i
checkV (VInit xs) _ =
  throwError "Ill-typed!"

checkV x@(VNeut nm fs) _A = do
  _A' <- inferN nm fs
  unless (_A == _A') $
    throwError $ "Ill-typed, checked type not equal to inferred type!\n\n" ++
    "Checked type:\n" ++ prettyPrint _A ++
    "\nInferred type:\n" ++ prettyPrint _A' ++
    "\nValue:\n" ++ prettyPrint x

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

inferN nm (Pipe fs (EElimUnit _P ptt)) = do
  checkVExtend VUnit _P VType
  let u = VNeut nm fs
  checkV u VUnit
  _P `sub` u

inferN nm (Pipe fs (EElimBool _P ptrue pfalse)) = do
  checkVExtend VBool _P VType
  checkV ptrue  =<< _P `sub` VTrue
  checkV pfalse =<< _P `sub` VFalse
  let b = VNeut nm fs
  checkV b VBool
  _P `sub` b

inferN nm (Pipe fs (EElimPair _A _B _P ppair)) = do
  checkV _A VType       
  checkVExtend _A _B VType
  checkVExtend (VSg _A _B) _P VType
  checkVppair _A _B _P ppair
  let ab = VNeut nm fs
  checkV ab (VSg _A _B)
  _P `sub` ab
  where

  checkVppair :: Type -> Bind Nom Type -> Bind Nom Type -> Bind Nom2 Value -> SpireM ()
  checkVppair _A _B _P bnd_ppair = do
    ((a , b) , ppair) <- unbind bnd_ppair
    _Ba    <- _B `sub` vVar a
    _Ppair <- _P `sub` VPair (vVar a) (vVar b)
    extendCtx a _A $ extendCtx b _Ba $ checkV ppair _Ppair

inferN nm (Pipe fs (EElimEnum _P pnil pcons)) = do
  let xs = VNeut nm fs
  checkV xs VEnum
  checkVExtend VEnum _P VType
  checkV pnil =<< _P `sub` VNil
  checkVpcons _P pcons
  _P `sub` xs
  where

  checkVpcons :: Bind Nom Type -> Bind Nom3 Value -> SpireM ()
  checkVpcons _P bnd_pcons = do
    ((nm_x , nm_xs , nm_pxs) , pcons) <- unbind bnd_pcons
    _Pxs   <- _P `sub` vVar nm_xs
    _Pcons <- _P `sub` VCons (vVar nm_x) (vVar nm_xs)
    extendCtx nm_x VString $ extendCtx nm_xs VEnum $ extendCtx nm_pxs _Pxs $ checkV pcons _Pcons

inferN nm (Pipe fs (EElimTel _P pemp pext)) = do
  checkVExtend VTel _P VType
  checkV pemp =<< _P `sub` VEmp
  checkVpext _P pext
  let _T = VNeut nm fs
  checkV _T VTel
  _P `sub` _T
  where

  checkVpext :: Bind Nom Type -> Bind Nom3 Value -> SpireM ()
  checkVpext _P bnd_pext = do
    ((_A , _B , pb) , pext) <- unbind bnd_pext
    let nm_a = "a"
    _Ba <- _P `sub` vApp' _B (var nm_a)
    let _PB = VPi (vVar _A) (sbind nm_a _Ba)
    _PExt <- _P `sub` VExt (vVar _A) (fbind' _B nm_a)
    extendCtx _A VType $ extendCtx _B (vVar _A `vArr` VTel) $ extendCtx pb _PB $ checkV pext _PExt

inferN nm (Pipe fs (EElimDesc _I _P pend prec parg)) = do
  let _D = VNeut nm fs
  checkV _I VType
  checkV _D (VDesc _I)
  checkVExtend (VDesc _I) _P VType
  checkVpend _I _P pend
  checkVprec _I _P prec
  checkVparg _I _P parg
  _P `sub` _D
  where

  checkVpend :: Value -> Bind Nom Type -> Bind Nom Value -> SpireM ()
  checkVpend _I _P bnd_pend = do
    (i , pend) <- unbind bnd_pend
    _Pi <- _P `sub` VEnd (vVar i)
    extendCtx i _I $ checkV pend _Pi

  checkVprec :: Value -> Bind Nom Type -> Bind Nom3 Value -> SpireM ()
  checkVprec _I _P bnd_prec = do
    ((i , _D , pd) , prec) <- unbind bnd_prec
    _PD <- _P `sub` (vVar _D)
    _PRec <- _P `sub` VRec (vVar i) (vVar _D)
    extendCtx i _I $ extendCtx _D (VDesc _I) $ extendCtx pd _PD $ checkV prec _PRec

  checkVparg :: Value -> Bind Nom Type -> Bind Nom3 Value -> SpireM ()
  checkVparg _I _P bnd_parg = do
    ((_A , _B , pb) , parg) <- unbind bnd_parg
    let nm_a = "a"
    _Ba <- _P `sub` vApp' _B (var nm_a)
    let _PB = VPi (vVar _A) (sbind nm_a _Ba)
    _PArg <- _P `sub` VArg (vVar _A) (fbind' _B nm_a)
    extendCtx _A VType $ extendCtx _B (vVar _A `vArr` VDesc _I) $ extendCtx pb _PB $ checkV parg _PArg

inferN nm (Pipe fs (ESubst _P px)) = do
  _Q <- inferN nm fs
  case _Q of
    VEq _A x _B y -> do
      unless (_A == _B) $
        throwError "Ill-typed!"
      checkVExtend _A _P VType
      checkV px =<< _P `sub` x
      _P `sub` y
    _  -> throwError "Ill-typed!"

inferN nm (Pipe fs (EFunc _I _X i)) = do
  checkV _I VType
  let _D = VNeut nm fs
  checkV _D (VDesc _I)
  checkVExtend _I _X VType
  checkV i _I
  return VType

inferN nm (Pipe fs (EHyps _I _X _M i xs)) = do
  checkV _I VType
  let _D = VNeut nm fs
  checkV _D (VDesc _I)
  checkVExtend _I _X VType
  checkVM _I _X _M
  checkV i _I
  checkV xs =<< _D `elim` EFunc _I _X i
  return VType

inferN nm (Pipe fs (EProve _I _X _M m i xs)) = do
  checkV _I VType
  let _D = VNeut nm fs
  checkV _D (VDesc _I)
  checkVExtend _I _X VType
  checkVM _I _X _M
  checkVm _I _X _M m
  checkV i _I
  checkV xs =<< _D `elim` EFunc _I _X i
  _D `elim` EHyps _I _X _M i xs
  where

  checkVm :: Type -> Bind Nom Type -> Bind Nom2 Type -> Bind Nom2 Type -> SpireM ()
  checkVm _I _X _M bnd_m = do
    ((i , x) , m) <- unbind bnd_m
    _Xi <- _X `sub` vVar i
    _Mix <- _M `sub2` (vVar i , vVar x)
    extendCtx i _I $ extendCtx x _Xi $ checkV m _Mix

inferN nm (Pipe fs (EInd l _P _I _D p _M m i)) = do
  checkV l VString
  checkV _P VType
  checkV _I VType
  checkV _D (VDesc _I)
  checkV p _P
  checkVM l _P _I _D p i _M
  checkVm l _P _I _D p i _M m
  checkV i _I
  let x = VNeut nm fs
  checkV x (VFix l _P _I _D p i)
  _M `sub2` (i , x)
  where

  checkVM :: Value -> Type -> Type -> Value -> Value -> Value -> Bind Nom2 Type -> SpireM ()
  checkVM l _P _I _D p i bnd_M = do
    ((i , x) , _M) <- unbind bnd_M
    let _X = VFix l _P _I _D p (vVar i)
    extendCtx i _I $ extendCtx x _X $ checkV _M VType

  checkVm :: Value -> Type -> Type -> Value -> Value -> Value -> Bind Nom2 Type -> Bind Nom3 Type -> SpireM ()
  checkVm l _P _I _D p i _M bnd_m = do
    ((i , xs , ihs) , m) <- unbind bnd_m
    let _X = vBind "i" (\j -> VFix l _P _I _D p j)
    _Xs <- _D `elim` EFunc _I _X (vVar i)
    _IHs <- _D `elim` EHyps _I _X _M (vVar i) (vVar xs)
    _Mix <- _M `sub2` (vVar i , VInit (vVar xs))
    extendCtx i _I $ extendCtx xs _Xs $ extendCtx ihs _IHs $ checkV m _Mix

inferN nm (Pipe fs (EBranches _P)) = do
  let _E = VNeut nm fs
  checkV _E VEnum
  checkVExtend (VTag _E) _P VType
  return VType

inferN nm (Pipe fs (ECase _E _P cs)) = do
  let t = VNeut nm fs
  checkV _E VEnum
  checkV t (VTag _E)
  checkVExtend (VTag _E) _P VType
  checkV cs =<< _E `elim` EBranches _P
  _P `sub` t

----------------------------------------------------------------------

checkVM :: Type -> Bind Nom Type -> Bind Nom2 Type -> SpireM ()
checkVM _I _X bnd_M = do
  ((i , x) , _M) <- unbind bnd_M
  _Xi <- _X `sub` vVar i
  extendCtx i _I $ extendCtx x _Xi $ checkV _M VType

----------------------------------------------------------------------

checkVExtend :: Type -> Bind Nom Value -> Type -> SpireM ()
checkVExtend _A bnd_b _B = do
  (x , b) <- unbind bnd_b
  extendCtx x _A $ checkV b _B

----------------------------------------------------------------------