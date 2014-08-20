{-# LANGUAGE MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
           , ViewPatterns
           , NoMonomorphismRestriction
           , CPP
           #-}

module Spire.Expression.Checker where
import Unbound.LocallyNameless
import Unbound.LocallyNameless.SubstM
import Control.Applicative ((<$>))
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Spire.Canonical.Types
import Spire.Canonical.Evaluator
import Spire.Debug
import Spire.Expression.Types
import Spire.Surface.PrettyPrinter

----------------------------------------------------------------------

checkProg :: CProg -> SpireM VProg
checkProg [] = return []
checkProg (CDef nm a _A : xs) = do
  _A'    <- check _A VType
  a'     <- check a _A'
  xs'    <- extendEnv nm a' _A' $ checkProg xs
  return (VDef nm a' _A' : xs')

----------------------------------------------------------------------

check :: Check -> Type -> SpireM Value
check x _T = do
  ctx <- asks ctx
  let p = prettyPrintError
  let msg = p ctx ++ "\n" ++
            "|-" ++ "\n" ++
            p x ++ "\n" ++
            "<=" ++ "\n" ++
            p _T ++ "\n"
  check' x _T `debug` msg

infer :: Infer -> SpireM (Value , Type)
infer x = do
  ctx <- asks ctx
  let p = prettyPrintError
  let msg = p ctx ++ "\n" ++
            "|-" ++ "\n" ++
            p x ++ "\n" ++
            "=>"
  r@(x' , _T) <- infer' x `debug` msg ++ "...\n"
  return r `debug` "..." ++ msg ++ "\n" ++
                   p _T ++ "\n" ++
                   "~>\n" ++
                   p x' ++ "\n"

----------------------------------------------------------------------

check' (CLam b) (VPi _A _B) = do
  b' <- checkLam _A b _B
  return $ VLam b' where

  checkLam :: Type -> Bind Nom Check -> Bind Nom Type -> SpireM (Bind Nom Value)
  checkLam _A bnd_b bnd_B = do
    (nm_a ,  b) <- unbind bnd_b
    _B          <- bnd_B `sub` vVar nm_a
    b'          <- extendCtx nm_a _A $ check b _B
    return      $  bind nm_a b'

check' l@(CLam _) _T = throwError $
  "Ill-typed!:\n" ++
  "attempt to check lambda " ++ prettyPrint l ++
  " at type " ++ prettyPrint _T

check' (CPair a b) (VSg _A _B) = do
  -- XXX: Could have a 'forceSig' here, but again, not sure what it's
  -- good for.
  a'        <- check a _A
  _B'       <- _B `sub` a'
  b'        <- check b _B'
  return    $  VPair a' b'

check' p@(CPair _ _) _T = throwError $
  "Ill-typed!:\n" ++
  "attempt to check pair " ++ prettyPrint p ++
  " at type " ++ prettyPrint _T

check' CRefl (VEq _A a _B b) = do
  unless (_A == _B) $
    throwError $
      "Ill-typed!:\n" ++
      "equality domain type " ++ prettyPrint _A ++
      " does not match codomain type " ++ prettyPrint _B
  unless (a == b) $
    throwError $
      "Ill-typed!:\n" ++
      "equality domain value " ++ prettyPrint a ++
      " does not match codomain value " ++ prettyPrint b
  return VRefl

check' as@CRefl _T = throwError $
  "Ill-typed!:\n" ++
  "attempt to check refl " ++
  " at type " ++ prettyPrint _T

check' CHere (VTag (VCons l _E)) = do
  return VHere

check' t@CHere _T = throwError $
  "Ill-typed!:\n" ++
  "attempt to check tag " ++ prettyPrint t ++
  " at type " ++ prettyPrint _T

check' (CThere t) (VTag (VCons l _E)) = do
  t' <- check t (VTag _E)
  return $ VThere t'

check' t@(CThere _) _T = throwError $
  "Ill-typed!:\n" ++
  "attempt to check tag " ++ prettyPrint t ++
  " at type " ++ prettyPrint _T

check' (CEnd i) (VDesc _I) = do
  i' <- check i _I
  return $ VEnd i'

check' _D@(CEnd _) _A = throwError $
  "Ill-typed!:\n" ++
  "attempt to check description " ++ prettyPrint _D ++
  " at type " ++ prettyPrint _A

check' (CRec i _D) (VDesc _I) = do
  i'  <- check i _I
  _D' <- check _D (VDesc _I)
  return $ VRec i' _D'

check' _D@(CRec _ _) _A = throwError $
  "Ill-typed!:\n" ++
  "attempt to check description " ++ prettyPrint _D ++
  " at type " ++ prettyPrint _A

check' (CArg _A _B) (VDesc _I) = do
  _A' <- check _A VType
  _B' <- checkExtend _A' _B (VDesc _I)
  return $ VArg _A' _B'

check' _D@(CArg _ _) _A = throwError $
  "Ill-typed!:\n" ++
  "attempt to check description " ++ prettyPrint _D ++
  " at type " ++ prettyPrint _A

check' (CInit xs) (VFix l _P _I _D p i) = do
  let _X = vBind "i" (\j -> VFix l _P _I _D p j)
  xs' <- check xs =<< _D `elim` EFunc _I _X i
  return $ VInit xs'

check' x@(CInit _) _A = throwError $
  "Ill-typed!:\n" ++
  "attempt to check fixpoint " ++ prettyPrint x ++
  " at type " ++ prettyPrint _A

check' (Infer a) _B = do
  (a' , _A) <- infer a
  ctx <- asks ctx
  unless (_A == _B) $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ prettyPrint _B ++
    "\n\nInferred type:\n" ++ prettyPrint _A ++
    "\n\nContext:\n" ++ prettyPrint ctx ++
    "\n\nValue:\n" ++ prettyPrint a'
  return a'

infer' (IQuotes s) = return (VQuotes s , VString)
                                 
infer' (ISg _A _B) = do
  _A' <- check _A VType
  _B' <- checkExtend _A' _B VType
  return (VSg _A' _B' , VType)

infer' (IPi _A _B) = do
  _A' <- check _A VType
  _B' <- checkExtend _A' _B VType
  return (VPi _A' _B' , VType)

infer' (IEq a b) = do
  (a' , _A') <- infer a
  (b' , _B') <- infer b
  return (VEq _A' a' _B' b' , VType)

infer' (IVar nm) = lookupValAndType nm

infer' (IAnn a _A) = do
  _A' <- check _A VType
  a'  <- check a _A'
  return (a' , _A')

infer' (IApp f a) = do
  (f' , _F) <- infer f
  case _F of
    VPi _A _B -> do
      a'  <- check a _A
      b'  <- elim f' (EApp a')
      _B' <- _B `sub` a'
      return (b' , _B')
    _ -> throwError $
      "Ill-typed, application of non-function!\n" ++
      "Applied value:\n" ++ show f ++
      "\nApplied type:\n" ++ show _F

infer' (IIf b ct cf) = do
  b' <- check b VBool
  (ct' , _C)  <- infer ct
  (cf' , _C') <- infer cf
  unless (_C == _C') $ throwError $
    "Ill-typed, conditional branches have different types!\n" ++
    "First branch:\n" ++ show _C ++
    "\nSecond branch:\n" ++ show _C'
  c <- elim b' (eIf _C ct' cf')
  return (c , _C)

----------------------------------------------------------------------

checkExtend :: Type -> Bind Nom Check -> Type -> SpireM (Bind Nom Value)
checkExtend _A bnd_b _B = do
  (x , b) <- unbind bnd_b
  b'      <- extendCtx x _A $ check b _B
  return  $  bind x b'

----------------------------------------------------------------------
