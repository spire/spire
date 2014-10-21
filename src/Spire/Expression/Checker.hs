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
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Spire.Canonical.Types
import Spire.Expression.Types
import Spire.Bound
import Bound

prettyPrint = show

----------------------------------------------------------------------

checkProg :: CProg -> SpireM VProg
checkProg [] = return []
checkProg (CDef nm a _A : xs) = do
  ctx    <- initCtx
  _A'    <- check ctx _A VType
  a'     <- check ctx a _A'
  xs'    <- extendEnv nm a' _A' $ checkProg xs
  return (VDef nm a' _A' : xs')

----------------------------------------------------------------------

check :: (Eq a,Show a) => Sub a -> Check a -> Type a -> SpireM (Value a)
check = check'

infer :: (Eq a,Show a) => Sub a -> Infer a -> SpireM (Value a , Type a)
infer = infer'

----------------------------------------------------------------------

check' ctx (CLam b) (VPi _A _B) = do
  return . VLam =<< checkExtend ctx _A b (fromScope _B)

check' ctx l@(CLam _) _T = throwError $
  "Ill-typed!:\n" ++
  "attempt to check lambda " ++ prettyPrint l ++
  " at type " ++ prettyPrint _T

check' ctx (CPair a b) (VSg _A _B) = do
  a'        <- check ctx a _A
  b'        <- check ctx b (_B `sub` a')
  return    $  VPair a' b'

check' ctx p@(CPair _ _) _T = throwError $
  "Ill-typed!:\n" ++
  "attempt to check pair " ++ prettyPrint p ++
  " at type " ++ prettyPrint _T

check' ctx CRefl (VEq _A a _B b) = do
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

check' ctx as@CRefl _T = throwError $
  "Ill-typed!:\n" ++
  "attempt to check refl " ++
  " at type " ++ prettyPrint _T

check' ctx CHere (VTag (VCons l _E)) = do
  return VHere

check' ctx t@CHere _T = throwError $
  "Ill-typed!:\n" ++
  "attempt to check tag " ++ prettyPrint t ++
  " at type " ++ prettyPrint _T

check' ctx (CThere t) (VTag (VCons l _E)) = do
  t' <- check ctx t (VTag _E)
  return $ VThere t'

check' ctx t@(CThere _) _T = throwError $
  "Ill-typed!:\n" ++
  "attempt to check tag " ++ prettyPrint t ++
  " at type " ++ prettyPrint _T

check' ctx (CEnd i) (VDesc _I) = do
  i' <- check ctx i _I
  return $ VEnd i'

check' ctx _D@(CEnd _) _A = throwError $
  "Ill-typed!:\n" ++
  "attempt to check description " ++ prettyPrint _D ++
  " at type " ++ prettyPrint _A

check' ctx (CRec i _D) (VDesc _I) = do
  i'  <- check ctx i _I
  _D' <- check ctx _D (VDesc _I)
  return $ VRec i' _D'

check' ctx _D@(CRec _ _) _A = throwError $
  "Ill-typed!:\n" ++
  "attempt to check description " ++ prettyPrint _D ++
  " at type " ++ prettyPrint _A

check' ctx (CArg _A _B) (VDesc _I) = do
  _A' <- check ctx _A VType
  _B' <- checkExtend ctx _A' _B (weaken $ VDesc _I)
  return $ VArg _A' _B'

check' ctx _D@(CArg _ _) _A = throwError $
  "Ill-typed!:\n" ++
  "attempt to check description " ++ prettyPrint _D ++
  " at type " ++ prettyPrint _A

check' ctx (CInit xs) (VFix l _P _I _D p i) = do
  let _X = bind1$ \j -> VFix # l # _P # _I # _D # p #! j
  xs' <- check ctx xs $ _D `elim` EFunc _I _X i
  return $ VInit xs'

check' ctx x@(CInit _) _A = throwError $
  "Ill-typed!:\n" ++
  "attempt to check fixpoint " ++ prettyPrint x ++
  " at type " ++ prettyPrint _A

check' ctx (Infer a) _B = do
  (a' , _A) <- infer ctx a
  unless (_A == _B) $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ prettyPrint _B ++
    "\n\nInferred type:\n" ++ prettyPrint _A ++
    -- "\n\nContext:\n" ++ prettyPrint ctx ++
    "\n\nValue:\n" ++ prettyPrint a'
  return a'

----------------------------------------------------------------------

infer' ctx (IQuotes s) = return (VQuotes s , VString)
                                 
infer' ctx (ISg _A _B) = do
  _A' <- check ctx _A VType
  _B' <- checkExtend ctx _A' _B VType
  return (VSg _A' _B' , VType)

infer' ctx (IPi _A _B) = do
  _A' <- check ctx _A VType
  _B' <- checkExtend ctx _A' _B VType
  return (VPi _A' _B' , VType)

infer' ctx (IEq a b) = do
  (a' , _A') <- infer ctx a
  (b' , _B') <- infer ctx b
  return (VEq _A' a' _B' b' , VType)

infer' ctx (IVar nm) = return $ ctx nm

infer' ctx (IAnn a _A) = do
  _A' <- check ctx _A VType
  a'  <- check ctx a _A'
  return (a' , _A')

infer' ctx (IApp f a) = do
  (f' , _F) <- infer ctx f
  case _F of
    VPi _A _B -> do
      a'  <- check ctx a _A
      let b' = elim f' (EApp a')
      let _B' = _B `sub` a'
      return (b' , _B')
    _ -> throwError $
      "Ill-typed, application of non-function!\n" ++
      "Applied value:\n" ++ show f ++
      "\nApplied type:\n" ++ show _F

infer' ctx (IIf b ct cf) = do
  b' <- check ctx b VBool
  (ct' , _C)  <- infer ctx ct
  (cf' , _C') <- infer ctx cf
  unless (_C == _C') $ throwError $
    "Ill-typed, conditional branches have different types!\n" ++
    "First branch:\n" ++ show _C ++
    "\nSecond branch:\n" ++ show _C'
  let c = elim b' (eIf _C ct' cf')
  return (c , _C)

----------------------------------------------------------------------

checkExtend :: (Eq a,Show a) => Sub a -> Type a -> SBind Nom Check a -> Type (Var Nom a) -> SpireM (Bind Nom Value a)
checkExtend ctx _A bnd_b _B = do
  let (ctx' , b) = unbind2 ctx bnd_b
  b' <- check ctx' b _B
  return $ toScope b'

----------------------------------------------------------------------
