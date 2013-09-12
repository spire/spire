{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , ViewPatterns
  #-}

module Spire.Expression.Checker where
import Unbound.LocallyNameless
import Control.Monad.Error
import Control.Monad.Reader
import Spire.Canonical.Types
import Spire.Canonical.Evaluator
import Spire.Expression.Types

----------------------------------------------------------------------

checkProg :: CProg -> SpireM VProg
checkProg [] = return []
checkProg (CDef nm a avs _A _Avs : xs) = do
  _A'    <- check _A VType
  a'     <- check a _A'
  xs'    <- extendEnv nm a' _A' $ checkProg xs
  return (VDef nm a' _A' : xs')

----------------------------------------------------------------------

check :: Check -> Type -> SpireM Value

check (CLam b) (VPi _A _B) = do
  b' <- checkExtend2 _A b _B
  return $ VLam b'

check (CLam _) _ = throwError "Ill-typed!"

check (CPair a b) (VSg _A _B) = do
  a'        <- check a _A
  _B'       <- _B `sub` a'
  b'        <- check b _B'
  return    $  VPair a' b'

check (CPair _ _) _ = throwError "Ill-typed!"

check (Infer a) _B = do
  (a' , _A) <- infer a
  ctx <- asks ctx
  unless (_A == _B) $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ show _B ++
    "\n\nInferred type:\n" ++ show _A ++
    "\n\nContext:\n" ++ show ctx ++
    "\n\nValue:\n" ++ show a'
  return a'

infer :: Infer -> SpireM (Value , Type)

infer ITT    = return (VTT    , VUnit)
infer ITrue  = return (VTrue  , VBool)
infer IFalse = return (VFalse , VBool)

infer IUnit  = return (VUnit  , VType)
infer IBool  = return (VBool  , VType)
infer IType  = return (VType  , VType)

infer (ISg _A _B) = do
  _A' <- check _A VType
  _B' <- checkExtend _A' _B VType
  return (VSg _A' _B' , VType)

infer (IPi _A _B) = do
  _A' <- check _A VType
  _B' <- checkExtend _A' _B VType
  return (VPi _A' _B' , VType)

infer (IVar nm) = do
  ctx <- asks ctx
  lookupCtx nm ctx

infer (IAnn a _A) = do
  _A' <- check _A VType
  a'  <- check a _A'
  return (a' , _A')

infer (IProj1 ab) = do
  (ab' , _AB) <- infer ab
  case _AB of
    VSg _A _B -> do
      a'     <- elim ab' EProj1
      return (a' , _A)
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ show ab ++
      "\nProjected type:\n" ++ show _AB

infer (IProj2 ab) = do
  (ab' , _AB) <- infer ab
  case _AB of
    VSg _A _B -> do
      a'     <- elim ab' EProj1
      b'     <- elim ab' EProj2
      _B'    <- _B `sub` a'
      return (b' , _B')
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ show ab ++
      "\nProjected type:\n" ++ show _AB

infer (IApp f a) = do
  (f' , _F) <- infer f
  case _F of
    VPi _A _B -> do
      a'     <- check a _A
      b'     <- elim f' (EApp a')
      _B'    <- _B `sub` a'
      return (b' , _B')
    _ -> throwError $
      "Ill-typed, projection of non-function!\n" ++
      "Applied value:\n" ++ show f ++
      "\nApplied type:\n" ++ show _F

infer (IIf b ct cf) = do
  b' <- check b VBool
  (ct' , _C)  <- infer ct
  (cf' , _C') <- infer cf
  unless (_C == _C') $ throwError $
    "Ill-typed, conditional branches have different types!\n" ++
    "First branch:\n" ++ show _C ++
    "\nSecond branch:\n" ++ show _C'
  c <- elim b' (eIf _C ct' cf')
  return (c , _C)

infer (ICaseBool _P ct cf b) = do
  b'  <- check b VBool
  _P' <- checkExtend VBool _P VType
  ct' <- check ct =<< _P' `sub` VTrue
  cf' <- check cf =<< _P' `sub` VFalse
  c   <- b' `elim` ECaseBool _P' ct' cf'
  _C  <- _P' `sub` b'
  return (c , _C)

----------------------------------------------------------------------

checkExtend :: Type -> Bind Nom Check -> Type -> SpireM (Bind Nom Value)
checkExtend _A bnd_b _B = do
  (x , b) <- unbind bnd_b
  b'      <- extendCtx x _A $ check b _B
  return  $  bind x b'

checkExtend2 :: Type -> Bind Nom Check -> Bind Nom Type -> SpireM (Bind Nom Value)
checkExtend2 _A bnd_b bnd_B = do
  (nm ,  b) <- unbind bnd_b
  _B        <- bnd_B `sub` vVar nm
  b'        <- extendCtx nm _A $ check b _B
  return    $  bind nm b'

----------------------------------------------------------------------
