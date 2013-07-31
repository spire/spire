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
import Spire.Unbound.SubstM
import Spire.Canonical.Types
import Spire.Canonical.Evaluator
import Spire.Expression.Types
import Data.Functor.Identity

----------------------------------------------------------------------

check :: Check -> Type -> SpireM Value

check (CLam bnd_b) (VPi _A bnd_B) = do
  (nm , _B) <- unbind bnd_B
  b'        <- checkExtend _A bnd_b _B
  return    $  VLam _A b'

check (CLam _) _ = throwError "Ill-typed!"

check (CPair a b) (VSg _A bnd_B) = do
  a'        <- check a _A
  (nm , _B) <- unbind bnd_B
  _B'       <- substM nm a' _B
  b'        <- check b _B'
  return    $  VPair a' b' _B

check (CPair _ _) _ = throwError "Ill-typed!"

check (Infer a) _B = do
  (a' , _A) <- infer a
  ctx <- asks ctx
  unless (_A == _B) $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ show _B ++
    "\n\nInferred type:\n" ++ show _A ++
    "\n\nContext:\n" ++ show ctx ++
    "\n\nUnevaluated value:\n" ++ show a
  return a'

infer :: Infer -> SpireM (Value , Type)
infer ITT    = return (VTT   , VUnit)
infer ITrue  = return (VTrue   , VUnit)
infer IFalse = return (VFalse   , VUnit)
infer IUnit  = return (VUnit , VType)
infer IBool  = return (VBool , VType)
infer IType  = return (VType , VType)

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
  lookUp nm ctx

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
      _B'    <- _B $$ a'
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
      _B'    <- _B $$ a'
      return (b' , _B')
    _ -> throwError $
      "Ill-typed, projection of non-function!\n" ++
      "Applied value:\n" ++ show f ++
      "\nApplied type:\n" ++ show _F

infer (IIf b ct cf) = do
  b' <- check b VBool
  (ct' , _C) <- infer ct
  (cf' , _C') <- infer cf
  unless (_C == _C') $ throwError $
    "Ill-typed, conditional branches have different types!\n" ++
    "First branch:\n" ++ show _C ++
    "\nSecond branch:\n" ++ show _C'
  c <- elim b' (EIf ct' cf')
  return (c , _C)

----------------------------------------------------------------------

lookUp :: Nom -> Tel -> SpireM (Value , Type)
lookUp nm Empty = do
  ctx <- asks ctx
  throwError $
    "Variable not in context!\n" ++
    "Referenced variable:\n" ++ show nm ++
    "\nCurrent context:\n" ++ show ctx
lookUp nm (Extend (unrebind -> ((x , Embed _A) , xs))) =
  if nm == x
  then return (vVar nm , _A)
  else lookUp nm xs

----------------------------------------------------------------------

checkExtend :: Type -> Bind Nom Check -> Type -> SpireM (Bind Nom Value)
checkExtend _A bd _B = do
  ctx <- asks ctx
  (x , b) <- unbind bd
  b' <- extendCtx x _A $ check b _B
  return $ bind x b'

extendCtx :: Nom -> Type -> SpireM a -> SpireM a
extendCtx x _A = local
  (\r -> r { ctx = snocTel (ctx r) (x , Embed _A) })

----------------------------------------------------------------------
