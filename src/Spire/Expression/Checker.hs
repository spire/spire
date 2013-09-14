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
import Control.Monad.State
import Spire.Canonical.Types
import Spire.Canonical.Evaluator
import Spire.Expression.Types

----------------------------------------------------------------------

checkProg :: CProg -> SpireM VProg
checkProg [] = return []
checkProg (CDef nm a avs _A _Avs : xs) = do
  _A'    <- refine _A _Avs VType
  a'     <- refine a avs _A'
  xs'    <- extendEnv nm a' _A' $ checkProg xs
  return (VDef nm a' _A' : xs')

----------------------------------------------------------------------
-- Now with Matita-inspired refinement!

-- XXX: The mvar decls are used to initialize the unification state
-- (mvar decls, mvar defs, unification problems).  Then the checker is
-- run.  Then the resulting state is inspected, e.g. to make sure that
-- all the unification problems were solved and all the mvars were
-- solved.
--
-- By changing the final state inspections here we can e.g. allow
-- unification to span multiple definitions, or for mvars in types to
-- be solved when refining the corresponding terms (type inference).
refine :: Check -> MVarDecls -> Type -> SpireM Value
refine a avs aT = do
  -- XXX: Initialize unification state
  modify (\r -> r { unifierCtx = () })
  a' <- check a aT
  -- XXX: Check unification state
  {- ... -}
  return a'

-- XXX
unify :: Type -> Value -> Value -> SpireM Bool
unify _ v1 v2 = return $ v1 == v2

unifyTypes :: Type -> Type -> SpireM () -> SpireM ()
unifyTypes t1 t2 m = do
  b <- unify VType t1 t2
  unless b m

-- XXX: Turn a type into a pi-type, by expanding it if it's an mvar
-- application, and failing if it's any other non-pi-type value.
forcePi :: Type -> SpireM (Type , Bind Nom Type)
forcePi = undefined

----------------------------------------------------------------------

check :: Check -> Type -> SpireM Value

check (CLam b) (VPi _A _B) = do
  -- XXX: Could do 'forcePi' here, but I'm not sure what we'd gain
  -- ... wait for an example.
  b' <- checkExtend2 _A b _B
  return $ VLam b'

check (CLam _) _ = throwError "Ill-typed!"

check (CPair a b) (VSg _A _B) = do
  -- XXX: Could have a 'forceSig' here, but again, not sure what it's
  -- good for.
  a'        <- check a _A
  _B'       <- _B `sub` a'
  b'        <- check b _B'
  return    $  VPair a' b'

check (CPair _ _) _ = throwError "Ill-typed!"

check (Infer a) _B = do
  (a' , _A) <- infer a
  ctx <- asks ctx
  unifyTypes _A _B $ throwError $
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
  -- XXX: Another 'forceSig' opportunity; analogous to the use of
  -- 'forcePi' in 'IApp' below?
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
  (_A , _B) <- forcePi _F
  a'        <- check a _A
  b'        <- elim f' (EApp a')
  _B'       <- _B `sub` a'
  return    (b' , _B')
{-
    _ -> throwError $
      "Ill-typed, application of non-function!\n" ++
      "Applied value:\n" ++ show f ++
      "\nApplied type:\n" ++ show _F
-}

infer (IIf b ct cf) = do
  b' <- check b VBool
  (ct' , _C)  <- infer ct
  (cf' , _C') <- infer cf
  unifyTypes _C _C' $ throwError $
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
