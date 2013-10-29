{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , ViewPatterns
  , NoMonomorphismRestriction
  #-}

module Spire.Expression.Checker where
import Unbound.LocallyNameless
import Unbound.LocallyNameless.SubstM
import Control.Applicative ((<$>))
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import PatternUnify.Context (Entry(..) , Decl(..))
import Spire.Canonical.Types
import Spire.Canonical.Evaluator
import Spire.Canonical.Unification
import Spire.Debug
import Spire.Expression.Types
import Spire.Surface.PrettyPrinter

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

-- The mvar decls are used to initialize the unification state
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
  -- Initialize unification state
  put emptySpireS
  mapM (uncurry declareMV) avs

  -- Update unification state.
  a' <- check a aT

  -- Check unification state.
  --
  -- Could type check subs, but Gundry essentially already did that.
  ctx <- gets unifierCtx
  subs <- ctx2Substitutions ctx
          `debug` "refine: metactx after refinement: " ++
                  prettyPrintError ctx

  -- Apply unification state (substitute).
  foldM (flip $ uncurry substM) a' subs

-- XXX: I'd like to put this function in Spire.Canonical.Unification,
-- with the other Gundry bridge code, but that creates an import cycle
-- with Spire.Canonical.Evaluator.
--
-- Convert unifier context to substitutions while checking for
-- errors. Errors are:
-- - unsolved problems
-- - unsolved mvars
--
-- Assumes the context is well formed, i.e. that all mvars are
-- declared in it.

ctx2Substitutions :: [Entry] -> SpireM [(Spire.Canonical.Types.Nom, Value)]
ctx2Substitutions ctx = c return ctx where
  c :: (Value -> SpireM Value) -> [Entry] -> SpireM [(Spire.Canonical.Types.Nom, Value)]
  c _ [] = return []
  c _ (Q _ _ : _) =
    error $ "ctx2Substitutions: meta context contains unsolved problem: " ++
            prettyPrintError ctx
  c _ (E _ (_ , HOLE) : _) =
    error $ "ctx2Substitutions: meta context contains unsolved metavar: " ++
            prettyPrintError ctx
  c sub (E x (_ , DEFN v) : es) = do
    let x' = translate x
    v' <- sub =<< tm2Value v
    ((x' , v') :) <$> c (substM x' v' <=< sub) es

unifyTypes :: Type -> Type -> SpireM () -> SpireM ()
unifyTypes t1 t2 m = do
  b <- unify VType t1 t2
  unless b m

-- Turn a type into a pi-type, by expanding it if it's an mvar
-- application, and failing if it's any other non-pi-type value.
forcePi :: Type -> SpireM (Type , Bind Nom Type)
forcePi (VPi _A _B) = return (_A , _B)
-- Given a metavar application
--
--   ? x1...xn
--
-- we create a new pi type
--
--   forall x : ?A x1...xn . ?B x1...xn x
--
-- and equate it with the given metavar application.
--
-- We declare the parts
--
--   ?A : forall x1:T1...xn:Tn . Type
--   ?B : forall x1:T1...xn:Tn x:(?A x1...xn) . Type
--
-- and return their applications
--
--   (?A x1 ... xn , \x . ?B x1 ... xn x) .
--
-- Could we make the refiner figure out these types for us, instead of
-- constructing them?
forcePi _T = do
  (_ , args) <- forceMVApp _T
  _A <- freshMV
  _B <- freshMV
  argTs <- mapM lookupType args
  declareMV _A (foldPi args argTs VType)
  _A' <- foldApp _A args
  x <- fresh . s2n $ "_forcePi"
  declareMV _B (foldPi (args ++ [x])  (argTs ++ [_A']) VType)
  _B' <- bind x <$> foldApp _B (args ++ [x])
  unify VType _T (VPi _A' _B')
  return (_A' , _B') `debug` "_A' = " ++ prettyPrintError _A' ++ "\n" ++ "_B' = " ++ prettyPrintError (VLam _B') ++ "\n"
  where
    foldPi :: [Nom] -> [Type] -> Type -> Type
    foldPi xs xTs _T = foldr mkPi _T (zip xs xTs)
      where
      mkPi = (\(x , xT) _T -> VPi xT (bind x _T))

    foldApp :: Nom -> [Nom] -> SpireM Value
    foldApp x xs = foldM elim (vVar x) (map (EApp . vVar) xs)
-- forcePi _T = throwError $ "Failed to force Pi type: " ++ prettyPrint _T

-- Decompose a type as an mvar applied to a spine of arguments.
forceMVApp :: Type -> SpireM (Nom , [Nom])
forceMVApp _T = case _T `debug` "forceMVApp " ++ prettyPrintError _T of
  VNeut nm s -> do
    args <- unSpine s
    if isMV nm
    then return (nm , args)
    else die
  _ -> die
  where
    unSpine Id = return []
    unSpine (Pipe s (EApp (VNeut x Id))) = (x:) <$> unSpine s
    unSpine _ = die

    die = throwError $ "Failed to force MV app: " ++ prettyPrint _T

----------------------------------------------------------------------
-- Debugging shims can be inserted between 'f' and 'f'' here.

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
  -- XXX: Could do 'forcePi' here, but I'm not sure what we'd gain
  -- ... wait for an example.
  b' <- checkExtend2 _A b _B
  return $ VLam b'

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

check' (Infer a) _B = do
  (a' , _A) <- infer a
  ctx <- asks ctx
  unifyTypes _A _B $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ show _B ++
    "\n\nInferred type:\n" ++ show _A ++
    "\n\nContext:\n" ++ show ctx ++
    "\n\nValue:\n" ++ show a'
  return a'

infer' ITT    = return (VTT    , VUnit)
infer' ITrue  = return (VTrue  , VBool)
infer' IFalse = return (VFalse , VBool)

infer' IUnit  = return (VUnit  , VType)
infer' IBool  = return (VBool  , VType)
infer' IType  = return (VType  , VType)

infer' (ISg _A _B) = do
  _A' <- check _A VType
  _B' <- checkExtend _A' _B VType
  return (VSg _A' _B' , VType)

infer' (IPi _A _B) = do
  _A' <- check _A VType
  _B' <- checkExtend _A' _B VType
  return (VPi _A' _B' , VType)

infer' (IVar nm) = lookupValAndType nm

infer' (IAnn a _A) = do
  _A' <- check _A VType
  a'  <- check a _A'
  return (a' , _A')

infer' (IProj1 ab) = do
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

infer' (IProj2 ab) = do
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

infer' (IApp f a) = do
  (f' , _F) <- infer f
  (_A , _B) <- forcePi _F
  a'        <- check a _A
  b'        <- elim f' (EApp a')
  _B'       <- _B `sub` a'
  let p = prettyPrintError
  let msg = "infer IApp:\n" ++ "f' = " ++ p f' ++ "\n" ++
            "a' = " ++ p a' ++ "\n" ++
            "b' = " ++ p b' ++ "\n" ++
            "_B = " ++ p (VLam _B) ++ "\n" ++
            "_B' = " ++ p _B' ++ "\n"
  return (b' , _B') `debug` msg
{-
    _ -> throwError $
      "Ill-typed, application of non-function!\n" ++
      "Applied value:\n" ++ show f ++
      "\nApplied type:\n" ++ show _F
-}

infer' (IIf b ct cf) = do
  b' <- check b VBool
  (ct' , _C)  <- infer ct
  (cf' , _C') <- infer cf
  unifyTypes _C _C' $ throwError $
    "Ill-typed, conditional branches have different types!\n" ++
    "First branch:\n" ++ show _C ++
    "\nSecond branch:\n" ++ show _C'
  c <- elim b' (eIf _C ct' cf')
  return (c , _C)

infer' (ICaseBool _P ct cf b) = do
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
