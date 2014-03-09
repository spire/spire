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
  sequence_ . unMVarDecls $ avs

  -- Update unification state.
  a' <- check a aT

  -- Check and apply unification state.
  concretize True a'

-- XXX: I'd like to put this function in Spire.Canonical.Unification,
-- with the other Gundry bridge code, but that creates an import cycle
-- with Spire.Canonical.Evaluator.
--
-- Convert unifier context to substitutions. Checks for errors if
-- 'validate' is 'True'.
--
-- Errors are:
--
-- - unsolved problems
--
-- - unsolved mvars
--
-- Assumes the context is well formed, i.e. that all mvars are
-- declared in it.

ctx2Substitutions :: Bool -> [Entry] -> SpireM [(Spire.Canonical.Types.Nom, Value)]
ctx2Substitutions validate ctx = c return ctx where
  c :: (Value -> SpireM Value) -> [Entry] -> SpireM [(Spire.Canonical.Types.Nom, Value)]
  c _ [] = return []
  c sub (p@(Q _ _) : es) =
    if validate then
      error $ "ctx2Substitutions: meta context:\n" ++
              prettyPrintError ctx ++ "\n" ++
              "contains unsolved problem:\n" ++
              prettyPrintError p
    else c sub es
  c sub (m@(E _ (_ , HOLE)) : es) =
    if validate then
      error $ "ctx2Substitutions: meta context:\n" ++
              prettyPrintError ctx ++ "\n" ++
              "contains unsolved metavar:\n" ++
              prettyPrintError m
    else c sub es
  c sub (E x (_ , DEFN v) : es) = do
    let x' = translate x
    v' <- sub =<< tm2Value v
    ((x' , v') :) <$> c (substM x' v' <=< sub) es

unifyTypes :: String -> Type -> Type -> SpireM () -> SpireM ()
unifyTypes s t1 t2 m =
  -- XXX: May be better (efficiency or error messages) to check if
  -- 't1' and 't2' were "pure", i.e. didn't contain any mvars, and in
  -- that case only use the alpha-equality '=='.  Right now, in the
  -- case of a type error, we will fire an impossible unification
  -- problem and then give an error.
  when (t1 /= t2) $ do
    let msg = s ++ ": " ++ prettyPrint t1 ++ " =u= " ++ prettyPrint t2
    b <- unify VType t1 t2 `debug` msg
    unless b m

-- Like "zonking" in GHC: substitute mvar values for their uses.
concretize :: Bool -> Value -> SpireM Value
concretize validate v = do
  -- Check unification state.
  --
  -- Could type check subs, but Gundry essentially already did that.
  ctx <- gets unifierCtx
  subs <- ctx2Substitutions validate ctx
          `debug` "concretize: metactx: " ++
                  prettyPrintError ctx

  -- Apply unification state (substitute).
  foldM (flip $ uncurry substM) v subs

-- Turn a type into a pi-type, by expanding it if it's an mvar
-- application, and failing if it's any other non-pi-type value.
forcePi :: Type -> SpireM (Type , Bind Nom Type)
forcePi = forcePi' <=< concretize False
forcePi' (VPi _A _B) = return (_A , _B)
-- Given a metavar application
--
--   ? x1...xn
--
-- we create a new pi type
--
--   forall x : ?A x1...xn . ?B x1...xn x
--
-- and equate it with the given metavar application, by introducing
-- the unification problem
--
--   ? x1...xn =u= forall x : ?A x1...xn . ?B x1...xn x .
--
-- We return the applications
--
--   (?A x1 ... xn , \x . ?B x1 ... xn x) .
--
-- ----------------------------------------------------------------------
--
-- We used to declare the parts
--
--   ?A : forall x1:T1...xn:Tn . Type
--   ?B : forall x1:T1...xn:Tn x:(?A x1...xn) . Type
--
-- and return their applications
--
--   (?A x1 ... xn , \x . ?B x1 ... xn x) ,
--
-- But I'm going to make the refiner figure out these types for us,
-- instead of constructing them. This will make life much easier when
-- adding support for splitting mvars applied to mvars.
--
-- E.g., in the 'id _ id _ x' example, we end up with 'forceMVApp' of
--'?M x (?N x)', and it would be nice to simply split this into
--
--   ?M x (?N x) =u= Pi y : ?MA x (?N x) . ?MB x (?N x) y .
--
-- Also, the fact that I don't check the variables returned by
-- 'forceMVApp' for uniqueness (linearity) may be a bug with the
-- current version, which defines the types, because of shadowing. For
-- example
--
--   forcePi ?M x x
--
-- produces
--
--   ?M x x =u= ?Pi y : ?MA x x . ?MB x x y
--
-- with
--
--   ?MA : Pi x : xT . Pi x : xT . Type
--   ?MB : Pi x : xT . Pi x : xT . (?MA x x) -> Type .
--
-- I don't actually see why this is bad, but it makes me a little
-- uneasy; deserves more thought.  But, in the mean time, I'm just
-- going to stop constructing the types, and let inference take care
-- of that.
forcePi' _T = do
  -- Generate mvars for domain and range.
  (mv , args) <- forceMVApp _T
  let prefix = mv2String mv ++ "_\x03C0" -- Unicode small pi.
  _A <- freshMV $ prefix ++ "A"
  _B <- freshMV $ prefix ++ "B"

  -- Declare types.
  --
  -- Note that '_A' and '_T' have the same type, but '_B's type is
  -- '_T's type with '_A'' inserted as a last domain type.
  x <- fresh . s2n $ prefix ++ "x"
  xTs <- unfoldPi =<< lookupType mv
  _A'' <- foldApp _A (map (vVar . fst) xTs)
  -- _AT == mvT
  let _AT = foldPi  xTs                  VType
  let _BT = foldPi (xTs ++ [(x , _A'')]) VType
  declareMVOfType _AT _A
  declareMVOfType _BT _B

  -- Apply mvars to '_T's args.
  --
  -- Note that '_A'' is concrete and '_A''' is abstract.
  _A' <-            foldApp _A  args
  _B' <- bind x <$> foldApp _B (args ++ [vVar x])

  -- Relate generated mvars to '_T'.
  unifyTypes "forcePi" _T (VPi _A' _B') $ throwError "Unreachable code!"
  return (_A' , _B') `debug` "_A' = " ++ prettyPrintError _A' ++ "\n" ++
                             "_B' = " ++ prettyPrintError (VLam _B') ++ "\n"
  where
    -- unfoldPi Pi x1 : T1 . ... . xn : Tn . Type
    -- ==>
    -- [(x1:T1) ... (xn:Tn)]
    unfoldPi :: Type -> SpireM [(Nom , Type)]
    unfoldPi VType = return []
    unfoldPi (VPi _A _B) = do
      (x , _B') <- unbind _B
      ((x , _A) :) <$> unfoldPi _B'
    unfoldPi _T = error $ "unfoldPi: unexpected: " ++ prettyPrintError _T
                  ++ ".This could be a type error or a bug ... savor the mystery!"

    -- foldPi [(x1 , T1) ... (xn , Tn)] range
    -- ==>
    -- Pi x1 : T1 . Pi x2 : T2 . ... . Pi xn : Tn . range
    foldPi :: [(Nom , Type)] -> Type -> Type
    foldPi xTs _T = foldr mkPi _T xTs
      where
      mkPi = \(x , _A) _B -> VPi _A (bind x _B)

    -- foldApp f xs ==> f x1 ... xn
    foldApp :: Nom -> [Value] -> SpireM Value
    foldApp x xs = foldM elim (vVar x) (map EApp xs)
-- forcePi _T = throwError $ "Failed to force Pi type: " ++ prettyPrint _T

-- Decompose a type as an mvar applied to a spine of arguments.
forceMVApp :: Type -> SpireM (Nom , [Value])
forceMVApp _T = case _T `debug` "forceMVApp " ++ prettyPrintError _T of
  VNeut nm s -> do
    args <- unSpine s
    if isMV nm
    then return (nm , reverse args)
    else die
  _ -> die
  where
    -- The 'Spine' is a snoc list, so the list built here is backwards.
    unSpine Id = return []
    unSpine (Pipe s (EApp e)) = (e:) <$> unSpine s
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

check' CNil (VList _A) = do
  return VNil

check' as@CNil _T = throwError $
  "Ill-typed!:\n" ++
  "attempt to check list " ++ prettyPrint as ++
  " at type " ++ prettyPrint _T

check' (CCons a as) (VList _A) = do
  a'     <- check a _A
  as'    <- check as (VList _A)
  return $  VCons a' as'

check' as@(CCons _ _) _T = throwError $
  "Ill-typed!:\n" ++
  "attempt to check list " ++ prettyPrint as ++
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

check' (Infer a) _B = do
  (a' , _A) <- infer a
  ctx <- asks ctx
  unifyTypes "check'/Infer" _A _B $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ prettyPrint _B ++
    "\n\nInferred type:\n" ++ prettyPrint _A ++
    "\n\nContext:\n" ++ prettyPrint ctx ++
    "\n\nValue:\n" ++ prettyPrint a'
  return a'

infer' ITT         = return (VTT       , VUnit)
infer' ITrue       = return (VTrue     , VBool)
infer' IFalse      = return (VFalse    , VBool)
infer' (IQuotes s) = return (VQuotes s , VString)
                                 
infer' IUnit   = return (VUnit   , VType)
infer' IBool   = return (VBool   , VType)
infer' IString = return (VString , VType)
infer' IType   = return (VType   , VType)

infer' (IList _A) = do
  _A' <- check _A VType
  return (VList _A' , VType)

infer' (ITag _E) = do
  _E' <- check _E vEnum
  return (VTag _E' , VType)

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
  unifyTypes "infer'/IIf" _C _C' $ throwError $
    "Ill-typed, conditional branches have different types!\n" ++
    "First branch:\n" ++ show _C ++
    "\nSecond branch:\n" ++ show _C'
  c <- elim b' (eIf _C ct' cf')
  return (c , _C)

infer' (IElimBool _P ct cf b) = do
  _P' <- checkExtend VBool _P VType
  ct' <- check ct =<< _P' `sub` VTrue
  cf' <- check cf =<< _P' `sub` VFalse
  b'  <- check b VBool
  c   <- b' `elim` EElimBool _P' ct' cf'
  _C  <- _P' `sub` b'
  return (c , _C)

infer' (IElimList _P pnil pcons as) = do
  (as' , _As') <- infer as
  case _As' of
    VList _A' -> do
      _P'    <- checkExtend (VList _A') _P VType
      pnil'  <- check pnil =<< _P' `sub` VNil
      pcons' <- checkPCons _A' _P' pcons
      pas'   <- as' `elim` EElimList _A' _P' pnil' pcons'
      _Pas'  <- _P' `sub` as'
      return (pas' , _Pas')
    _ -> throwError $
      "Ill-typed, elimination of non-list!\n" ++
      "Eliminated value:\n" ++ show as' ++
      "\nEliminated type:\n" ++ show _As'

  where

  checkPCons :: Type -> Bind Nom Type -> Bind (Nom , Nom , Nom) Check -> SpireM (Bind (Nom , Nom , Nom) Value)
  checkPCons _A bnd_P bnd_pcons = do
    ((nm_a , nm_as , nm_pas) , pcons) <- unbind bnd_pcons
    _Pas    <- bnd_P `sub` vVar nm_as
    _Pcons  <- bnd_P `sub` VCons (vVar nm_a) (vVar nm_as)
    pcons'  <- extendCtx nm_a _A $ extendCtx nm_as (VList _A) $ extendCtx nm_pas _Pas $ check pcons _Pcons
    return  $  bind (nm_a , nm_as , nm_pas) pcons'

infer' (ISubst _P q px) = do
  (q' , _Q') <- infer q
  case _Q' of
    VEq _A x _B y -> do
      _P' <- checkExtend _A _P VType
      unless (_A == _B) $
        throwError $
          "Ill-typed!:\n" ++
          "using subst when equality domain type " ++ prettyPrint _A ++
          " does not match codomain type " ++ prettyPrint _B
      px' <- check px =<< _P' `sub` x
      py  <- q' `elim` ESubst _A _P' x y px'
      _Py <- _P' `sub` y
      return (py , _Py)

    _ -> throwError $
      "Ill-typed, substitution of non-equality!\n" ++
      "Eliminated value:\n" ++ show q' ++
      "\nEliminated type:\n" ++ show _Q'

infer' (IBranches _E _P) = do
  _E' <- check _E vEnum
  _P' <- checkExtend _E' _P VType
  _BsEP <- _E' `elim` EBranches _P'
  return (_BsEP , VType)

infer' (ICase _P cs t) = do
  (t' , _T') <- infer t
  case _T' of
    VTag _E -> do
      _P'   <- checkExtend (VTag _E) _P VType
      _BsEP <- _E `elim` EBranches _P'
      cs'   <- check cs _BsEP
      pt    <- t' `elim` ECase _E _P' cs'
      _Pt   <- _P' `sub` t'
      return (pt , _Pt)

    _ -> throwError $
      "Ill-typed, case of non-tag!\n" ++
      "Eliminated value:\n" ++ show t' ++
      "\nEliminated type:\n" ++ show _T'

----------------------------------------------------------------------

checkExtend :: Type -> Bind Nom Check -> Type -> SpireM (Bind Nom Value)
checkExtend _A bnd_b _B = do
  (x , b) <- unbind bnd_b
  b'      <- extendCtx x _A $ check b _B
  return  $  bind x b'

----------------------------------------------------------------------
