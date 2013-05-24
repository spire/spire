{-# LANGUAGE Rank2Types #-}
module Spire.Canonical.HereditarySubstitution
  ( sub , foldSub
  , evalStrAppend , evalStrEq , evalIf , evalCaseBool
  , evalProj1 , evalProj2 , evalApp , evalDInterp )
where
import Control.Monad.Reader
import Data.Generics
import Spire.Canonical.Types

import Debug.Trace
-- trace' x y = trace x y
trace' x y = y

----------------------------------------------------------------------

subV :: Var -> Val -> Val -> Val
subV i x aT@VUnit = aT
subV i x aT@VBool = aT
subV i x aT@VString = aT
subV i x aT@VDesc = aT
subV i x aT@VProg = aT
subV i x aT@VType = aT
subV i x a@VTT = a
subV i x a@VTrue = a
subV i x a@VFalse = a
subV i x a@(VQuotes _) = a
subV i x (VPi aT bT) = VPi (subV i x aT) (subExtend i x bT)
subV i x (VSg aT bT) = VSg (subV i x aT) (subExtend i x bT)
subV i x (VFix d) = VFix (subV i x d)
subV i x (VPair aT bT a b) =
  VPair (subV i x aT) (subExtend i x bT) (subV i x a) (subV i x b)
subV i x (VLam aT f) = VLam (subV i x aT) (subExtend i x f)
subV i x (VDefs as) = VDefs (subVs i x as)
subV i x d@VDUnit = d
subV i x d@VDRec = d
subV i x (VDSum d e) = VDSum (subV i x d) (subV i x e)
subV i x (VDPi aT fD) = VDPi (subV i x aT) (subExtend i x fD)
subV i x (VDSg aT fD) = VDSg (subV i x aT) (subExtend i x fD)
subV i x (VIn d a) = VIn (subV i x d) (subV i x a)
subV i x (Neut n) = subN i x n

subN :: Var -> Val -> Neut -> Val
subN i x nv@(NVar (NomVar (l , j)))
  | i == j = x
  -- This assumes that we only substitute by eliminating a binder (and
  -- hence unbinding the current variable 0).  Bad things could happen
  -- in general, e.g. , if we were doing an alpha renaming
  -- substitution of '\ x -> x z' to '\ y -> y z':
  --
  --   Lam [("y",0)/#0] (App ("x",0) ("z",1))
  --
  -- we would *not* want to decrement '("z", 1) to ("z" , 0)' ...
  | i < j = Neut (NVar (NomVar (l , pred j)))
  | otherwise = Neut nv
subN i x (NStrAppendL s1 s2) =
  evalStrAppend (subN i x s1) (subV i x s2)
subN i x (NStrAppendR s1 s2) =
  evalStrAppend (subV i x s1) (subN i x s2)
subN i x (NStrEqL s1 s2) =
  evalStrEq (subN i x s1) (subV i x s2)
subN i x (NStrEqR s1 s2) =
  evalStrEq (subV i x s1) (subN i x s2)
subN i x (NIf b c1 c2) =
  evalIf (subN i x b) (subV i x c1) (subV i x c2)
subN i x (NCaseBool pT pt pf b) =
  evalCaseBool (subExtend i x pT) (subV i x pt) (subV i x pf) (subN i x b)
subN i x (NProj1 ab) = evalProj1 (subN i x ab)
subN i x (NProj2 ab) = evalProj2 (subN i x ab)
subN i x (NApp f a) =
  evalApp (subN i x f) (subV i x a)
subN i x (NDInterp d e) = evalDInterp (subN i x d) (subV i x e)

----------------------------------------------------------------------

subVs :: Var -> Val -> [VDef] -> [VDef]
subVs i x [] = []
subVs i x ((a , aT) : as) = (subV i x a , subV i x aT) : subVs (succ i) x as

----------------------------------------------------------------------

evalStrAppend :: Val -> Val -> Val
evalStrAppend (VQuotes s1) (VQuotes s2) = VQuotes (s1 ++ s2)
evalStrAppend (Neut s1) s2 = Neut $ NStrAppendL s1 s2
evalStrAppend s1 (Neut s2) = Neut $ NStrAppendR s1 s2
evalStrAppend _ _ = error "Ill-typed evaluation of (++)"

evalStrEq :: Val -> Val -> Val
evalStrEq (VQuotes s1) (VQuotes s2) = if (s1 == s2)
  then VTrue else VFalse
evalStrEq (Neut s1) s2 = Neut $ NStrEqL s1 s2
evalStrEq s1 (Neut s2) = Neut $ NStrEqR s1 s2
evalStrEq _ _ = error "Ill-typed evaluation of (==)"

evalIf :: Val -> Val -> Val -> Val
evalIf VTrue c1 c2 = c1
evalIf VFalse c1 c2 = c2
evalIf (Neut b) c1 c2 = Neut $ NIf b c1 c2
evalIf _ _ _ = error "Ill-typed evaluation of If"

evalCaseBool :: Bound Type -> Val -> Val -> Val -> Val
evalCaseBool pT pt pf VTrue = pt
evalCaseBool pT pt pf VFalse = pf
evalCaseBool pT pt pf (Neut b) = Neut $ NCaseBool pT pt pf b
evalCaseBool _ _ _ _ = error "Ill-typed evaluation of CaseBool"

evalProj1 :: Val -> Val
evalProj1 (VPair aT bT a b) = a
evalProj1 (Neut ab) = Neut $ NProj1 ab
evalProj1 _ = error "Ill-typed evaluation of Proj1"

evalProj2 :: Val -> Val
evalProj2 (VPair aT bT a b) = b
evalProj2 (Neut ab) = Neut $ NProj1 ab
evalProj2 _ = error "Ill-typed evaluation of Proj2"

evalApp :: Val -> Val -> Val
evalApp (VLam aT f) a = sub a f
evalApp (Neut f) a = Neut $ NApp f a
evalApp f a = error $
  "Ill-typed evaluation of App\n" ++
  "Function:\n" ++ show f ++ "\n" ++
  "Argument:\n" ++ show a

evalDInterp :: Val -> Val -> Val
evalDInterp VDUnit x = VUnit
evalDInterp VDRec x = x
evalDInterp (VDSum d e) x =
  vSum (evalDInterp d x) (evalDInterp e x)
evalDInterp (VDPi aT (Bound (ident , fD))) x =
  VPi aT (Bound (ident , evalDInterp fD x))
evalDInterp (VDSg aT (Bound (ident , fD))) x =
  VSg aT (Bound (ident , evalDInterp fD x))
evalDInterp (Neut d) x = Neut $ NDInterp d x
evalDInterp d x = error $
  "Ill-typed evaluation of DInterp"

----------------------------------------------------------------------

-- Substitute concrete values for variables in the context.
--
-- The values 'xs' are in context order.
foldSub :: [Val] -> Val -> Val
foldSub xs a = helper (reverse xs) a
  where
  helper :: [Val] -> Val -> Val
  helper [] a = a
  helper (x : xs) a = helper xs (subV (length xs) x a)

-- If G |- A and G,A |- B then G |- B.
sub :: Val -> Bound Val -> Val
sub x (Bound (_ , a)) = subV 0 x a

----------------------------------------------------------------------

-- A more efficient version would instead weaken only once, at the
-- 'NVar' leaves, by the number of binders were traversed on the way
-- to the leaf.
subExtend :: Var -> Val -> Bound Val -> Bound Val
subExtend i x (Bound (l , a)) = Bound (l , subV (succ i) (weakenVal0 x) a)

----------------------------------------------------------------------
type WeakenMonad = Reader Int

weakenNomVarM :: NomVar -> WeakenMonad NomVar
weakenNomVarM (NomVar (id , k)) = do
  isFree <- asks (<= k)
  trace' ("XXX weakenNomVarM XXX: " ++ show id) $
    return $ NomVar (id , if isFree then succ k else k)

-- XXX: I get type errors with this more generic signature:
{-
weakenBoundM :: (Data a , Typeable a) => Bound a -> WeakenMonad (Bound a)
-}
-- and similar when I try to make 'isBound' below work for 'Bound a'.
-- Looking at 'Spire.Canonical.Types' I see that only 'Bound Val'
-- occurs, but I would like to cover all 'Bound a', just to be safe.
-- How can I do this, without enumerating all ground values of 'a'?
--
-- XXX: how to write this in a simpler way, where here we just do
-- 'local (+1)', but not call 'weakenM' recursively?
weakenBoundM :: Bound Val -> WeakenMonad (Bound Val)
weakenBoundM (Bound (id , a)) = do
  wa <- local (+1) $ weakenM a
  trace' ("XXX weakenBoundM XXX: " ++ show a) $
    return (Bound (id , wa))

weakenM :: GenericM WeakenMonad
weakenM = everyWhereUntilM q t
  where
  isBound :: Bound Val -> Bool
  isBound = const True
  q :: GenericQ Bool
  q = mkQ False isBound
  t :: GenericM WeakenMonad
  t = mkM weakenBoundM `extM` weakenNomVarM

everyWhereUntilM :: Monad m => GenericQ Bool -> GenericM m -> GenericM m
everyWhereUntilM q t x =
  if q x
  then t x
  else t =<< gmapM (everyWhereUntilM q t) x

-- Weaken free variables, assuming we start under 'n' binders.
--
-- E.g., before going under more binders, all variables with value
-- greater than 'n' are considered free, and after going under 'k'
-- binders, all variables with values greater than 'n + k' are
-- considered free.
weakenVal :: Int -> Val -> Val
weakenVal n v = runReader (weakenM v) n

-- Weaken free variables, assuming we start under no binders.
weakenVal0 :: Val -> Val
weakenVal0 = weakenVal 0

-- Weakening tests
{-

weakenVal0 (Neut (NVar (NomVar ("x", 0))))
== (Neut (NVar (NomVar ("x", 1))))

weakenVal0 (VLam VUnit (Bound ("x" , (Neut (NVar (NomVar ("x", 0)))))))
== (VLam VUnit (Bound ("x" , (Neut (NVar (NomVar ("x", 0)))))))

weakenVal0 (VLam VUnit (Bound ("x" , (Neut (NVar (NomVar ("x", 1)))))))
== VLam VUnit (Bound ("x",Neut (NVar (NomVar ("x",2)))))

-}

----------------------------------------------------------------------
