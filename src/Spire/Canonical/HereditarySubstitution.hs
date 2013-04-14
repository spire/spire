module Spire.Canonical.HereditarySubstitution where
import Spire.Canonical.Types

----------------------------------------------------------------------

{-
Do not explicitly inspect `Bound' variables in `subV' and `subN'.
Instead, use helper functions like `subExtend', which correctly
increment the De Bruijn index.
-}

subV :: Var -> Val -> Val -> Val
subV i x (VPi aT bT) = VPi (subV i x aT) (subExtend i x bT)
subV i x (VSg aT bT) = VSg (subV i x aT) (subExtend i x bT)
subV i x (VPair a b) = VPair (subV i x a) (subV i x b)
subV i x (VLam aT f) = VLam (subV i x aT) (subExtend i x f)
subV i x (VDefs as) = VDefs (subVs i x as)
subV i x (Neut n) = subN i x n
subV _ _ a = a

subN :: Var -> Val -> Neut -> Val
subN i x (NVar j) | i == j = x
subN i x (NVar j) | i < j = Neut (NVar (j - succ i))
subN i x (NVar j) = Neut (NVar j)
subN i x (NIf b c1 c2) =
  evalIf (subN i x b) (subV i x c1) (subV i x c2)
subN i x (NCaseBool pT pt pf b) =
  evalCaseBool (subExtend i x pT) (subV i x pt) (subV i x pf) (subN i x b)
subN i x (NProj1 ab) = evalProj1 (subN i x ab)
subN i x (NProj2 ab) = evalProj2 (subN i x ab)
subN i x (NApp f a) =
  evalApp (subN i x f) (subV i x a)

----------------------------------------------------------------------

sub :: Val -> Val -> Val
sub = subV 0

subs :: Val -> [VDef] -> [VDef]
subs = subVs 0

subVs :: Var -> Val -> [VDef] -> [VDef]
subVs i x [] = []
subVs i x ((a , aT) : as) = (subV i x a , subV i x aT) : subVs (succ i) x as

----------------------------------------------------------------------

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
evalProj1 (VPair a b) = a
evalProj1 (Neut ab) = Neut $ NProj1 ab
evalProj1 _ = error "Ill-typed evaluation of Proj1"

evalProj2 :: Val -> Val
evalProj2 (VPair a b) = b
evalProj2 (Neut ab) = Neut $ NProj1 ab
evalProj2 _ = error "Ill-typed evaluation of Proj2"

evalApp :: Val -> Val -> Val
evalApp (VLam aT f) a = suB a f
evalApp (Neut f) a = Neut $ NApp f a
evalApp f a = error $
  "Ill-typed evaluation of App\n" ++
  "Function:\n" ++ show f ++ "\n" ++
  "Argument:\n" ++ show a

foldSub :: [Val] -> Val -> Val
foldSub xs a = helper (reverse xs) a
  where
  helper :: [Val] -> Val -> Val
  helper [] a = a
  helper (x : xs) a = helper xs (subV (length xs) x a)

----------------------------------------------------------------------

suB :: Val -> Bound Val -> Val
suB x (Bound a) = sub x a

subExtend :: Var -> Val -> Bound Val -> Bound Val
subExtend i x (Bound a) = Bound $ subV (succ i) x a

----------------------------------------------------------------------