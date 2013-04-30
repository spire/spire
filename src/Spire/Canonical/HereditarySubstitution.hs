module Spire.Canonical.HereditarySubstitution where
import Spire.Canonical.Types

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
subV i x (VPair aT bT a b) =
  VPair (subV i x aT) (subExtend i x bT) (subV i x a) (subV i x b)
subV i x (VLam aT f) = VLam (subV i x aT) (subExtend i x f)
subV i x (VDefs as) = VDefs (subVs i x as)
subV i x d@VDUnit = d
subV i x d@VDRec = d
subV i x (VDSum d e) = VDSum (subV i x d) (subV i x e)
subV i x (VDProd d e) = VDProd (subV i x d) (subV i x e)
subV i x (VDPi aT fD) = VDPi (subV i x aT) (subExtend i x fD)
subV i x (VDSg aT fD) = VDSg (subV i x aT) (subExtend i x fD)
subV i x (Neut n) = subN i x n

subN :: Var -> Val -> Neut -> Val
subN i x (NVar (NomVar (l , j))) | i == j = x
subN i x (NVar (NomVar (l , j))) | i < j = Neut (NVar (NomVar (l , (j - succ i))))
subN i x (NVar j) = Neut (NVar j)
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

----------------------------------------------------------------------

sub :: Val -> Val -> Val
sub = subV 0

subs :: Val -> [VDef] -> [VDef]
subs = subVs 0

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
suB x (Bound (_ , a)) = sub x a

subExtend :: Var -> Val -> Bound Val -> Bound Val
subExtend i x (Bound (l , a)) = Bound (l , subV (succ i) x a)

----------------------------------------------------------------------