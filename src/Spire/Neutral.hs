module Spire.Neutral where

----------------------------------------------------------------------

type Var = Int
type Type = Val
type Ctx = [Type]

data Val =
    VBool | VType
  | VPi Val Val
  | VSg Val Val

  | VTrue | VFalse
  | VPair Val Val
  | VLam Val
  | Neut Neut
  deriving ( Eq, Show, Read )

data Neut =
    NVar Var
  | NIf Neut Val Val
  | NProj1 Neut
  | NProj2 Neut
  | NApp Neut Val
  deriving ( Eq, Show, Read )

----------------------------------------------------------------------

evalIf :: Val -> Val -> Val -> Val
evalIf VTrue c1 c2 = c1
evalIf VFalse c1 c2 = c2
evalIf (Neut b) c1 c2 = Neut (NIf b c1 c2)
evalIf _ _ _ = error "Ill-typed evaluation of If"

evalProj1 :: Val -> Val
evalProj1 (VPair a b) = a
evalProj1 (Neut ab) = Neut (NProj1 ab)
evalProj1 _ = error "Ill-typed evaluation of Proj1"

evalProj2 :: Val -> Val
evalProj2 (VPair a b) = b
evalProj2 (Neut ab) = Neut (NProj1 ab)
evalProj2 _ = error "Ill-typed evaluation of Proj2"

evalApp :: Val -> Val -> Val
evalApp (VLam f) a = subV 0 f a
evalApp (Neut f) a = Neut (NApp f a)
evalApp _ _ = error "Ill-typed evaluation of App"

----------------------------------------------------------------------

subV :: Var -> Val -> Val -> Val
subV i x (VPi a b) = VPi (subV i x a) (subV (succ i) x b)
subV i x (VSg a b) = VSg (subV i x a) (subV (succ i) x b)
subV i x VBool = VBool
subV i x VType = VType
subV i x VTrue = VTrue
subV i x VFalse = VFalse
subV i x (VPair a b)  = VPair (subV i x a) (subV i x b)
subV i x (VLam f) = VLam (subV (succ i) x f)
subV i x (Neut n) = subNV i x n

subNV :: Var -> Val -> Neut -> Val
subNV i x (NVar j) | i == j = x
subNV i x (NVar j) = Neut (NVar j)
subNV i x (NIf b c1 c2) =
  evalIf (subNV i x b) (subV i x c1) (subV i x c2)
subNV i x (NProj1 ab) = evalProj1 (subNV i x ab)
subNV i x (NProj2 ab) = evalProj2 (subNV i x ab)
subNV i x (NApp f a) =
  evalApp (subNV i x f) (subV i x a)

----------------------------------------------------------------------