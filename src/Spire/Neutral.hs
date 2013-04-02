module Spire.Neutral where

----------------------------------------------------------------------

type Var = Integer

data Val =
    VBool
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

evalProj1 :: Val -> Val
evalProj1 (VPair a b) = a
evalProj1 (Neut ab) = Neut (NProj1 ab)

evalProj2 :: Val -> Val
evalProj2 (VPair a b) = b
evalProj2 (Neut ab) = Neut (NProj1 ab)

evalApp :: Val -> Val -> Val
evalApp (VLam f) a = subV 0 a f
evalApp (Neut f) a = Neut (NApp f a)

----------------------------------------------------------------------

subV :: Var -> Val -> Val -> Val
subV i (VPi a b) x = VPi (subV i a x) (subV (succ i) b x)
subV i (VSg a b) x = VSg (subV i a x) (subV (succ i) b x)
subV i VBool x = VBool
subV i VTrue x = VTrue
subV i VFalse x = VFalse
subV i (VPair a b) x = VPair (subV i a x) (subV i b x)
subV i (VLam f) x = VLam (subV (succ i) f x)
subV i (Neut n) x = subNV i n x

subNV :: Var -> Neut -> Val -> Val
subNV i (NVar j) x | i == j = x
subNV i (NVar j) x = Neut (NVar j)
subNV i (NIf b c1 c2) x =
  evalIf (subNV i b x) (subV i c1 x) (subV i c2 x)
subNV i (NProj1 ab) x = evalProj1 (subNV i ab x)
subNV i (NProj2 ab) x = evalProj2 (subNV i ab x)
subNV i (NApp f a) x =
  evalApp (subNV i f x) (subV i a x)

----------------------------------------------------------------------