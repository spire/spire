module Spire.Neutral where

----------------------------------------------------------------------

type Var = Integer
type Type = Val

data Val =
    VUnit | VBool | VType
  | VPi Type Type
  | VSg Type Type
  | VRecord [Type]

  | VTT | VTrue | VFalse
  | VPair Val Val
  | VLam Val            -- Abstracted over (Neut(NVar 0))
  | VTuple [Val]
  | Neut Neut
  deriving ( Eq, Show, Read )

data Neut =
    NVar Var
  | NIf Neut Val Val
  | NCaseBool Type Val Val Neut
  | NProj1 Neut
  | NProj2 Neut
  | NApp Neut Val
  deriving ( Eq, Show, Read )

----------------------------------------------------------------------

evalIf :: Val -> Val -> Val -> Val
evalIf VTrue c1 c2 = c1
evalIf VFalse c1 c2 = c2
evalIf (Neut b) c1 c2 = Neut $ NIf b c1 c2
evalIf _ _ _ = error "Ill-typed evaluation of If"

evalCaseBool :: Val -> Val -> Val -> Val -> Val
evalCaseBool p pt pf VTrue = pt
evalCaseBool p pt pf VFalse = pf
evalCaseBool p pt pf (Neut b) = Neut $ NCaseBool p pt pf b
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
evalApp (VLam f) a = subV 0 a f
evalApp (Neut f) a = Neut $ NApp f a
evalApp _ _ = error "Ill-typed evaluation of App"

----------------------------------------------------------------------

subVs :: Var -> Val -> [Val] -> [Val]
subVs i x [] = []
subVs i x (a : as) = subV i x a : subVs (succ i) x as

subV :: Var -> Val -> Val -> Val
subV i x (VPi a b) = VPi (subV i x a) (subV (succ i) x b)
subV i x (VSg a b) = VSg (subV i x a) (subV (succ i) x b)
subV i x (VRecord as) = VRecord (subVs i x as)
subV i x VUnit = VUnit
subV i x VBool = VBool
subV i x VType = VType
subV i x VTT = VTT
subV i x VTrue = VTrue
subV i x VFalse = VFalse
subV i x (VPair a b)  = VPair (subV i x a) (subV i x b)
subV i x (VLam f) = VLam (subV (succ i) x f)
subV i x (VTuple as) = VTuple (subVs i x as)
subV i x (Neut n) = subN i x n

subN :: Var -> Val -> Neut -> Val
subN i x (NVar j) | i == j = x
subN i x (NVar j) | i < j = Neut (NVar (j - succ i))
subN i x (NVar j) = Neut (NVar j)
subN i x (NIf b c1 c2) =
  evalIf (subN i x b) (subV i x c1) (subV i x c2)
subN i x (NCaseBool p pt pf b) =
  evalCaseBool (subV (succ i) x p) (subV i x pt) (subV i x pf) (subN i x b)
subN i x (NProj1 ab) = evalProj1 (subN i x ab)
subN i x (NProj2 ab) = evalProj2 (subN i x ab)
subN i x (NApp f a) =
  evalApp (subN i x f) (subV i x a)

----------------------------------------------------------------------
