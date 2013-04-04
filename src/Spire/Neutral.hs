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

printV :: Val -> String
printV VBool = "Bool"
printV VType = "Type"
printV (VPi a b) =
  "Pi " ++
  printV a ++
  printV b
printV (VSg a b) =
  "Sg " ++
  printV a ++
  printV b
printV VTrue = "true"
printV VFalse = "false"
printV (VPair a b) =
  "( " ++ printV a ++
  " , " ++
  printV b ++ " )"
printV (VLam f) =
  "-> ( " ++
  printV f ++
  " )"
printV (Neut a) = printN a

printN :: Neut -> String
printN (NVar i) = show i
printN (NIf b c1 c2) =
  "if " ++ printN b ++
  " then " ++ printV c1 ++
  " else " ++ printV c2
printN (NProj1 ab) =
  "proj1 " ++ printN ab
printN (NProj2 ab) =
  "proj2 " ++ printN ab
printN (NApp f a) =
  printN f ++
  " $ " ++
  printV a

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
subV i x (Neut n) = subN i x n

subN :: Var -> Val -> Neut -> Val
subN i x (NVar j) | i == j = x
subN i x (NVar j) = Neut (NVar j)
subN i x (NIf b c1 c2) =
  evalIf (subN i x b) (subV i x c1) (subV i x c2)
subN i x (NProj1 ab) = evalProj1 (subN i x ab)
subN i x (NProj2 ab) = evalProj2 (subN i x ab)
subN i x (NApp f a) =
  evalApp (subN i x f) (subV i x a)

----------------------------------------------------------------------