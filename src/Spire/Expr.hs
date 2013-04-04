module Spire.Expr where
import Spire.Neutral

----------------------------------------------------------------------

data Expr =
    EBool | EType
  | EPi Expr Expr
  | ESg Expr Expr

  | ETrue | EFalse
  | EPair Expr Expr
  | ELam Expr

  | EVar Var
  | EIf Expr Expr Expr
  | EProj1 Expr
  | EProj2 Expr
  | EApp Expr Expr
  deriving ( Eq, Show, Read )

----------------------------------------------------------------------

embed :: Val -> Expr
embed VBool = EBool
embed VType = EType
embed (VPi a b) = EPi (embed a) (embed b)
embed (VSg a b) = ESg (embed a) (embed b)
embed VTrue = ETrue
embed VFalse = EFalse
embed (VPair a b) = EPair (embed a) (embed b)
embed (VLam f) = ELam (embed f)
embed (Neut n) = embedN n

embedN :: Neut -> Expr
embedN (NVar i) = EVar i
embedN (NIf b c1 c2) = EIf (embedN b) (embed c1) (embed c2)
embedN (NProj1 ab) = EProj1 (embedN ab)
embedN (NProj2 ab) = EProj2 (embedN ab)
embedN (NApp f a) = EApp (embedN f) (embed a)

----------------------------------------------------------------------

eval :: Expr -> Val
eval EBool = VBool
eval EType = VType
eval (EPi a b) = VPi (eval a) (eval b)
eval (ESg a b) = VSg (eval a) (eval b)
eval ETrue = VTrue
eval EFalse = VFalse
eval (EPair a b) = VPair (eval a) (eval b)
eval (ELam f) = VLam (eval f)
eval (EVar i) = Neut (NVar i)
eval (EIf b c1 c2) = evalIf (eval b) (eval c1) (eval c2)
eval (EProj1 ab) = evalProj1 (eval ab)
eval (EProj2 ab) = evalProj2 (eval ab)
eval (EApp f a) = evalApp (eval f) (eval a)

----------------------------------------------------------------------