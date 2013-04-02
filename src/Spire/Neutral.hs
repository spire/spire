module Spire.Neutral where

----------------------------------------------------------------------

type Var = Integer

data Val =
    Bool
  | Pi Val Val
  | Sg Val Val

  | TT | FF
  | Pair Val Val
  | Lam Val
  | NVal NVal
  deriving ( Eq, Show, Read )

data NVal =
    Var Var
  | App NVal Val
  | Proj1 NVal
  | Proj2 NVal
  | If NVal Val Val
  deriving ( Eq, Show, Read )

----------------------------------------------------------------------

subV :: Var -> Val -> Val -> Val
subV i (Pi a b) x = Pi (subV i a x) (subV (succ i) b x)
subV i (Sg a b) x = Sg (subV i a x) (subV (succ i) b x)
subV i Bool x = Bool
subV i TT x = TT
subV i FF x = FF
subV i (Pair a b) x = Pair (subV i a x) (subV i b x)
subV i (Lam f) x = Lam (subV (succ i) f x)
subV i (NVal n) x = subNV i n x

subNV :: Var -> NVal -> Val -> Val
subNV i (Var j) x | i == j = x
subNV i (Var j) x = NVal (Var j)
subNV i (App f a) x =
  let a' = subV i a x in
  case subNV i f x of
  Lam f' -> subV 0 a' f'
  NVal f' -> NVal (App f' a')
subNV i (Proj1 ab) x =
  case subNV i ab x of
  Pair a b -> a
  NVal ab' -> NVal (Proj1 ab')
subNV i (Proj2 ab) x =
  case subNV i ab x of
  Pair a b -> b
  NVal ab' -> NVal (Proj2 ab')
subNV i (If b c1 c2) x =
  let
    c1' = subV i c1 x
    c2' = subV i c2 x
  in case subNV i b x of
  TT -> c1'
  FF -> c2'
  NVal b' -> NVal (If b' c1' c2')

----------------------------------------------------------------------