module Spire.Parser where

data Nat = Zero | Succ Nat
  deriving ( Eq, Show, Read )

data Type =
    Wkn Type
  | Unit | Bool
  | Arr Type Type
  | If Term Type Type
  deriving ( Eq, Show, Read )

data Term =
    Var Nat
  | WknV Term
  | TT | True | False
  | Lam Term
  | Not Term
  deriving ( Eq, Show, Read )

