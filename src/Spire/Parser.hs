module Spire.Parser where

data Nat = Zero | Succ Nat
  deriving ( Eq, Show, Read)

data Type = Unit | Bool
  deriving ( Eq, Show, Read )

data Term =
    Var Nat
  | TT | True | False
  | If Term Term Term
  deriving ( Eq, Show, Read )

