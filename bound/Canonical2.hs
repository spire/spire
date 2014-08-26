{-# LANGUAGE
    DeriveFunctor
  , DeriveFoldable
  , DeriveTraversable
  #-}

module Canonical2 where

import Prelude hiding ( foldl )
import Data.Foldable
import Data.Traversable
import Control.Monad
import Prelude.Extras
import Bound

data Val a =
    TT
  | FF
  | Pair (Val a) (Val a)
  | Lam (Scope () Val a)
  | Neut a (Spine (Elim Val (Val a)))
  deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable)

data Spine a = Id | Pipe (Spine a) a
  deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable)

data Elim f a =
    App a
  | Proj1
  | Proj2
  | If (Scope () f a) a a
  deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable)

instance Eq1   Val
instance Ord1  Val
instance Show1 Val
instance Read1 Val

elim :: Val a -> Elim Val (Val a) -> Val a
elim TT (If _P ct cf) = ct
elim FF (If _P ct cf) = cf
elim (Pair a b) Proj1 = a
elim (Pair a b) Proj2 = b
elim (Lam b) (App a) = instantiate1 a b
elim (Neut a xs) x = Neut a (Pipe xs x)
elim _ _ = error "Ill-typed evaluation"

instance Monad Val where
  return a = Neut a Id
  TT >>= f = TT
  FF >>= f = FF
  Lam b >>= f = Lam (b >>>= f)
  Pair a b >>= f = Pair (a >>= f) (b >>= f)
  Neut a xs >>= f = foldl elim (f a) (fmap (fmap (>>= f)) xs)

lam :: Eq a => a -> Val a -> Val a
lam nm b = Lam (abstract1 nm b)

myNot :: Val String
myNot = lam "x" $ Neut "x" $ Pipe Id $ If undefined FF TT

myFF :: Val String
myFF = myNot `elim` App TT