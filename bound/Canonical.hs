{-# LANGUAGE
    DeriveFunctor
  , DeriveFoldable
  , DeriveTraversable
  #-}

module Canonical where

import Prelude hiding ( foldl )
import Data.Foldable
import Data.Traversable
import Control.Monad
import Prelude.Extras
import Bound

data Val a =
    TT
  | FF
  | Lam (Scope () Val a)
  | Neut a (Spine (Elim (Val a)))
  deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable)

data Spine a = Id | Pipe (Spine a) a
  deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable)

data Elim a =
    App a
  | If a a
  deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable)

instance Eq1   Val
instance Ord1  Val
instance Show1 Val
instance Read1 Val

elim :: Val a -> Elim (Val a) -> Val a
elim TT (If ct cf) = ct
elim FF (If ct cf) = cf
elim (Lam b) (App a) = instantiate1 a b
elim (Neut a xs) x = Neut a (Pipe xs x)
elim _ _ = error "Ill-typed evaluation"

instance Monad Val where
  return a = Neut a Id
  TT >>= f = TT
  FF >>= f = FF
  Lam b >>= f = Lam (b >>>= f)
  Neut a xs >>= f = foldl elim (f a) (fmap (\ e -> (fmap (>>= f) e)) xs)

lam :: Eq a => a -> Val a -> Val a
lam nm b = Lam (abstract1 nm b)

myNot :: Val String
myNot = lam "x" $ Neut "x" $ Pipe Id $ If FF TT

myFF :: Val String
myFF = myNot `elim` App TT