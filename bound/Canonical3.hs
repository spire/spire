{-# LANGUAGE
    DeriveFunctor
  , DeriveFoldable
  , DeriveTraversable
  #-}

module Canonical3 where

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
  | Lam2 (Scope Bool Val a)
  | Neut a (Spine (Elim a))
  deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable)

data Spine a = Id | Pipe (Spine a) a
  deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable)

data Elim a =
    App (Val a)
  | Proj1
  | Proj2
  | If (Scope () Val a) (Val a) (Val a)
  deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable)

instance Eq1   Val
instance Ord1  Val
instance Show1 Val
instance Read1 Val

var :: a -> Val a
var a = Neut a Id

elim :: Val a -> Elim a -> Val a
elim TT (If _P ct cf) = ct
elim FF (If _P ct cf) = cf
elim (Pair a b) Proj1 = a
elim (Pair a b) Proj2 = b
elim (Lam b) (App a) = instantiate1 a b
elim (Neut a xs) x = Neut a (Pipe xs x)
elim _ _ = error "Ill-typed evaluation"

instance Monad Val where
  return = var
  TT >>= f = TT
  FF >>= f = FF
  Lam b >>= f = Lam (b >>>= f)
  Lam2 b >>= f = Lam2 (b >>>= f)
  Pair a b >>= f = Pair (a >>= f) (b >>= f)
  Neut nm xs >>= f = foldl elim (f nm) (fmap g xs)
    where
    g (App a) = App (a >>= f)
    g Proj1 = Proj1
    g Proj2 = Proj2
    g (If _P ct cf) = If (_P >>>= f) (ct >>= f) (cf >>= f)

lam :: Eq a => a -> Val a -> Val a
lam nm b = Lam (abstract1 nm b)

data Three = One | Two | Three
  deriving (Show,Read,Eq,Ord,Enum)

abstract2 :: (Monad f, Eq a) => (a , a) -> f a -> Scope Bool f a
abstract2 (x , y) = abstract $ \b ->
  if x == b then Just True else
  if y == b then Just False else Nothing

abstract3 :: (Monad f, Eq a) => (a , a , a) -> f a -> Scope Three f a
abstract3 (x1 , x2 , x3) = abstract $ \b ->
  if x1 == b then Just One else
  if x2 == b then Just Two else
  if x3 == b then Just Three else Nothing

bad :: Val String
bad = lam "x" $ lam "y" $ Pair (var "x") (var "y")

bad2 :: Val String
bad2 = lam "x" $ Pair (var "x") $ lam "y" $ Pair (var "x") (var "y")

next2 (Lam (Scope b)) = b
next2 _ = undefined

next (Lam b) = fromScope b
next _ = undefined

wut :: Val String
wut = Lam2 $ abstract2 ("x" , "y")  $ Pair (var "x") $ Pair (var "z") (var "y")

myNot :: Val String
myNot = lam "x" $ Neut "x" $ Pipe Id $ If undefined FF TT

myFF :: Val String
myFF = myNot `elim` App TT