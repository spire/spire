{-# LANGUAGE
    ExistentialQuantification
  , GADTs
  #-}

module PolyDict where

import Control.Monad
import Control.Monad.State

type Rev a = [a] -> Maybe [a]

mreverse :: Eq a =>
  [a] -> Rev a -> (Rev a , [a])
mreverse xs f = case f xs of
  Just ys -> (f , ys)
  Nothing -> let
    ys = reverse xs
    g = \xs' -> if xs' == xs
      then Just ys
      else f xs'
    in (g , ys)

data Bind = forall a. (Eq a) =>
  B (Rev a)

reverseM :: Eq a =>
  [a] -> State (Rev a) [a]
reverseM xs = do
  f <- get
  let (g , ys) = mreverse xs f
  put g
  return ys

