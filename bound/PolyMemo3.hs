{-# LANGUAGE
    DeriveFunctor
  , DeriveFoldable
  , DeriveTraversable
  , GeneralizedNewtypeDeriving
  , ExistentialQuantification
  , GADTs
  , TypeOperators
  #-}

module PolyMemo where

import Prelude hiding ( foldl )
import Generics.RepLib
import Data.Type.Equality
import Unsafe.Coerce
import Control.Monad
import Control.Monad.State

data Bind = forall a. (Eq a,Rep a) =>
  B [a] [a]

two :: [a] -> [a] -> [a]
two _ x = x

blookup :: (Eq a,Rep a) =>
  [a] -> [Bind] -> Maybe [a]
blookup j = look
  where
  look :: [Bind] -> Maybe [a]
  look [] = Nothing
  look (B k v : sbs) =
    case gcast k of
      Just k' -> if j == k'
        then case gcast v of
          Just v' -> Just (two k v')
          Nothing -> look sbs
        else look sbs
      _ -> look sbs
