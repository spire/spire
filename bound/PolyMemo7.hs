{-# LANGUAGE
    DeriveFunctor
  , DeriveFoldable
  , DeriveTraversable
  , GeneralizedNewtypeDeriving
  , ExistentialQuantification
  , DeriveDataTypeable
  , GADTs
  , TypeOperators
  , RankNTypes
  #-}

module PolyMemo7 where

import Prelude hiding ( foldl )
import Data.Typeable
import Data.Type.Equality
import Control.Monad
import Control.Monad.State
import Prelude.Extras

type Rev a = [a] -> Maybe [a]

data Memo = Memo (forall a. Eq a => Rev a)

reverseM :: Eq a =>
  [a] -> State Memo [a]
reverseM xs = do
  Memo f <- get
  case f xs of
    Just ys -> return ys
    Nothing -> do
      let ys = reverse xs
      let g = \xs' -> if xs == xs' then Just ys else f xs'
      put (Memo g)
      return ys

    -- Just xs' -> case f xs' of
    --   Just ys -> case cast ys of
    --     Just ys' -> return ys'
    --     Nothing -> error "Inconsistent type casting"
    --   Nothing -> do
    --     let ys = reverse xs'
    --     let g = \xs'' -> if xs' == xs'' then Just ys else f xs'
    --     put (Memo g)
    --     case cast ys of
    --       Just ys' -> return ys'
    --       Nothing -> error "Inconsistent type casting"
    -- Nothing -> error "Inconsistent type casting"

emptyMemo :: Memo
emptyMemo = Memo (const Nothing)
