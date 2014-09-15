{-# LANGUAGE
    DeriveFunctor
  , DeriveFoldable
  , DeriveTraversable
  , GeneralizedNewtypeDeriving
  , ExistentialQuantification
  , DeriveDataTypeable
  , GADTs
  , TypeOperators
  #-}

module PolyMemo6 where

import Prelude hiding ( foldl )
import Data.Typeable
import Data.Type.Equality
import Control.Monad
import Control.Monad.State

type Rev f a = f a -> Maybe (f a)

data Memo f = forall a. (Typeable a , Eq a) => Memo (Rev f a)

-- reverseM :: (Typeable a , Eq a) =>
--   [a] -> State (Memo []) [a]
-- reverseM xs = do
--   Memo f <- get
--   case cast xs of
--     Just xs' -> case f xs' of
--       Just ys -> case cast ys of
--         Just ys' -> return ys'
--         Nothing -> error "Inconsistent type casting"
--       Nothing -> do
--         let ys = reverse xs'
--         let g = \xs'' -> if xs' == xs'' then Just ys else f xs'
--         put (Memo g)
--         case cast ys of
--           Just ys' -> return ys'
--           Nothing -> error "Inconsistent type casting"
--     Nothing -> error "Inconsistent type casting"

emptyMemo :: Memo []
emptyMemo = Memo (\xs -> Just [False])
