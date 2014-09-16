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

----------------------------------------------------------------------

type Rev a = [a] -> Maybe [a]
type ForallRev = (Typeable a , Eq a) => Rev a
data Memo = Memo ForallRev

----------------------------------------------------------------------

memoRev :: (Typeable a,Eq a) => ForallRev -> [a] -> [a] -> ForallRev
memoRev f xs ys zs = case cast (xs , ys) of
  Just (xs' , ys') -> if xs' == zs then Just ys' else f zs
  Nothing -> f zs

reverseM :: (Typeable a , Eq a) =>
  [a] -> State Memo [a]
reverseM xs = do
  Memo f <- get
  case f xs of
    Just ys -> return ys
    Nothing -> do
      let ys = slowReverse xs
      put (Memo (memoRev f xs ys))
      return ys

reversesM :: (Typeable a , Eq a) =>
  Int -> [a] -> State Memo [a]
reversesM n xs | n < 1 = reverseM xs
reversesM n xs = reverseM =<< reversesM (pred n) xs

----------------------------------------------------------------------

emptyMemo :: Memo
emptyMemo = Memo (const Nothing)

idMemo :: Memo
idMemo = Memo Just

----------------------------------------------------------------------

slowReverse' :: Int -> [a] -> [a]
slowReverse' n xs | n < 1 = reverse xs
slowReverse' n xs = slowReverse' (pred n) xs

slowReverse = slowReverse' 10000000

----------------------------------------------------------------------
