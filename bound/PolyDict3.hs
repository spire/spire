{-# LANGUAGE
    ExistentialQuantification
  , GADTs
  , ConstraintKinds
  , KindSignatures
  , MultiParamTypeClasses
  #-}

module PolyDict3 where

import Control.Monad
import Control.Monad.State

-- class Eq a => Memo (f :: * -> *) a where
--   memo :: f a -> Maybe (f a)

class Memo f where
  memo :: Eq a => f a -> Maybe (f a)

-- type Rev a = Dict (Eq a) -> [a] -> Maybe [a]

-- -- mreverse :: Eq a =>
-- --   [a] -> Rev a -> (Rev a , [a])
-- -- mreverse xs f = case f xs of
-- --   Just ys -> (f , ys)
-- --   Nothing -> let
-- --     ys = reverse xs
-- --     g = \xs' -> if xs' == xs
-- --       then Just ys
-- --       else f xs'
-- --     in (g , ys)

-- data Bind = forall a. Bind (Rev a)

-- reverseM ::
--   Dict (Eq a) -> [a] -> State Bind [a]
-- reverseM Dict xs = do
--   Bind f <- get
-- --   -- let (g , ys) = mreverse xs f
-- --   -- put g
--   case f Dict xs of
--     _ -> return xs
--   -- return xs

