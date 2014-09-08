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

module PolyMemo where

import Prelude hiding ( foldl )
import Data.Typeable
import Data.Type.Equality
import Unsafe.Coerce
import Control.Monad
import Control.Monad.State

data Bind = forall a. (Eq a,Typeable a) =>
  B [a] [a]

-- meq :: forall a b. (Typeable a, Typeable b) => a -> b -> Maybe (a :=: b)
-- meq a b = if typeOf a == typeOf b
--       then Just $ unsafeCoerce Refl
--       else Nothing

meq :: (Typeable a, Typeable b) => f a -> f b -> Maybe (a :=: b)
meq a b = if typeOf1 a == typeOf1 b
      then Just $ unsafeCoerce Refl
      else Nothing

blookup :: (Eq a,Typeable a) =>
  [a] -> [Bind] -> Maybe [a]
blookup k = look
  where
  look :: [Bind] -> Maybe [a]
  look [] = Nothing
  look (B k' v : sbs) =
    case meq k k' of
      _ -> undefined
      -- Just Refl -> if k == k'
      --   then case meq k' v of
      --     Just Refl -> Just v
      --     Nothing -> look sbs
      --   else look sbs
      -- Nothing -> look sbs

    -- case meq k k' of
    --   Just Refl -> if k == k'
    --     then case meq k' v of
    --       Just Refl -> Just v
    --       Nothing -> look sbs
    --     else look sbs
    --   Nothing -> look sbs
  
-- memo :: (Eq a,Ord a) => [a] -> State Memo [a]
-- memo xs = do
--   Memo f <- get
--   undefined
--   -- case f xs of
--   --   _ -> undefined

-- type 