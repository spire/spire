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
import Control.Monad
import Control.Monad.State

data Bind = forall a. (Eq a,Typeable a) =>
  B [a] [a]

blookup :: (Eq a,Typeable a) =>
  [a] -> [Bind] -> Maybe [a]
blookup k = look
  where
  look :: [Bind] -> Maybe [a]
  look [] = Nothing
  look (B k' v : sbs) =
    case eqT of
      Just p -> look sbs
      Nothing -> look sbs
      --   if k == k'
      --   then case eqT of
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