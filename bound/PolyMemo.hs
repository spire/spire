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
import System.Mem.StableName
import Data.Typeable
import Control.Monad
import Control.Monad.State
import qualified Data.IntMap as I

-- type k :--> v  = forall a. (Typeable a) => k a -> v a

type SM k v = I.IntMap [StableBind k v]

data StableBind k v = forall a. Typeable a =>
  SB (StableName (k a)) (v a)

-- type M k v = I.IntMap [StableBind k v]

-- data Bind k v = forall a. Typeable a =>
--   B (k a) (v a)

blookup :: Typeable a =>
  StableName (k a) -> [StableBind k v] -> Maybe (v a)
blookup sk = look
  where
  look :: [StableBind k v] -> Maybe (v a)
  look [] = Nothing
  look (SB sk' v : sbs) = undefined
  
-- memo :: (Eq a,Ord a) => [a] -> State Memo [a]
-- memo xs = do
--   Memo f <- get
--   undefined
--   -- case f xs of
--   --   _ -> undefined

-- type 