{-# LANGUAGE
    GeneralizedNewtypeDeriving
  , ExistentialQuantification
  , DeriveDataTypeable
  , GADTs
  , Rank2Types
  , TypeFamilies
  , DataKinds
  , StandaloneDeriving
  , TypeSynonymInstances
  , FlexibleInstances
  #-}

module PRebound where

import Prelude hiding ( foldl )
import Data.Typeable
import Data.Type.Equality
import Control.Monad
import qualified Data.Map    as M
import qualified Data.IntMap as IM
import System.IO.Unsafe

----------------------------------------------------------------------

data Param (a :: *) :: * where
  String' :: Param String
  Maybe' :: Param a -> Param (Maybe a)
deriving instance Show (Param a)

instance TestEquality Param where
  testEquality String' String' = Just Refl
  testEquality (Maybe' a) (Maybe' b) = case testEquality a b of
    Just Refl -> Just Refl
    Nothing -> Nothing
  testEquality _ _ = Nothing

----------------------------------------------------------------------

type Sig f a b = a -> f b

class Subst f where
  vari :: Sig f a a
  trav :: Sig f a b -> f a -> f b

newtype Bind f a = Bind (f (Maybe a))

----------------------------------------------------------------------

class S2N a where
  s2n :: String -> a

instance S2N String where
  s2n = id

instance S2N a => S2N (Maybe a) where
  s2n s = Just (s2n s)

----------------------------------------------------------------------

travBind :: Subst f => Sig f a b -> Bind f a -> Bind f b
travBind s (Bind a) = Bind $ trav (lift s) a

wkn :: Subst f => Sig f a (Maybe a)
wkn x = vari (Just x)

lift :: Subst f => Sig f a b -> Sig f (Maybe a) (Maybe b)
lift s Nothing = vari Nothing
lift s (Just x) = trav wkn (s x)

----------------------------------------------------------------------

sub :: Subst f => Bind f a -> f a -> f a
sub (Bind b) a = trav (bn a) b

bn :: Subst f => f a -> Sig f (Maybe a) a
bn x Nothing = x
bn x (Just a) = vari a

----------------------------------------------------------------------

bind :: (Eq a,Subst f) =>
  a -> f a -> Bind f a
bind a x = Bind $ trav (fr a) x

fr :: (Eq a,Subst f) => a -> Sig f a (Maybe a)
fr a b = if a == b
  then vari Nothing
  else vari (Just b)

----------------------------------------------------------------------

unbind :: Subst f => Sig f a b -> Bind f a -> (Sig f (Maybe a) (Maybe b) , f (Maybe a))
unbind s (Bind a) = (lift s , a)

rebind :: Subst f => f (Maybe a) -> Bind f a
rebind b = Bind b

----------------------------------------------------------------------