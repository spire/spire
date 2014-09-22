{-# LANGUAGE
    GeneralizedNewtypeDeriving
  , ExistentialQuantification
  , DeriveDataTypeable
  , GADTs
  , Rank2Types
  , TypeFamilies
  , DataKinds
  , StandaloneDeriving
  , MultiParamTypeClasses
  , TypeSynonymInstances
  , FlexibleInstances
  #-}

module PReboundM where

import Prelude hiding ( foldl )
import Data.Typeable
import Data.Type.Equality
import Control.Monad
import qualified Data.Map    as M
import qualified Data.IntMap as IM

----------------------------------------------------------------------

type Sig m f a b = a -> m (f b)

class Monad m => Subst m f where
  vari :: Sig m f a a
  trav :: Sig m f a b -> f a -> m (f b)

newtype Bind f a = Bind (f (Maybe a))

----------------------------------------------------------------------

class Extendable a where
  extend :: String -> a

instance Extendable String where
  extend = id

instance Extendable a => Extendable (Maybe a) where
  extend s = Just (extend s)

----------------------------------------------------------------------

travBind :: Subst m f => Sig m f a b -> Bind f a -> m (Bind f b)
travBind s (Bind a) = return . Bind =<< trav (lift s) a

wkn :: Subst m f => Sig m f a (Maybe a)
wkn x = vari (Just x)

lift :: Subst m f => Sig m f a b -> Sig m f (Maybe a) (Maybe b)
lift s Nothing = vari Nothing
lift s (Just x) = trav wkn =<< (s x)

----------------------------------------------------------------------

sub :: Subst m f => Bind f a -> f a -> m (f a)
sub (Bind b) a = trav (bn a) b

bn :: Subst m f => f a -> Sig m f (Maybe a) a
bn x Nothing = return x
bn x (Just a) = vari a

----------------------------------------------------------------------

bind :: (Eq a,Subst m f) =>
  a -> f a -> m (Bind f a)
bind a x = return . Bind =<< trav (fr a) x

fr :: (Eq a,Subst m f) => a -> Sig m f a (Maybe a)
fr a b = if a == b
  then vari Nothing
  else vari (Just b)

----------------------------------------------------------------------

unbind :: Subst m f => Sig m f a b -> Bind f a -> (Sig m f (Maybe a) (Maybe b) , f (Maybe a))
unbind s (Bind a) = (lift s , a)

rebind :: f (Maybe a) -> Bind f a
rebind b = Bind b

----------------------------------------------------------------------