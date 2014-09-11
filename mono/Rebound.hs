{-# LANGUAGE TypeSynonymInstances
           , MultiParamTypeClasses
           , FlexibleInstances
  #-}


module Rebound where
import Control.Monad

----------------------------------------------------------------------

data Name a = Fr String | Bn Integer
  deriving (Show,Read,Eq,Ord)

newtype Bind a = Bind a
  deriving (Show,Read,Eq,Ord)

type Sig m a = Name a -> m a

class Monad m => Subst m a where
  vari :: Name a -> m a
  trav :: Sig m a -> a -> m a

travBind :: Subst m a => Sig m a -> Bind a -> m (Bind a)
travBind s (Bind a) = return . Bind =<< trav (lift s) a

unbind :: Subst m a => Sig m a -> Bind a -> (Sig m a , a)
unbind s (Bind a) = (lift s , a)

bind :: Subst m a => String -> a -> m (Bind a)
bind str a = return . Bind =<< trav (fr1 str) a

fr1 :: Subst m a => String -> Sig m a
fr1 str (Fr str') | str == str' = vari (Bn 0)
fr1 str nm = vari nm

sub :: Subst m a => Bind a -> a -> m a
sub (Bind b) a = trav (bn1 a) b

bn1 :: Subst m a => a -> Sig m a
bn1 a (Bn 0) = return a
bn1 a nm = vari nm

lift :: Subst m a => Sig m a -> Sig m a
lift s nm@(Bn 0) = vari nm
lift s (Bn i) = trav wkn =<< s (Bn (pred i))
lift s nm = trav wkn =<< s nm

wkn :: Subst m a => Sig m a
wkn (Bn i) = vari (Bn (succ i))
wkn nm = vari nm

s2n :: String -> Name a
s2n = Fr

n2s :: Name a -> String
n2s (Fr str) = str
n2s (Bn i) = "x" ++ show i

----------------------------------------------------------------------