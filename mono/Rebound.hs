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

type Var a = Name a -> a
type Sig m a = Var a -> Name a -> m a

class Monad m => Subst m a where
  trav :: Sig m a -> a -> m a

-- instance Subst a => Subst (Bind a) where
--   trav s (Bind a) = do
--     a' <- trav (lift s) a
--     undefined

travBind :: Subst m a => Sig m a -> Bind a -> m (Bind a)
travBind s (Bind a) = return . Bind =<< trav (lift s) a

unbind :: Subst m a => Sig m a -> Bind a -> (Sig m a , a)
unbind s (Bind a) = (lift s , a)

bind :: Subst m a => String -> a -> m (Bind a)
bind str a = return . Bind =<< trav (fr1 str) a

fr1 :: Subst m a => String -> Sig m a
fr1 str r (Fr str') | str == str' = return $ r (Bn 0)
fr1 str r nm = return (r nm)

sub :: Subst m a => Bind a -> a -> m a
sub (Bind b) a = trav (bn1 a) b

bn1 :: Subst m a => a -> Sig m a
bn1 a r (Bn 0) = return a
bn1 a r nm = return (r nm)

lift :: Subst m a => Sig m a -> Sig m a
lift s r nm@(Bn 0) = return $ r nm
lift s r (Bn i) = trav wkn =<< s r (Bn (pred i))
lift s r nm = trav wkn =<< s r nm

wkn :: Subst m a => Sig m a
wkn r (Bn i) = return $ r (Bn (succ i))
wkn r nm = return $ r nm

s2n :: String -> Name a
s2n = Fr

n2s :: Name a -> String
n2s (Fr str) = str
n2s (Bn i) = "x" ++ show i

----------------------------------------------------------------------