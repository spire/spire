{-# LANGUAGE TypeSynonymInstances
           , MultiParamTypeClasses
           , FlexibleInstances
  #-}


module Expr where
import Control.Monad
import Control.Monad.Identity hiding ( lift )

----------------------------------------------------------------------

data Name a = Fr String | Bn Integer
  deriving (Show,Read,Eq,Ord)

newtype Bind a = Bind a
  deriving (Show,Read,Eq,Ord)

data Exp =
    TT | FF
  | Pair Exp Exp
  | App Exp Exp
  | Var (Name Exp)
  | Lam (Bind Exp)
  deriving (Show,Read,Eq,Ord)

type Var a = Name a -> a
type Sig m a = Var a -> Name a -> m a

class Monad m => Subst m a where
  trav :: Sig m a -> a -> m a

instance Subst Identity Exp where
  trav s (Var nm) = s Var nm
   -- Spine nm xs = elim (s Var nm) =<< trav s xs
  trav s TT = return TT
  trav s FF = return FF
  trav s (Pair a b) = do
    a' <- trav s a
    b' <- trav s b
    return $ App a' b'
  trav s (App f a) = do
    f' <- trav s f
    a' <- trav s a
    return $ App f' a'
  trav s (Lam b) = do
    b' <- travBind s b
    return $ Lam b'

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

idSig :: Subst m a => Sig m a
idSig r nm = return (r nm)

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
lift s r nm = trav wkn =<< s r nm

wkn :: Subst m a => Sig m a
wkn r (Bn i) = return $ r (Bn (succ i))
wkn r nm = return $ r nm

----------------------------------------------------------------------