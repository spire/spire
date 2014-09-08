{-# LANGUAGE TypeSynonymInstances
           , GeneralizedNewtypeDeriving
  #-}


module Expr where
import Control.Monad
import Control.Monad.State
import Name

----------------------------------------------------------------------

newtype Bind a = Bind a
  deriving (Show,Read,Eq,Ord)

data Exp =
    Var (Name Exp)
  | App Exp Exp
  | Pair Exp Exp
  | TT | FF
  deriving (Show,Read,Eq,Ord)

type Var a = Name a -> a
type Sig m a = Var a -> Name a -> m a

class Sub a where
  trav :: Monad m => Sig m a -> a -> m a

instance Sub Exp where
  trav s (Var nm) = s Var nm
   -- Spine nm xs = elim (s Var nm) =<< trav s xs
  trav s (App f a) = do
    f' <- trav s f
    a' <- trav s a
    return $ App f' a'

-- instance Sub a => Sub (Bind a) where
--   trav s (Bind a) = undefined

-- sub :: (Monad m,Sub a) => Bind a -> a -> a
-- sub (Bind t) a = trav 

-- sig :: (Monad m,Sub a) => a -> Var a -> Name a -> m a
-- sig a r (Bn 0) = return a
-- sig a r nm@(Bn i) = return (r nm)
-- sig a r nm@(Fr _ _) = return (r nm)

ren :: (Monad m,Sub a) => Sig m a -> Var a -> Name a -> m a
ren s r nm@(Bn 0) = r nm
ren s r nm = undefined

wkn :: (Monad m,Sub a) => Sig m a
wkn r (Bn i) = return $ r (Bn (succ i))
wkn r nm@(Fr _ _) = return $ r nm

-- weakenSub :: (Monad m,Sub a) => Int -> (Name a -> m a) -> Name a -> ma
-- weakenSub i s nm = undefined

----------------------------------------------------------------------