{-# LANGUAGE TypeSynonymInstances
           , MultiParamTypeClasses
           , FlexibleInstances
  #-}


module Rebound where
import Control.Monad

----------------------------------------------------------------------

data Name = Fr String | Bn Integer
  deriving (Show,Read,Eq,Ord)

newtype Bind a = Bind a
  deriving (Show,Read,Eq,Ord)

type Sig a = Name -> a

class Var a where
  var :: Sig a
  weaken :: a -> a

lift :: Var a => Sig a -> Sig a
lift s nm@(Bn 0) = var nm
lift s (Bn i) = weaken $ s (Bn (pred i))
lift s nm = weaken $ s nm

class Term a where
  term :: Var b => b -> a

class Subst a where
  trav :: (Term a , Var b) => Sig b -> a -> a

instance Var Name where
  var = id

  weaken (Bn i) = Bn (succ i)
  weaken nm = nm

travBind :: (Term a,Var b,Subst a) => Sig b -> Bind a -> Bind a
travBind s (Bind a) = Bind $ trav (lift s) a





-- unbind :: Subst m a => Sig m a -> Bind a -> (Sig m a , a)
-- unbind s (Bind a) = (lift s , a)

-- bind :: Subst m a => String -> a -> m (Bind a)
-- bind str a = return . Bind =<< trav (fr1 str) a

-- fr1 :: Subst m a => String -> Sig m a
-- fr1 str r (Fr str') | str == str' = return $ r (Bn 0)
-- fr1 str r nm = return (r nm)

-- sub :: Subst m a => Bind a -> a -> m a
-- sub (Bind b) a = trav (bn1 a) b

-- bn1 :: Subst m a => a -> Sig m a
-- bn1 a r (Bn 0) = return a
-- bn1 a r nm = return (r nm)

s2n :: String -> Name
s2n = Fr

n2s :: Name -> String
n2s (Fr str) = str
n2s (Bn i) = "x" ++ show i

----------------------------------------------------------------------