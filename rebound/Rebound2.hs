{-# LANGUAGE TypeSynonymInstances
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
  #-}


module Rebound2 where
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

instance Var Name where
  var = id
  weaken (Bn i) = Bn (succ i)
  weaken nm = nm

----------------------------------------------------------------------

travBind :: (Term a b,Subst a) => Sig b -> Bind a -> Bind a
travBind s (Bind a) = Bind $ trav (lift s) a

----------------------------------------------------------------------

class Var b => Term a b where
  term :: b -> a

class Subst a where
  trav :: (Var b , Term a b) => Sig b -> a -> a

----------------------------------------------------------------------

-- unbind :: Subst m a => Sig m a -> Bind a -> (Sig m a , a)
-- unbind s (Bind a) = (lift s , a)

bind :: (Term a Name, Subst a) => String -> a -> Bind a
bind str a = Bind $ trav (fr1 str :: Sig Name) a

fr1 :: Var a => String -> Sig a
fr1 str (Fr str') | str == str' = var (Bn 0)
fr1 str nm = var nm

-- sub :: Subst m a => Bind a -> a -> m a
-- sub (Bind b) a = trav (bn1 a) b

-- bn1 :: Subst m a => a -> Sig m a
-- bn1 a r (Bn 0) = return a
-- bn1 a r nm = return (r nm)

var' :: Var a => String -> a
var' = var . s2n

s2n :: String -> Name
s2n = Fr

n2s :: Name -> String
n2s (Fr str) = str
n2s (Bn i) = "x" ++ show i

----------------------------------------------------------------------