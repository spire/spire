{-# LANGUAGE
             MultiParamTypeClasses
           , KindSignatures
  #-}


module Rebound where
import Control.Monad

----------------------------------------------------------------------

data Name = Fr String | Bn Int Int
  deriving (Show,Read,Eq,Ord)

type Sig m a = Name -> m a

class Monad m => Subst m a where
  vari :: Sig m a
  trav :: Sig m a -> a -> m a

----------------------------------------------------------------------

class Pattern f where
  bindP :: f a -> Int -> Maybe a
  freeP :: f String -> String -> Maybe Int

newtype Bind (f :: * -> *) a = Bind a
  deriving (Show,Read,Eq,Ord)

----------------------------------------------------------------------

travBind :: Subst m a => Sig m a -> Bind f a -> m (Bind f a)
travBind s (Bind a) = return . Bind =<< trav (lift s) a

unbind :: (Pattern f , Subst m a) => Sig m a -> Bind f a -> (Sig m a , a)
unbind s (Bind a) = (lift s , a)

bind :: (Pattern f , Subst m a) =>
  f String -> a -> m (Bind f a)
bind str a = return . Bind =<< trav (fr str) a

fr :: (Pattern f , Subst m a) => f String -> Sig m a
fr pat nm@(Fr str) = case freeP pat str of
  Just o -> vari (Bn 0 o)
  Nothing -> vari nm
fr pat nm = vari nm

sub :: (Pattern f , Subst m a) => Bind f a -> f a -> m a
sub (Bind b) a = trav (bn a) b

bn :: (Pattern f , Subst m a) => f a -> Sig m a
bn pat (Bn 0 o) = case bindP pat o of
  Just a -> return a
  Nothing -> error "Pattern index out of bounds"
bn pat nm = vari nm

lift :: Subst m a => Sig m a -> Sig m a
lift s nm@(Bn 0 _) = vari nm
lift s (Bn i o) = trav wkn =<< s (Bn (pred i) o)
lift s nm = trav wkn =<< s nm

wkn :: Subst m a => Sig m a
wkn (Bn i o) = vari (Bn (succ i) o)
wkn nm = vari nm

s2n :: String -> Name
s2n = Fr

n2s :: Name -> String
n2s (Fr str) = str
n2s (Bn i o) = "x-" ++ show i ++ "-" ++ show o

----------------------------------------------------------------------

type Bind1 = Bind One
type Bind2 = Bind Two
type Bind3 = Bind Three

sub1 t x = sub t $ One x
sub2 t x1 x2 = sub t $ Two (x1,x2)
sub3 t x1 x2 x3 = sub t $ Three (x1,x2,x3)

bind1 nm = bind $ One nm
bind2 nm1 nm2 = bind $ Two (nm1,nm2)
bind3 nm1 nm2 nm3 = bind $ Three (nm1,nm2,nm3)

newtype One a = One a
  deriving (Show,Read,Eq,Ord)

instance Pattern One where
  bindP (One a) 0 = Just a
  bindP (One a) _ = Nothing

  freeP (One a) x | a == x = Just 0
  freeP (One a) x = Nothing

newtype Two a = Two (a , a)
  deriving (Show,Read,Eq,Ord)

instance Pattern Two where
  bindP (Two (a , b)) 0 = Just a
  bindP (Two (a , b)) 1 = Just b
  bindP (Two (a , b)) _ = Nothing

  freeP (Two (a , b)) x | a == x = Just 0
  freeP (Two (a , b)) x | b == x = Just 1
  freeP (Two (a , b)) x = Nothing

newtype Three a = Three (a , a , a)
  deriving (Show,Read,Eq,Ord)

instance Pattern Three where
  bindP (Three (a , b , c)) 0 = Just a
  bindP (Three (a , b , c)) 1 = Just b
  bindP (Three (a , b , c)) 2 = Just c
  bindP (Three (a , b , c)) _ = Nothing

  freeP (Three (a , b , c)) x | a == x = Just 0
  freeP (Three (a , b , c)) x | b == x = Just 1
  freeP (Three (a , b , c)) x | c == x = Just 2
  freeP (Three (a , b , c)) x = Nothing

----------------------------------------------------------------------

