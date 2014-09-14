{-# LANGUAGE
             MultiParamTypeClasses
           , KindSignatures
           , GADTs
           , KindSignatures
           , ExistentialQuantification
           , DataKinds
           , StandaloneDeriving
  #-}


module IRebound where

----------------------------------------------------------------------

data Nat = Z | S Nat
 deriving (Show,Read,Eq,Ord)

data Var n where
  Fr :: String -> Var n
  Bn :: Fin n -> Var n
deriving instance Show (Var n)
deriving instance Eq (Var n)
deriving instance Ord (Var n)

data Fin n where 
  Here :: Fin (S n)
  There :: Fin n -> Fin (S n)
deriving instance Show (Fin n)
deriving instance Eq (Fin n)
deriving instance Ord (Fin n)

type Sig (f :: Nat -> *) m n = Var m -> f n

class Subst f where
  vari :: Sig f n n
  trav :: Sig f m n -> f m -> f n

----------------------------------------------------------------------

-- class Pattern f where
--   bindP :: f a -> Int -> Maybe a
--   freeP :: f String -> String -> Maybe Int

newtype Bind f n = Bind (f (S n))
-- deriving instance Show (Bind f n)
-- deriving instance Eq (Bind f n)
-- deriving instance Ord (Bind f n)

----------------------------------------------------------------------

travBind :: Subst f => Sig f m n -> Bind f m -> Bind f n
travBind s (Bind a) = Bind $ trav (lift s) a

unbind :: Subst f => Sig f m n -> Bind f m -> (Sig f (S m) (S n) , f (S m))
unbind s (Bind a) = (lift s , a)

rebind :: Subst f => f (S m) -> Bind f m
rebind b = Bind b

bind :: Subst f =>
  String -> f n -> Bind f n
bind str a = Bind $ trav (fr str) a

fr :: Subst f => String -> Sig f n (S n)
fr str (Fr str') =
  if str == str'
  then vari $ Bn Here
  else vari $ Fr str'
fr str (Bn i) = vari $ Bn (There i)

sub :: Subst f => Bind f n -> f n -> f n
sub (Bind b) a = trav (bn a) b

bn :: Subst f => f n -> Sig f (S n) n
bn a (Bn Here) = a
bn a (Bn (There i)) = vari $ Bn i
bn a (Fr str) = vari $ Fr str

lift :: Subst f => Sig f m n -> Sig f (S m) (S n)
lift s (Bn Here) = vari (Bn Here)
lift s (Bn (There i)) = trav wkn $ s (Bn i)
lift s (Fr str) = trav wkn $ s (Fr str)

wkn :: Subst f => Sig f n (S n)
wkn (Bn i) = vari (Bn (There i))
wkn (Fr str) = vari (Fr str)

s2n :: String -> Var n
s2n = Fr

n2s :: Var n -> String
n2s (Fr str) = str
n2s (Bn i) = "x" ++ show i

----------------------------------------------------------------------

-- type Bind1 = Bind One
-- type Bind2 = Bind Two
-- type Bind3 = Bind Three

-- sub1 t x = sub t $ One x
-- sub2 t x1 x2 = sub t $ Two (x1,x2)
-- sub3 t x1 x2 x3 = sub t $ Three (x1,x2,x3)

-- bind1 nm = bind $ One nm
-- bind2 nm1 nm2 = bind $ Two (nm1,nm2)
-- bind3 nm1 nm2 nm3 = bind $ Three (nm1,nm2,nm3)

-- newtype One a = One a
--   deriving (Show,Read,Eq,Ord)

-- instance Pattern One where
--   bindP (One a) 0 = Just a
--   bindP (One a) _ = Nothing

--   freeP (One a) x | a == x = Just 0
--   freeP (One a) x = Nothing

-- newtype Two a = Two (a , a)
--   deriving (Show,Read,Eq,Ord)

-- instance Pattern Two where
--   bindP (Two (a , b)) 0 = Just a
--   bindP (Two (a , b)) 1 = Just b
--   bindP (Two (a , b)) _ = Nothing

--   freeP (Two (a , b)) x | a == x = Just 0
--   freeP (Two (a , b)) x | b == x = Just 1
--   freeP (Two (a , b)) x = Nothing

-- newtype Three a = Three (a , a , a)
--   deriving (Show,Read,Eq,Ord)

-- instance Pattern Three where
--   bindP (Three (a , b , c)) 0 = Just a
--   bindP (Three (a , b , c)) 1 = Just b
--   bindP (Three (a , b , c)) 2 = Just c
--   bindP (Three (a , b , c)) _ = Nothing

--   freeP (Three (a , b , c)) x | a == x = Just 0
--   freeP (Three (a , b , c)) x | b == x = Just 1
--   freeP (Three (a , b , c)) x | c == x = Just 2
--   freeP (Three (a , b , c)) x = Nothing

-- ----------------------------------------------------------------------

