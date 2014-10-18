{-# LANGUAGE
    TypeSynonymInstances
  , FlexibleInstances
  #-}

module Spire.Bound where
import Bound
import qualified Bound.Scope.Simple as S
import Data.Traversable

----------------------------------------------------------------------

data Three = One | Two | Three
  deriving (Show,Read,Eq,Ord,Enum)

----------------------------------------------------------------------

type Bind = Scope
type Nom = ()
type Nom2 = Bool
type Nom3 = Three

var :: Monad m => a -> m a
var = return

----------------------------------------------------------------------

(#) :: Monad f => (f (Var b (f a)) -> c) -> f a -> c
f # a = f (return (F a))
{-# INLINE (#) #-}

(#~) :: Monad f => (Var b (f a) -> c) -> a -> c
f #~ b = f (F (return b))
{-# INLINE (#~) #-}

(##) :: Monad f => (Scope b f (Var b' (f a)) -> c) -> Scope b f a -> c
f ## b = f (shiftS b)
{-# INLINE (##) #-}

f ### b = f (shiftS (shiftS b))
{-# INLINE (###) #-}

f #### b = f (shiftS (shiftS (shiftS b)))
{-# INLINE (####) #-}

(#!) :: Monad f => (f (Var b (f a)) -> c) -> b -> c
f #! b = f (return (B b))
{-# INLINE (#!) #-}

f #!! b = f (return (F (return (B b))))
{-# INLINE (#!!) #-}

f #!!! b = f (return (F (return (F (return (B b))))))
{-# INLINE (#!!!) #-}

(#|) :: Monad f => (Var b (f a) -> c) -> b -> c
f #| b = f (B b)
{-# INLINE (#|) #-}

shiftS :: Monad f => Scope b f a -> Scope b f (Var b' (f a))
shiftS b = b >>>= return . F . return
{-# INLINE shiftS #-}

----------------------------------------------------------------------

var1 :: ()
var1 = ()

vars2 :: (Bool , Bool)
vars2 = (True , False)

vars3 :: (Three , Three , Three)
vars3 = (One , Two , Three)

locals1 :: (() -> a) -> a
locals1 f = f var1
bind1 f = locals1 $ \ x -> Scope (f x)

locals2 :: (Bool -> Bool -> a) -> a
locals2 f = uncurry f vars2
bind2 f = locals2 $ \ x y -> Scope (f x y)

locals3 :: (Three -> Three -> Three -> a) -> a
locals3 f = let (x,y,z) = vars3 in f x y z
bind3 f = locals3 $ \ x y z -> Scope (f x y z)

----------------------------------------------------------------------

bind0 :: Monad f => f a -> Scope b f a
bind0 = abstract (const Nothing)

abs1 (x , b) = abstract1 x b

abstract2 :: (Monad f, Eq a) => (a , a) -> f a -> Scope Bool f a
abstract2 (x , y) = abstract $ \b ->
  if x == b then Just True else
  if y == b then Just False else Nothing
abs2 (x , y , b) = abstract2 (x , y) b

abstract3 :: (Monad f, Eq a) => (a , a , a) -> f a -> Scope Three f a
abstract3 (x1 , x2 , x3) = abstract $ \b ->
  if x1 == b then Just One else
  if x2 == b then Just Two else
  if x3 == b then Just Three else Nothing
abs3 (x , y , z , b) = abstract3 (x , y , z) b

----------------------------------------------------------------------

instantiate2 :: Monad f => (f a , f a) -> Scope Bool f a -> f a
instantiate2 (x , y) = instantiate $ \ b -> if b then x else y

instantiate3 :: Monad f => (f a , f a , f a) -> Scope Three f a -> f a
instantiate3 (x , y , z) = instantiate $ \ t -> case t of
  One -> x ; Two -> y ; Three -> z

----------------------------------------------------------------------

unbind :: Monad m =>
  (a -> m a') -> S.Scope b f a -> ((Var b a -> m (Var b a')) , f (Var b a))
unbind f b = (Data.Traversable.mapM f , S.fromScope b)

----------------------------------------------------------------------

class Binder b where
  bound :: b -> String

class Free a where
  free :: String -> a 
  captured :: a -> String

instance Free String where
  free = id
  captured = id

instance (Binder b , Free a) => Free (Var b a) where
  free = F . free
  captured (B b) = bound b
  captured (F a) = captured a

instance Binder () where
  bound () = "x"

instance Binder Bool where
  bound True = "x"
  bound False = "y"

instance Binder Three where
  bound One = "x"
  bound Two = "y"
  bound Three = "z"

----------------------------------------------------------------------

liftScope :: (Monad m , Free a) =>
  (m (Var b a) -> f (Var b a)) -> Scope b m a -> S.Scope b f a
liftScope f = S.toScope . f . fromScope

----------------------------------------------------------------------