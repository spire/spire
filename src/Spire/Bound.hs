module Spire.Bound where
import Bound

----------------------------------------------------------------------

data Three = One | Two | Three
  deriving (Show,Read,Eq,Ord,Enum)

----------------------------------------------------------------------

type Bind = Scope
type Nom = ()
type Nom2 = Bool
type Nom3 = Three

----------------------------------------------------------------------

abstract0 :: Monad f => f a -> Scope b f a
abstract0 = abstract (const Nothing)

abstract2 :: (Monad f, Eq a) => (a , a) -> f a -> Scope Bool f a
abstract2 (x , y) = abstract $ \b ->
  if x == b then Just True else
  if y == b then Just False else Nothing

abstract3 :: (Monad f, Eq a) => (a , a , a) -> f a -> Scope Three f a
abstract3 (x1 , x2 , x3) = abstract $ \b ->
  if x1 == b then Just One else
  if x2 == b then Just Two else
  if x3 == b then Just Three else Nothing

----------------------------------------------------------------------

instantiate2 :: Monad f => (f a , f a) -> Scope Bool f a -> f a
instantiate2 (x , y) = instantiate $ \ b -> if b then x else y

instantiate3 :: Monad f => (f a , f a , f a) -> Scope Three f a -> f a
instantiate3 (x , y , z) = instantiate $ \ t -> case t of
  One -> x ; Two -> y ; Three -> z

----------------------------------------------------------------------