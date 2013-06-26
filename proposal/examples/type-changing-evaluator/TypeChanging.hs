{-# LANGUAGE DeriveDataTypeable
  , StandaloneDeriving
  , GADTs
  , DataKinds
  , KindSignatures
  , MultiParamTypeClasses #-}
import Data.Generics

----------------------------------------------------------------
-- Lambda calc with DeBruijn vars.

-- data Exp (i :: I) where
data Exp (i :: *) where
  Var  :: VarI i     => Int -> Exp i
  Lam  :: LamI i j   => Binder (Exp i) -> Exp j
  (:@) :: AppI i j k => Exp i -> Exp j -> Exp k

newtype Binder a = Binder a
  deriving (Eq , Show , Data , Typeable)

deriving instance Eq (Exp i)
deriving instance Show (Exp i)
deriving instance Data (Exp i)
-- Not allowed to derive typeable for 'i' of kind other than '*'.
deriving instance Typeable1 Exp

-- data I = E | M | R
data E
data M
data R

-- class VarI (i :: I)
class VarI i
instance VarI E
instance VarI R

-- class AppI (i :: I) (j :: I) (k :: I)
class AppI i j k

-- class LamI (i :: I) (j :: I)
class LamI i j