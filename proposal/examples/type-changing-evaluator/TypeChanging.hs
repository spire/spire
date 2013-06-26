{-# LANGUAGE DeriveDataTypeable
  , StandaloneDeriving
  , GADTs
  , DataKinds
  , KindSignatures
  , MultiParamTypeClasses #-}
import Data.Generics

----------------------------------------------------------------
-- Lambda calc with DeBruijn vars.

data Exp (i :: I) where
  Var  :: VarI i     => Int -> Exp i
  Lam  :: LamI i j   => Binder (Exp i) -> Exp j
  (:@) :: AppI i j k => Exp i -> Exp j -> Exp k
  Lift :: LiftI i j  => Exp i -> Exp j

newtype Binder a = Binder a
  deriving (Eq , Show , Data , Typeable)

-- deriving instance Eq (Exp i)
deriving instance Show (Exp i)
-- deriving instance Data (Exp i)
-- -- Not allowed to derive typeable for 'i' of kind other than '*'.
-- deriving instance Typeable1 Exp

----------------------------------------------------------------
-- Index constraints.

data I = E | M | R
-- data E
-- data M
-- data R

class VarI (i :: I)
-- class VarI i
instance VarI E
instance VarI R

class LamI (i :: I) (j :: I)
-- class LamI i j
instance LamI E E
instance LamI M M

class AppI (i :: I) (j :: I) (k :: I)
-- class AppI i j k
instance AppI E E E
instance AppI R M R

class LiftI (i :: I) (j :: I)
instance LiftI R M

