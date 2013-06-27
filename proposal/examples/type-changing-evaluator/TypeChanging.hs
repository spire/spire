{-# LANGUAGE DeriveDataTypeable
  , TypeFamilies
  , RankNTypes
  , StandaloneDeriving
  , GADTs
  , DataKinds
  , KindSignatures
  , MultiParamTypeClasses #-}
-- Like TypeChanging.hs, but using type functions instead of
-- functional dependencies.
import Data.Generics

----------------------------------------------------------------
-- Lambda calc with DeBruijn vars.

data Exp (i :: I) where
  Var  :: VarI i                      => Int -> Exp i
  Lam  :: LamI j ~ i                  => Binder (Exp i) -> Exp j
  (:@) :: (AppI1 k ~ i , AppI2 k ~ j) => Exp i -> Exp j -> Exp k
  Lift :: LiftI j ~ i                 => Exp i -> Exp j

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

type family   LamI (i :: I) :: I
-- class LamI i j
type instance LamI E = E
type instance LamI M = M

type family   AppI1 (k :: I) :: I
-- class AppI i j k
type instance AppI1 E = E
type instance AppI1 R = R

type family   AppI2 (k :: I) :: I
type instance AppI2 E = E
type instance AppI2 R = M

type family   LiftI (j :: I) :: I
type instance LiftI M = R

----------------------------------------------------------------
-- Non generic, non monadic operations.

-- Increment all free variables:
-- If G |- e:B then G,A |- weaken e:B.
weaken1 :: Exp e -> Exp e
weaken1 = w 0
  where
  w :: Int -> Exp e -> Exp e
  w i (Var j)          = wVar i j
  w i (e1 :@ e2)       = w i e1 :@ w i e2
  w i (Lam (Binder e)) = Lam (Binder (w (succ i) e))
  w i (Lift e)         = Lift (w i e)

wVar :: VarI e => Int -> Int -> Exp e
wVar i j | i <= j    = Var (succ j)
         | otherwise = Var j

-- Substitute an expression for variable zero:
-- If G |- e1:A and G,A |- e2:B then G |- substitute e1 e2:B.
substitute1 :: (forall e. Exp e -> Exp e) -> Exp M -> Exp M -> Exp M
substitute1 weaken = sM 0
  where
  sM :: Int -> Exp M -> Exp M -> Exp M
  sM i e0 (Lam (Binder e)) = Lam (Binder (sM (succ i) (weaken e0) e))
  sM i e0 (Lift e)         = sR i e0 e

  sR :: Int -> Exp M -> Exp R -> Exp M
  sR i e0 (Var j)          = sVar i e0 j
  sR i e0 (e1 :@ e2)       = sR i e0 e1 `app` sM i e0 e2

  app :: Exp M -> Exp M -> Exp M
  app (Lift e) e' = Lift (e :@ e')
  app (Lam (Binder e)) e' = substitute1 weaken e' e

sVar :: Int -> Exp M -> Int -> Exp M
sVar i e0 j | i == j    = e0
            | i <  j    = Lift $ Var (pred j)
            | otherwise = Lift $ Var j
