{-# LANGUAGE
    DeriveFunctor
  , DeriveFoldable
  , DeriveTraversable
  , GeneralizedNewtypeDeriving
  , ExistentialQuantification
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , UndecidableInstances
  , MultiParamTypeClasses
  #-}

module HashCons2 where

import Prelude hiding ( foldl )
import Data.Foldable
import Data.Traversable
import Control.Monad
import Control.Monad.State
import Prelude.Extras
import BiMap
import Bound
import Generics.RepLib

type Id = Int

data Exp a =
    TT
  | FF
  | Var a
  | Pair Id Id
  deriving (Show,Read,Eq,Ord,Functor)

$(derive [''Exp])

instance Eq1   Exp
instance Ord1  Exp
instance Show1 Exp
instance Read1 Exp

typeOf1 :: Rep a => f a -> R a
typeOf1 x = rep

data DAG = forall a. (Eq a,Ord a,Rep a) =>
  DAG (R a -> BiMap (Exp a))

hashcons :: (Eq a,Ord a,Rep a) => Exp a -> State DAG Id
hashcons n = do
  DAG gs <- get
  -- let g = gs (typeOf1 n)
  undefined
  -- case lookupKey n g of
  --   _ -> undefined
--   let _N  = typeOf n
--   case cast n of
--     Just n' -> case lookupKey n' g of
--       Just k -> return k
--       Nothing -> do
--         let (k , g') = insert n' g
--         put $ DAG $ \ t -> if t == _N then g' else gs t
--         return k
--     Nothing -> error "DAG improperly initialized"

emptyExp :: Rep a => R a -> BiMap (Exp a)
emptyExp _ = empty

emptyDAG :: DAG
emptyDAG = DAG emptyExp

