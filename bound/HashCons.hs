{-# LANGUAGE
    DeriveFunctor
  , DeriveFoldable
  , DeriveTraversable
  , GeneralizedNewtypeDeriving
  , ExistentialQuantification
  , DeriveDataTypeable
  , GADTs
  #-}

module HashCons where

import Prelude hiding ( foldl )
import Data.Foldable
import Data.Traversable
import Data.Typeable
import Control.Monad
import Control.Monad.State
import Prelude.Extras
import BiMap
import qualified Data.Map    as M
import qualified Data.IntMap as IM
import Bound

type Id = Int

data Exp a =
    TT
  | FF
  | Var a
  | Pair Id Id
  deriving (Show,Read,Eq,Ord,Functor,Typeable)

instance Eq1   Exp
instance Ord1  Exp
instance Show1 Exp
instance Read1 Exp

-- data DAG = forall a. (Eq a,Ord a,Typeable a) =>
--   DAG (TypeRep -> BiMap (Exp a))

data DAG where
  DAG :: (Eq a,Ord a,Typeable a) => (TypeRep -> BiMap (Exp a)) -> DAG

hashcons :: (Eq a,Ord a,Typeable a) => Exp a -> State DAG Id
hashcons n = do
  DAG gs <- get
  let _N  = typeOf n
  let g = gs _N
  case cast n of
    Just n' -> case lookupKey n' g of
      Just k -> return k
      Nothing -> do
        let (k , g') = insert n' g
        put $ DAG $ \ t -> if t == _N then g' else gs t
        return k
    Nothing -> error "DAG improperly initialized"

emptyExp :: (Eq a,Ord a,Typeable a) => BiMap (Exp a)
emptyExp = BiMap (M.empty) (IM.empty)

pack :: (Eq a,Ord a,Typeable a) => BiMap (Exp a) -> DAG
pack g = DAG (const g)

-- emptyDAG :: DAG
-- emptyDAG = pack emptyExp
