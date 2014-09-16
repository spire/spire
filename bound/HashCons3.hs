{-# LANGUAGE
    GeneralizedNewtypeDeriving
  , ExistentialQuantification
  , DeriveDataTypeable
  , GADTs
  , Rank2Types
  #-}

module HashCons3 where

import Prelude hiding ( foldl )
import Data.Typeable
import Control.Monad
import Control.Monad.State
import Prelude.Extras
import BiMap
import qualified Data.Map    as M
import qualified Data.IntMap as IM
import Bound

----------------------------------------------------------------------

type Id a = Int
type EId a = Id (Exp a)

data Exp a =
    TT
  | FF
  | Var a
  | Pair (EId a) (EId a)
  deriving (Show,Read,Eq,Ord,Typeable)

instance Eq1   Exp
instance Ord1  Exp
instance Show1 Exp
instance Read1 Exp

----------------------------------------------------------------------

type ForallMap = (Eq a,Ord a,Typeable a) => BiMap (Exp a)
data DAG = DAG { fromDAG :: ForallMap }
type TCM a = State DAG a

insertDAG :: (Eq a,Ord a,Typeable a) => Exp a -> ForallMap -> ForallMap
insertDAG v g = case cast v of
  Just v' -> snd $ insert v' g
  Nothing -> error "Dare I say never?"

hashcons :: (Eq a,Ord a,Typeable a) => Exp a -> TCM (EId a)
hashcons v = do
  DAG g <- get
  case lookupKey v g of
    Just k -> return k
    Nothing -> do
      put $ DAG (insertDAG v g)
      hashcons v

----------------------------------------------------------------------

emptyDAG :: DAG
emptyDAG = DAG $ BiMap (M.empty) (IM.empty)

----------------------------------------------------------------------

hmz :: TCM (EId String)
hmz = do
  tt <- hashcons (TT :: Exp String)
  hashcons (TT :: Exp String)
  hashcons (TT :: Exp String)
  hashcons $ (Pair tt tt :: Exp String)
  hashcons $ (Pair tt tt :: Exp String)
  hashcons $ (Pair tt tt :: Exp String)

----------------------------------------------------------------------