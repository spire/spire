{-# LANGUAGE
    GeneralizedNewtypeDeriving
  , ExistentialQuantification
  , DeriveDataTypeable
  , GADTs
  , Rank2Types
  , TypeFamilies
  , DataKinds
  , StandaloneDeriving
  #-}

module HashCons4 where

import Prelude hiding ( foldl )
import Data.Typeable
import Data.Type.Equality
import Control.Monad
import Control.Monad.State
import BiMap
import qualified Data.Map    as M
import qualified Data.IntMap as IM
import Data.Typeable
import System.IO.Unsafe

----------------------------------------------------------------------

type EId a = Int

data Exp a =
    TT
  | FF
  | Var a
  | Lam (EId (Maybe a))
  | Pair (EId a) (EId a)
  deriving (Show,Read,Eq,Ord,Typeable)

----------------------------------------------------------------------

type ParamBiMap = forall a. (Show a,Eq a,Ord a,Typeable a) => BiMap (Exp a)
data DAG = DAG { fromDAG :: ParamBiMap }
type TCM a = State DAG a

insertDAG :: (Show a,Eq a,Ord a,Typeable a) => Exp a -> ParamBiMap -> ParamBiMap
insertDAG v g =  case cast v of
    Just v' -> snd $ insert v' g
    Nothing -> g

hashcons :: (Show a,Eq a,Ord a,Typeable a) => Exp a -> TCM (EId a)
hashcons v = do
  DAG g <- get
  case lookupKey v g of
    Just k -> return (unsafePerformIO (putStrLn ("key found " ++ show k ++ " " ++ show v)  >> return k))
    Nothing -> do
      put $ DAG (insertDAG v g)
      hashcons v

----------------------------------------------------------------------

emptyDAG :: DAG
emptyDAG = DAG $ BiMap (M.empty) (IM.empty)

runDAG = flip runState emptyDAG

getVal :: TCM a -> a
getVal = fst . runDAG

getDAG :: (Show a,Eq a,Ord a,Typeable a) => TCM (EId b) -> BiMap (Exp a)
getDAG v = fromDAG (snd (runDAG v))

----------------------------------------------------------------------

-- hmz :: (Show a,Eq a,Ord a,Typeable a) => TCM (EId a)
-- hmz = do
--   tt <- hashcons TT
--   tt' <- hashcons TT
--   ab <- hashcons $ Pair tt tt'
--   ab' <- hashcons $ Pair tt tt'
--   hashcons $ Pair ab ab'

-- hmz2 :: (Show a,Eq a,Ord a,Typeable a) => Param a -> TCM (EId a)
-- hmz2 a = do
--   x0  <- hashcons (Maybe' a) $ Var Nothing
--   x0' <- hashcons (Maybe' a) $ Var Nothing
--   ab <- hashcons (Maybe' a) $ Pair x0 x0'
--   ab' <- hashcons (Maybe' a) $ Pair x0 x0'
--   aabb <- hashcons (Maybe' a) $ Pair ab ab'
--   hashcons a $ Lam aabb


----------------------------------------------------------------------