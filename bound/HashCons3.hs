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

module HashCons3 where

import Prelude hiding ( foldl )
import Data.Typeable
import Data.Type.Equality
import Control.Monad
import Control.Monad.State
import BiMap
import qualified Data.Map    as M
import qualified Data.IntMap as IM
import System.IO.Unsafe

----------------------------------------------------------------------

data Param (a :: *) :: * where
  String' :: Param String
  Maybe' :: Param a -> Param (Maybe a)
deriving instance Show (Param a)

instance TestEquality Param where
  testEquality String' String' = Just Refl
  testEquality (Maybe' a) (Maybe' b) = case testEquality a b of
    Just Refl -> Just Refl
    Nothing -> Nothing
  testEquality _ _ = Nothing

----------------------------------------------------------------------

type EId a = Int

data Exp a =
    TT
  | FF
  | Var a
  | Lam (EId (Maybe a))
  | Pair (EId a) (EId a)
  deriving (Show,Read,Eq,Ord)

----------------------------------------------------------------------

type ParamBiMap = forall a. Param a -> BiMap (Exp a)
data DAG = DAG { fromDAG :: ParamBiMap }
type TCM a = State DAG a

insertDAG :: (Show a,Eq a,Ord a) => Param a -> Exp a -> ParamBiMap -> ParamBiMap
insertDAG a v g b =  case testEquality a b of
    Just Refl -> snd $ insert v (g a)
    Nothing -> g b

hashcons :: (Show a,Eq a,Ord a) => Param a -> Exp a -> TCM (EId a)
hashcons a v = do
  DAG g <- get
  case lookupKey v (g a) of
    Just k -> return (unsafePerformIO (putStrLn ("key found (" ++ show a ++ ") " ++ show k ++ " " ++ show v)  >> return k))
    Nothing -> do
      put $ DAG (insertDAG a v g)
      hashcons a v

----------------------------------------------------------------------

emptyDAG :: DAG
emptyDAG = DAG $ const $ BiMap (M.empty) (IM.empty)

runDAG = flip runState emptyDAG

getVal :: TCM a -> a
getVal = fst . runDAG

getDAG :: Param a -> TCM (EId b) -> BiMap (Exp a)
getDAG a v = fromDAG (snd (runDAG v)) a

----------------------------------------------------------------------

hmz :: (Show a,Eq a,Ord a) => Param a -> TCM (EId a)
hmz a = do
  tt <- hashcons a TT
  tt' <- hashcons a TT
  ab <- hashcons a $ Pair tt tt'
  ab' <- hashcons a $ Pair tt tt'
  hashcons a $ Pair ab ab'

hmz2 :: (Show a,Eq a,Ord a) => Param a -> TCM (EId a)
hmz2 a = do
  x0  <- hashcons (Maybe' a) $ Var Nothing
  x0' <- hashcons (Maybe' a) $ Var Nothing
  ab <- hashcons (Maybe' a) $ Pair x0 x0'
  ab' <- hashcons (Maybe' a) $ Pair x0 x0'
  aabb <- hashcons (Maybe' a) $ Pair ab ab'
  hashcons a $ Lam aabb


----------------------------------------------------------------------