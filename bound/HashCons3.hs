{-# LANGUAGE
    GeneralizedNewtypeDeriving
  , ExistentialQuantification
  , DeriveDataTypeable
  , GADTs
  , Rank2Types
  , TypeFamilies
  , DataKinds
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

instance TestEquality Param where
  testEquality String' String' = Just Refl
  testEquality (Maybe' a) (Maybe' b) = case testEquality a b of
    Just Refl -> Just Refl
    Nothing -> Nothing
  testEquality _ _ = Nothing

----------------------------------------------------------------------

type EId = Int

data Exp a =
    TT
  | FF
  | Var a
  | Pair EId EId
  deriving (Show,Read,Eq,Ord,Typeable)

----------------------------------------------------------------------

type ParamBiMap = forall a. Param a -> BiMap (Exp a)
data DAG = DAG { fromDAG :: ParamBiMap }
type TCM a = State DAG a

insertDAG :: (Show a,Eq a,Ord a) => Param a -> Exp a -> ParamBiMap -> ParamBiMap
insertDAG a v g b =  case testEquality a b of
    Just Refl -> snd $ insert v (g a)
    Nothing -> g b

hashcons :: (Show a,Eq a,Ord a) => Param a -> Exp a -> TCM EId
hashcons a v = do
  DAG g <- get
  case lookupKey v (g a) of
    Just k -> return (unsafePerformIO (putStrLn "key found" >> return k))
    Nothing -> do
      put $ DAG (insertDAG a v g)
      hashcons a v

----------------------------------------------------------------------

hashcons0 = hashcons String'

emptyDAG :: DAG
emptyDAG = DAG $ const $ BiMap (M.empty) (IM.empty)

runDAG = flip runState emptyDAG

getVal :: TCM a -> a
getVal = fst . runDAG

getDAG :: Param a -> TCM EId -> BiMap (Exp a)
getDAG a v = fromDAG (snd (runDAG v)) a

----------------------------------------------------------------------

hmz :: TCM EId
hmz = do
  tt <- hashcons0 TT
  tt' <- hashcons0 TT
  ab <- hashcons0 $ (Pair tt tt')
  ab' <- hashcons0 $ (Pair tt tt')
  hashcons0 $ (Pair ab ab')

----------------------------------------------------------------------