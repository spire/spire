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
import System.IO.Unsafe

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

type ForallMap = (Show a,Eq a,Ord a,Typeable a) => BiMap (Exp a)
data DAG = DAG { fromDAG :: ForallMap }
type TCM a = State DAG a

insertDAG :: (Show a,Eq a,Ord a,Typeable a) => Exp a -> ForallMap -> ForallMap
insertDAG v g =  case unsafePerformIO (putStrLn "try insert" >> return (cast v)) of
    Just v' -> unsafePerformIO (putStrLn "insert worked" >> return (snd $ insert v' g)) -- (error ("ugh\n" ++ show v'))
    Nothing -> g

hashcons :: (Show a,Eq a,Ord a,Typeable a) => Exp a -> TCM (EId a)
hashcons v = do
  DAG g <- get
  case lookupKey v g of
    Just k -> return (unsafePerformIO (putStrLn "key found" >> return k))
    Nothing -> do
      put $ DAG (insertDAG v g)
      hashcons v

----------------------------------------------------------------------

emptyDAG :: DAG
emptyDAG = DAG $ BiMap (M.empty) (IM.empty)

----------------------------------------------------------------------

hmz :: TCM (EId String)
hmz = do
  hashcons (TT :: Exp String)
  -- tt <- hashcons (TT :: Exp String)
  hashcons (TT :: Exp String)
  -- hashcons (TT :: Exp String)
  -- hashcons $ (Pair tt tt :: Exp String)
  -- hashcons $ (Pair tt tt :: Exp String)
  -- hashcons $ (Pair tt tt :: Exp String)

----------------------------------------------------------------------