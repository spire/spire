{-# LANGUAGE DeriveDataTypeable #-}


module BiMap where
import Data.Typeable
import qualified Data.Map    as M
import qualified Data.IntMap as IM

data BiMap a = BiMap (M.Map a Int) (IM.IntMap a)
  deriving (Show,Read,Eq,Ord,Typeable)

lookupKey :: Ord a => a -> BiMap a -> Maybe Int
lookupKey v (BiMap m _) = M.lookup v m

lookupVal :: Int -> BiMap a -> a
lookupVal k (BiMap _ m) = m IM.! k

nextId :: BiMap a -> Int
nextId (BiMap m im) = IM.size im

insert :: Ord a => a -> BiMap a -> (Int, BiMap a)
insert v g = (k , insertWith k v g)
 where k = nextId g

insertWith :: Ord a => Int -> a -> BiMap a -> BiMap a
insertWith k v (BiMap m im) = BiMap m' im'
 where m'  = M.insert v k m
       im' = IM.insert k v im

empty :: BiMap a
empty = BiMap (M.empty) (IM.empty)

size :: BiMap a -> Int
size (BiMap _ m) = IM.size m

toList :: BiMap a -> [(Int , a)]
toList (BiMap _ g) = IM.toList g

keys :: BiMap a -> [Int]
keys (BiMap _ g) = map fst (IM.toList g)