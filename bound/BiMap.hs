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

-- Insert the value and return the corresponding key
-- and the new map
-- Alas, Map interface does not have an operation to insert and find the index 
-- at the same time (although such an operation is easily possible)
insert :: Ord a => a -> BiMap a -> (Int, BiMap a)
insert v (BiMap m im) = (k , BiMap m' im')
 where m'  = M.insert v k m
       im' = IM.insert k v im
       k   = IM.size im

empty :: BiMap a
empty = BiMap (M.empty) (IM.empty)

size :: BiMap a -> Int
size (BiMap _ m) = IM.size m

toList :: BiMap a -> [(Int , a)]
toList (BiMap _ g) = IM.toList g