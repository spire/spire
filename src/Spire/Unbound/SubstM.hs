{-# LANGUAGE MultiParamTypeClasses
           , FlexibleContexts
           , FlexibleInstances
           , TypeFamilies
           , GADTs
           , ScopedTypeVariables
  #-}

module Spire.Unbound.SubstM where
-- import Data.List (find)
import Generics.RepLib
import Unbound.LocallyNameless.Types
import Unbound.LocallyNameless.Alpha

----------------------------------------------------------------------

-- data SubstCoerceM m a b =
--   SubstCoerceM (Name b) (b -> Maybe (m a))

type SubstMType m b a = Name b -> b -> a -> m a
type SubstHookMType m b a = a -> Maybe (Name b -> b -> m a)

-- Substitute 'b's into 'a's in the monad 'm'.
--
-- The interface is 'substHookM': the user should define it in all
-- cases where a variable is encountered or where the results of a
-- regular substitution needs to be post processed (e.g. in hereditary
-- substitution).
class (Monad m, Rep1 (SubstDM m b) a) => SubstM m b a where

  substHookM :: SubstHookMType m b a
  substHookM _ = Nothing

  -- isVarM :: a -> Maybe (SubstCoerceM m a b)
  -- isVarM _ = Nothing

  substM :: SubstMType m b a
  substM n u x | isFree n =
     case substHookM x of
       Just f -> f n u
       Nothing -> substR1M rep1 n u x
  substM m _ _ = error $ "Cannot substitute for bound variable " ++ show m

  -- XXX: Not sure how to write this now since we've essentially lost
  -- the notion of base case in substitution.  I.e., the below code
  -- seems to have independent base cases in mind (variables), but we
  -- have no such base cases ...

  -- substsM :: [(Name b, b)] -> a -> m a
  -- substsM ss x
  --   | all (isFree . fst) ss =
  --       case isVarM x of 
  --         Just (SubstCoerceM m f) ->
  --           case find ((==m) . fst) ss of 
  --               Just (_, u) -> maybe (return x) id (f u)
  --               Nothing -> return x
  --         Nothing -> substsR1M rep1 ss x
  --   | otherwise =
  --     error $ "Cannot substitute for bound variable in: " ++ show (map fst ss)

----------------------------------------------------------------------

data SubstDM m b a = SubstDM {
  substHookDM :: SubstHookMType m b a ,
  substDM :: SubstMType m b a
  -- substsDM :: [(Name b, b)] -> a -> m a
}

instance (SubstM m b a) => Sat (SubstDM m b a) where
  dict = SubstDM substHookM substM --substsM

substDefaultM :: Monad m => Rep1 (SubstDM m b) a => SubstMType m b a
substDefaultM = substR1M rep1

----------------------------------------------------------------------

substR1M :: Monad m => R1 (SubstDM m b) a -> SubstMType m b a
substR1M (Data1 _dt cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = mapM_l (\ w -> substDM w x y) rec kids
      in return . to c =<< z
substR1M _ = \ _ _ c -> return c

-- substsR1M :: Monad m => R1 (SubstDM m b) a -> [(Name b, b)] -> a -> m a
-- substsR1M (Data1 _dt cons) = \ s d ->
--   case (findCon cons d) of
--   Val c rec kids ->
--       let z = mapM_l (\ w -> substsDM w s) rec kids
--       in return . to c =<< z
-- substsR1M _ = \ _ c -> return c

----------------------------------------------------------------------

instance Monad m => SubstM m b Int
instance Monad m => SubstM m b Bool
instance Monad m => SubstM m b ()
instance Monad m => SubstM m b Char
instance Monad m => SubstM m b Integer
instance Monad m => SubstM m b Float
instance Monad m => SubstM m b Double

instance Monad m => SubstM m b AnyName
instance (Monad m, Rep a) => SubstM m b (R a)
instance (Monad m, Rep a) => SubstM m b (Name a)

instance (Monad m, SubstM m c a, SubstM m c b) => SubstM m c (a,b)
instance (Monad m, SubstM m c a, SubstM m c b, SubstM m c d) => SubstM m c (a,b,d)
instance (Monad m, SubstM m c a, SubstM m c b, SubstM m c d, SubstM m c e) => SubstM m c (a,b,d,e)
instance (Monad m, SubstM m c a, SubstM m c b, SubstM m c d, SubstM m c e, SubstM m c f) =>
   SubstM m c (a,b,d,e,f)
instance (Monad m, SubstM m c a) => SubstM m c [a]
instance (Monad m, SubstM m c a) => SubstM m c (Maybe a)
instance (Monad m, SubstM m c a, SubstM m c b) => SubstM m c (Either a b)

instance (Rep order, Rep card, Monad m, SubstM m c b, SubstM m c a, Alpha a,Alpha b) =>
    SubstM m c (GenBind order card a b)
instance (Monad m, SubstM m c b, SubstM m c a, Alpha a, Alpha b) =>
    SubstM m c (Rebind a b)

instance (Monad m, SubstM m c a) => SubstM m c (Embed a)
instance (Alpha a, Monad m, SubstM m c a) => SubstM m c (Rec a)

----------------------------------------------------------------------
