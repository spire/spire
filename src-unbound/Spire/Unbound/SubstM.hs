{-# LANGUAGE MultiParamTypeClasses
           , FlexibleContexts
           , FlexibleInstances
           , TypeFamilies
           , GADTs
           , ScopedTypeVariables
  #-}

module Spire.Unbound.SubstM where
import Data.List (find)
import Generics.RepLib
import Unbound.LocallyNameless.Fresh
import Unbound.LocallyNameless.Types
import Unbound.LocallyNameless.Alpha

----------------------------------------------------------------------

data SubstCoerceM m a b =
  SubstCoerceM (Name b) (b -> Maybe (m a))

class (Rep1 (SubstDM m b) a) => SubstM m b a where

  isVarM :: Monad m => a -> Maybe (SubstCoerceM m a b)
  isVarM _ = Nothing

  substM :: Monad m => Name b -> b -> a -> m a
  substM n u x | isFree n =
     case isVarM x of
       Just (SubstCoerceM m f) -> if m == n then maybe (return x) id (f u) else return x
       Nothing -> substR1M rep1 n u x
  substM m _ _ = error $ "Cannot substitute for bound variable " ++ show m

  substsM :: Monad m => [(Name b, b)] -> a -> m a
  substsM ss x
    | all (isFree . fst) ss =
        case isVarM x of 
          Just (SubstCoerceM m f) ->
            case find ((==m) . fst) ss of 
                Just (_, u) -> maybe (return x) id (f u)
                Nothing -> return x
          Nothing -> substsR1M rep1 ss x
    | otherwise =
      error $ "Cannot substitute for bound variable in: " ++ show (map fst ss)

----------------------------------------------------------------------

data SubstDM m b a = SubstDM {
  isVarDM  :: a -> Maybe (SubstCoerceM m a b),
  substDM  :: Name b -> b -> a -> m a,
  substsDM :: [(Name b, b)] -> a -> m a
}

instance (Monad m, SubstM m b a) => Sat (SubstDM m b a) where
  dict = SubstDM isVarM substM substsM

substDefaultM :: Monad m => Rep1 (SubstDM m b) a => Name b -> b -> a -> m a
substDefaultM = substR1M rep1

----------------------------------------------------------------------

substR1M :: Monad m => R1 (SubstDM m b) a -> Name b -> b -> a -> m a
substR1M (Data1 _dt cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = mapM_l (\ w -> substDM w x y) rec kids
      in return . to c =<< z
substR1M _ = \ _ _ c -> return c

substsR1M :: Monad m => R1 (SubstDM m b) a -> [(Name b, b)] -> a -> m a
substsR1M (Data1 _dt cons) = \ s d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = mapM_l (\ w -> substsDM w s) rec kids
      in return . to c =<< z
substsR1M _ = \ _ c -> return c

----------------------------------------------------------------------

instance SubstM m b Int
instance SubstM m b Bool
instance SubstM m b ()
instance SubstM m b Char
instance SubstM m b Integer
instance SubstM m b Float
instance SubstM m b Double

instance SubstM m b AnyName
instance (Rep a) => SubstM m b (R a)
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
