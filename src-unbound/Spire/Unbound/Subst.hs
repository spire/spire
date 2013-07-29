{-# LANGUAGE MultiParamTypeClasses
           , FlexibleContexts
           , FlexibleInstances
           , TypeFamilies
           , GADTs
           , ScopedTypeVariables
  #-}

module Spire.Unbound.Subst where
import Data.List (find)
import Generics.RepLib
import Unbound.LocallyNameless.Fresh
import Unbound.LocallyNameless.Types
import Unbound.LocallyNameless.Alpha

----------------------------------------------------------------------

data SubstCoerce m a b =
  SubstCoerce (Name b) (b -> Maybe (m a))

class (Rep1 (SubstD m b) a) => Subst m b a where

  isVar :: Monad m => a -> Maybe (SubstCoerce m a b)
  isVar _ = Nothing

  subst :: Monad m => Name b -> b -> a -> m a
  subst n u x | isFree n =
     case isVar x of
       Just (SubstCoerce m f) -> if m == n then maybe (return x) id (f u) else return x
       Nothing -> substR1 rep1 n u x
  subst m _ _ = error $ "Cannot substitute for bound variable " ++ show m

  substs :: Monad m => [(Name b, b)] -> a -> m a
  substs ss x
    | all (isFree . fst) ss =
        case isVar x of 
          Just (SubstCoerce m f) ->
            case find ((==m) . fst) ss of 
                Just (_, u) -> maybe (return x) id (f u)
                Nothing -> return x
          Nothing -> substsR1 rep1 ss x
    | otherwise =
      error $ "Cannot substitute for bound variable in: " ++ show (map fst ss)

----------------------------------------------------------------------

data SubstD m b a = SubstD {
  isVarD  :: a -> Maybe (SubstCoerce m a b),
  substD  :: Name b -> b -> a -> m a,
  substsD :: [(Name b, b)] -> a -> m a
}

instance (Monad m, Subst m b a) => Sat (SubstD m b a) where
  dict = SubstD isVar subst substs

substDefault :: Monad m => Rep1 (SubstD m b) a => Name b -> b -> a -> m a
substDefault = substR1 rep1

----------------------------------------------------------------------

substR1 :: Monad m => R1 (SubstD m b) a -> Name b -> b -> a -> m a
substR1 (Data1 _dt cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = mapM_l (\ w -> substD w x y) rec kids
      in return . to c =<< z
substR1 _ = \ _ _ c -> return c

substsR1 :: Monad m => R1 (SubstD m b) a -> [(Name b, b)] -> a -> m a
substsR1 (Data1 _dt cons) = \ s d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = mapM_l (\ w -> substsD w s) rec kids
      in return . to c =<< z
substsR1 _ = \ _ c -> return c

----------------------------------------------------------------------

instance Subst m b Int
instance Subst m b Bool
instance Subst m b ()
instance Subst m b Char
instance Subst m b Integer
instance Subst m b Float
instance Subst m b Double

instance Subst m b AnyName
instance (Rep a) => Subst m b (R a)
instance (Monad m, Rep a) => Subst m b (Name a)

instance (Monad m, Subst m c a, Subst m c b) => Subst m c (a,b)
instance (Monad m, Subst m c a, Subst m c b, Subst m c d) => Subst m c (a,b,d)
instance (Monad m, Subst m c a, Subst m c b, Subst m c d, Subst m c e) => Subst m c (a,b,d,e)
instance (Monad m, Subst m c a, Subst m c b, Subst m c d, Subst m c e, Subst m c f) =>
   Subst m c (a,b,d,e,f)
instance (Monad m, Subst m c a) => Subst m c [a]
instance (Monad m, Subst m c a) => Subst m c (Maybe a)
instance (Monad m, Subst m c a, Subst m c b) => Subst m c (Either a b)

instance (Rep order, Rep card, Monad m, Subst m c b, Subst m c a, Alpha a,Alpha b) =>
    Subst m c (GenBind order card a b)
instance (Monad m, Subst m c b, Subst m c a, Alpha a, Alpha b) =>
    Subst m c (Rebind a b)

instance (Monad m, Subst m c a) => Subst m c (Embed a)
instance (Alpha a, Monad m, Subst m c a) => Subst m c (Rec a)

----------------------------------------------------------------------