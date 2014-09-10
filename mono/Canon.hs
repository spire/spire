{-# LANGUAGE TypeSynonymInstances
           , MultiParamTypeClasses
           , FlexibleInstances
           , DeriveFunctor
  #-}

module Canon where
import Rebound
import Control.Applicative
import Control.Monad
import Control.Monad.Identity hiding ( lift )

----------------------------------------------------------------------

type TCM = Identity
type Nom = Name Val
type Spine = SpineF Elim

data Val =
    TT | FF
  | Pair Val Val
  | Lam (Bind Val)
  | Neut Nom Spine
  deriving (Show,Read,Eq,Ord)

data SpineF a = Emp | Ext (SpineF a) a
  deriving (Show,Read,Eq,Ord,Functor)

data Elim =
    Proj1 | Proj2
  | App Val
  deriving (Show,Read,Eq,Ord)

----------------------------------------------------------------------

instance Subst TCM Val where
  trav s TT = return TT
  trav s FF = return FF
  trav s (Pair a b) = do
    a' <- trav s a
    b' <- trav s b
    return $ Pair a' b'
  trav s (Lam b) = do
    b' <- travBind s b
    return $ Lam b'
  trav s (Neut nm xs) = mapM (travElim s) xs

travElim :: Sig TCM Val -> Elim -> TCM Elim
travElim s Proj1 = return Proj1
travElim s Proj2 = return Proj2
travElim s (App a) = do
  a' <- trav s a
  return $ App a'

-- instance Subst TCM Elim where
--   trav s Proj1 = return Proj1
--   trav s Proj2 = return Proj2
--   trav s (App a) = return . App =<< trav s a

-- instance Subst TCM Exp where
--   trav s (Var nm) = s Var nm
--    -- Spine nm xs = elim (s Var nm) =<< trav s xs
--   trav s TT = return TT
--   trav s FF = return FF
--   trav s (Proj1 ab) = do
--     ab' <- trav s ab
--     return $ Proj1 ab'
--   trav s (Proj2 ab) = do
--     ab' <- trav s ab
--     return $ Proj2 ab'
--   trav s (Pair a b) = do
--     a' <- trav s a
--     b' <- trav s b
--     return $ Pair a' b'
--   trav s (App f a) = do
--     f' <- trav s f
--     a' <- trav s a
--     return $ App f' a'
--   trav s (Lam b) = do
--     b' <- travBind s b
--     return $ Lam b'

----------------------------------------------------------------------

-- tt :: TCM Exp
-- tt = return TT

-- ff :: TCM Exp
-- ff = return FF

-- pair :: TCM Exp -> TCM Exp -> TCM Exp
-- pair = liftM2 Pair

-- app :: TCM Exp -> TCM Exp -> TCM Exp
-- app = liftM2 App

-- proj1 :: TCM Exp -> TCM Exp
-- proj1 = liftM Proj1

-- proj2 :: TCM Exp -> TCM Exp
-- proj2 = liftM Proj2

-- var :: String -> TCM Exp
-- var = var' . s2n

-- var' :: Nom -> TCM Exp
-- var' = return . Var

-- lam :: String -> TCM Exp -> TCM Exp
-- lam nm a = return . Lam =<< bind nm =<< a

-- ----------------------------------------------------------------------

-- eval :: Exp -> TCM Exp
-- eval TT = tt
-- eval FF = ff
-- eval (Pair a b) = pair (eval a) (eval b)
-- eval (Proj1 ab) = do
--   ab' <- eval ab
--   case ab' of
--     Pair a b -> return a
--     otherwise -> return $ Proj1 ab'
-- eval (Proj2 ab) = do
--   ab' <- eval ab
--   case ab' of
--     Pair a b -> return b
--     otherwise -> return $ Proj2 ab'
-- eval (App f a) = do
--   f' <- eval f
--   a' <- eval a
--   case f' of
--     Lam b -> eval =<< sub b a'
--     otherwise -> return $ App f' a'
-- eval (Var nm) = var' nm
-- eval (Lam (Bind b)) =
--   return . Lam . Bind =<< eval b

-- ----------------------------------------------------------------------

-- run :: TCM Exp -> Exp
-- run = runIdentity

-- ----------------------------------------------------------------------

-- eg1 :: TCM Exp
-- eg1 = lam "x" $ pair tt (var "y")

-- eg2 :: TCM Exp
-- eg2 = lam "x" $ pair ff (var "x")

-- eg3 :: TCM Exp
-- eg3 = lam "x" $ pair (lam "x" $ pair (var "x") (var "y")) (var "x")

-- eg4 :: TCM Exp
-- eg4 = lam "x" $ pair (lam "y" $ pair (var "x") (var "y")) (var "x")

-- eg4Eval1 :: TCM Exp
-- eg4Eval1 = eval =<< app eg4 tt

-- eg4Eval2 :: TCM Exp
-- eg4Eval2 = eval =<< app (proj1 (app eg4 tt)) ff

-- ----------------------------------------------------------------------