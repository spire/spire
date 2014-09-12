{-# LANGUAGE TypeSynonymInstances
           , MultiParamTypeClasses
           , FlexibleInstances
  #-}

module ExprHashCons where
import BiMap
import Rebound
import Control.Applicative
import Control.Monad
import Control.Monad.State hiding ( lift )

----------------------------------------------------------------------

type ExpId = Int
type DAG = BiMap Exp
type TCM = State DAG

data Exp =
    TT | FF
  | Pair ExpId ExpId | App ExpId ExpId
  | Proj1 ExpId | Proj2 ExpId
  | Var Name
  | Lam (Bind1 ExpId)
  deriving (Show,Read,Eq,Ord)

hashExp :: Exp -> TCM Exp
hashExp v = do
  g <- get
  if member v g 
  then do
    let (k , g') = insert v g
    put g'
    return v
  else return v

hashcons :: Exp -> TCM ExpId
hashcons v = do
  g <- get
  case lookupKey v g of
    Nothing -> do
      let (k , g') = insert v g
      put g'
      return k
    Just k -> return k

----------------------------------------------------------------------

-- instance Subst TCM Exp where
--   vari = hashExp . Var

--   trav s (Var nm) = hashExp =<< s nm
--   trav s TT = hashExp TT
--   trav s FF = hashExp FF
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

-- ----------------------------------------------------------------------

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
-- var = vari . s2n

-- lam :: String -> TCM Exp -> TCM Exp
-- lam nm a = return . Lam =<< bind1 nm =<< a

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
--     Lam b -> eval =<< sub1 b a'
--     otherwise -> return $ App f' a'
-- eval (Var nm) = vari nm
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

----------------------------------------------------------------------