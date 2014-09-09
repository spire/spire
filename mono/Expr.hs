{-# LANGUAGE TypeSynonymInstances
           , MultiParamTypeClasses
           , FlexibleInstances
  #-}

module Expr where
import Rebound
import Control.Applicative
import Control.Monad
import Control.Monad.Identity hiding ( lift )

----------------------------------------------------------------------

type TCM = Identity

data Exp =
    TT | FF
  | Pair Exp Exp
  | App Exp Exp
  | Var (Name Exp)
  | Lam (Bind Exp)
  deriving (Show,Read,Eq,Ord)

----------------------------------------------------------------------

instance Subst TCM Exp where
  trav s (Var nm) = s Var nm
   -- Spine nm xs = elim (s Var nm) =<< trav s xs
  trav s TT = return TT
  trav s FF = return FF
  trav s (Pair a b) = do
    a' <- trav s a
    b' <- trav s b
    return $ App a' b'
  trav s (App f a) = do
    f' <- trav s f
    a' <- trav s a
    return $ App f' a'
  trav s (Lam b) = do
    b' <- travBind s b
    return $ Lam b'

----------------------------------------------------------------------

tt :: TCM Exp
tt = return TT

ff :: TCM Exp
ff = return FF

pair :: TCM Exp -> TCM Exp -> TCM Exp
pair = liftM2 Pair

app :: TCM Exp -> TCM Exp -> TCM Exp
app = liftM2 App

var :: String -> TCM Exp
var = return . Var . s2n

lam :: String -> TCM Exp -> TCM Exp
lam nm a = return . Lam =<< bind nm =<< a

run :: TCM Exp -> Exp
run = runIdentity

----------------------------------------------------------------------

eg1 :: Exp
eg1 = run $ lam "x" $ pair tt (var "y")

eg2 :: Exp
eg2 = run $ lam "x" $ pair tt (var "x")

eg3 :: Exp
eg3 = run $ lam "x" $ pair (lam "x" $ pair (var "x") (var "y")) (var "x")

eg4 :: Exp
eg4 = run $ lam "x" $ pair (lam "y" $ pair (var "x") (var "y")) (var "x")

----------------------------------------------------------------------