{-# LANGUAGE TypeSynonymInstances
           , MultiParamTypeClasses
           , FlexibleInstances
  #-}

module Canon where
import Rebound
import Control.Applicative
import Control.Monad
import Control.Monad.Identity hiding ( lift )

----------------------------------------------------------------------

type TCM = Identity
type Spine = SpineF Elim

data Val =
    TT | FF
  | Pair Val Val
  | Lam (Bind1 Val)
  | Neut Name Spine
  deriving (Show,Read,Eq,Ord)

data SpineF a = Id | Pipe (SpineF a) a
  deriving (Show,Read,Eq,Ord)

data Elim =
    Proj1 | Proj2
  | App Val
  deriving (Show,Read,Eq,Ord)

----------------------------------------------------------------------

instance Subst TCM Val where
  vari = return . flip Neut Id

  trav s TT = return TT
  trav s FF = return FF
  trav s (Pair a b) = do
    a' <- trav s a
    b' <- trav s b
    return $ Pair a' b'
  trav s (Lam b) = do
    b' <- travBind s b
    return $ Lam b'
  trav s (Neut nm xs) = do
    xs' <- travSpine s xs
    x <- s nm
    elims x xs'

travSpine :: Sig TCM Val -> Spine -> TCM Spine
travSpine s Id = return Id
travSpine s (Pipe xs x) = do
  xs' <- travSpine s xs
  x' <- travElim s x
  return $ Pipe xs' x'  

travElim :: Sig TCM Val -> Elim -> TCM Elim
travElim s Proj1 = return Proj1
travElim s Proj2 = return Proj2
travElim s (App a) = do
  a' <- trav s a
  return $ App a'

----------------------------------------------------------------------

tt :: TCM Val
tt = return TT

ff :: TCM Val
ff = return FF

pair :: TCM Val -> TCM Val -> TCM Val
pair = liftM2 Pair

app :: TCM Val -> TCM Val -> TCM Val
app f a = do
  f' <- f
  a' <- a
  elim f' (App a')

proj1 :: TCM Val -> TCM Val
proj1 ab = ab >>= flip elim Proj1

proj2 :: TCM Val -> TCM Val
proj2 ab = ab >>= flip elim Proj2

var :: String -> TCM Val
var = vari . s2n

lam :: String -> TCM Val -> TCM Val
lam nm a = return . Lam =<< bind1 nm =<< a

----------------------------------------------------------------------

elims :: Val -> Spine -> TCM Val
elims x Id = return x
elims x (Pipe fs f) = do
  x' <- elims x fs
  elim x' f

elim :: Val -> Elim -> TCM Val
elim (Neut nm fs) f = return $ Neut nm (Pipe fs f)
elim (Pair a b) Proj1 = return a
elim (Pair a b) Proj2 = return b
elim (Lam f) (App a) = f `sub1` a
elim _ _ = error "Ill-typed evaluation"

----------------------------------------------------------------------

run :: TCM Val -> Val
run = runIdentity

----------------------------------------------------------------------

eg1 :: TCM Val
eg1 = lam "x" $ pair tt (var "y")

eg2 :: TCM Val
eg2 = lam "x" $ pair ff (var "x")

eg3 :: TCM Val
eg3 = lam "x" $ pair (lam "x" $ pair (var "x") (var "y")) (var "x")

eg4 :: TCM Val
eg4 = lam "x" $ pair (lam "y" $ pair (var "x") (var "y")) (var "x")

eg4Eval1 :: TCM Val
eg4Eval1 = app eg4 tt

eg4Eval2 :: TCM Val
eg4Eval2 = app (proj1 (app eg4 tt)) ff

----------------------------------------------------------------------