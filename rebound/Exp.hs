{-# LANGUAGE TypeSynonymInstances
           , MultiParamTypeClasses
           , FlexibleInstances
  #-}

module Exp where
import Rebound

----------------------------------------------------------------------

data Exp =
    TT | FF
  | Pair Exp Exp | App Exp Exp
  | Proj1 Exp | Proj2 Exp
  | Nm Name
  | Lam (Bind Exp)
  deriving (Show,Read,Eq,Ord)

----------------------------------------------------------------------

instance Subst Exp where
  trav s (Nm nm) = term (s nm)
  trav s TT = TT
  trav s FF = FF
  trav s (Pair a b) = Pair (trav s a) (trav s b)
  trav s (App f a) = App (trav s f) (trav s a)
  trav s (Proj1 ab) = Proj1 (trav s ab)
  trav s (Proj2 ab) = Proj2 (trav s ab)
  trav s (Lam b) = Lam (travBind s b)

instance Term Exp where
  term = Nm

type Ren = Name -> Name

-- ren :: Ren -> Exp -> Exp
-- ren s a = trav s a

-- instance Subst TCM Exp where
--   trav s (Nm nm) = s Nm nm
--    -- Spine nm xs = elim (s Nm nm) =<< trav s xs
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
-- var = var' . s2n

-- var' :: Name -> TCM Exp
-- var' = return . Nm

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
-- eval (Nm nm) = var' nm
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