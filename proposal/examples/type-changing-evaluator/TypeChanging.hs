{-# LANGUAGE DeriveDataTypeable
  , ViewPatterns
  , TypeFamilies
  , RankNTypes
  , StandaloneDeriving
  , GADTs
  , DataKinds
  , KindSignatures
  , MultiParamTypeClasses #-}
-- Like TypeChanging.hs, but using type functions instead of
-- functional dependencies.
import Data.Generics

----------------------------------------------------------------
-- Lambda calc with DeBruijn vars.

data Exp (i :: I) where
  Var  :: VarI i                      => Int -> Exp i
  Lam  :: LamI j ~ i                  => Binder (Exp i) -> Exp j
  (:@) :: (AppI1 k ~ i , AppI2 k ~ j) => Exp i -> Exp j -> Exp k
  Lift :: LiftI j ~ i                 => Exp i -> Exp j

newtype Binder a = Binder a
  deriving (Eq , Show , Data , Typeable)

-- deriving instance Eq (Exp i)
deriving instance Show (Exp i)
-- deriving instance Data (Exp i)
-- -- Not allowed to derive typeable for 'i' of kind other than '*'.
-- deriving instance Typeable1 Exp

----------------------------------------------------------------
-- Index constraints.

data I = E | M | R
-- data E
-- data M
-- data R

class VarI (i :: I)
-- class VarI i
instance VarI E
instance VarI R

type family   LamI (i :: I) :: I
-- class LamI i j
type instance LamI E = E
type instance LamI M = M

type family   AppI1 (k :: I) :: I
-- class AppI i j k
type instance AppI1 E = E
type instance AppI1 R = R

type family   AppI2 (k :: I) :: I
type instance AppI2 E = E
type instance AppI2 R = M

type family   LiftI (j :: I) :: I
type instance LiftI M = R

----------------------------------------------------------------
-- Non generic, non monadic operations.

-- Increment all free variables:
-- If G |- e:B then G,A |- weaken e:B.
weaken1 :: Exp e -> Exp e
weaken1 = w 0
  where
  w :: Int -> Exp e -> Exp e
  w i (Var j)          = wVar i j
  w i (e1 :@ e2)       = w i e1 :@ w i e2
  w i (Lam (Binder e)) = Lam (Binder (w (succ i) e))
  w i (Lift e)         = Lift (w i e)

wVar :: VarI e => Int -> Int -> Exp e
wVar i j | i <= j    = Var (succ j)
         | otherwise = Var j

-- Substitute an expression for variable zero:
-- If G |- e1:A and G,A |- e2:B then G |- substitute e1 e2:B.
substitute1 :: (Exp M -> Exp M) -> Exp M -> Exp M -> Exp M
substitute1 weaken = sM 0
  where
  sM :: Int -> Exp M -> Exp M -> Exp M
  -- Generic!
  sM i e0 (Lam (Binder e)) = Lam (Binder (sM (succ i) (weaken e0) e))
  sM i e0 (Lift e)         = sR i e0 e

  sR :: Int -> Exp M -> Exp R -> Exp M
  sR i e0 (Var j)          = sVar i e0 j
  sR i e0 (e1 :@ e2)       = sR i e0 e1 `appM` sM i e0 e2

  appM = appM1 (substitute1 weaken)

appM1 :: (Exp M -> Exp M -> Exp M) -> Exp M -> Exp M -> Exp M
appM1 substitute (Lift e) e' = Lift (e :@ e')
appM1 substitute (Lam (Binder e)) e' = substitute e' e

sVar :: Int -> Exp M -> Int -> Exp M
sVar i e0 j | i == j    = e0
            | i <  j    = Lift $ Var (pred j)
            | otherwise = Lift $ Var j

normalize1 :: (Exp M -> Exp M -> Exp M) -> Exp E -> Exp M
normalize1 appM = n
  where
  n :: Exp E -> Exp M
  n (Var i)                    = Lift $ Var i
  n ((n -> e1') :@ (n -> e2')) = e1' `appM` e2'
  -- Generic!
  n (Lam (Binder e))           = Lam (Binder (n e))

n1 = normalize1 (appM1 $ substitute1 weaken1)

----------------------------------------------------------------
-- Pretty printers

pp :: Exp e -> String
pp = p ["x" ++ show i | i <- [0..]] []
  where
  -- Print open exp with respect to (f)ree and (b)ound names.
  p :: [String] -> [String] -> Exp e -> String
  p f b (Var i) = if i < length b then b !! i else w ("#" ++ show i)
  p f b (e1 :@ e2) = l e1 (p f b e1) ++ " " ++ r e2 (p f b e2)
  p (x:f) b (Lam (Binder e)) = "\\" ++ x ++ ". " ++ p f (x:b) e
  p f b (Lift e) = p f b e

  -- Optionally (w)rap (l)eft and (r)ight subexpressions.
  w :: String  -> String
  w s = "(" ++ s ++ ")"
  l , r :: Exp e -> String -> String
  l (Lam _)  = w
  l _        = id
  r (_ :@ _) = w
  r (Lam _)  = w
  r _        = id

ppp :: Exp e -> IO ()
ppp  = putStrLn . pp
pppn :: Exp E -> IO ()
pppn = ppp . n1

----------------------------------------------------------------
-- Examples.

-- Closed examples.

k = Lam (Binder (Lam (Binder (Var 1))))
s = Lam (Binder (Lam (Binder (Lam (Binder $
       (Var 2 :@ Var 0) :@
       (Var 1 :@ Var 0))))))
i = Lam (Binder (Var 0))
skk = (s :@ k) :@ k
skkEta = Lam (Binder (skk :@ Var 0))

-- Open examples.

e1 = Var 0
e2 = Lam (Binder (Var 1 :@ Var 0))
e3 = Lam (Binder (Lam (Binder (Var 2 :@ Var 3))))
e4 = (e3 :@ e2) :@ e1

-- All examples.
egs = [ k , s , i , skk , skkEta , e1 , e2 , e3 , e4 ]

main = do
  ppp s
  ppp skkEta
  pppn skkEta
  -- print $ agree n1 n2 n3
  -- print $ agree freeVars1 freeVars2 freeVars3
  -- where
  -- agree f g h = and [ f e == g e && g e == h e | e <- egs ]
