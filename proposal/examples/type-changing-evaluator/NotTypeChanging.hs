{-# LANGUAGE DeriveDataTypeable , Rank2Types , ViewPatterns #-}
import Control.Applicative
import Control.Arrow
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Generics
import Data.Set (Set)
import qualified Data.Set

----------------------------------------------------------------
-- Lambda calc with DeBruijn vars.

data Exp = Var Int | Exp :@ Exp | Lam (Binder Exp)
  deriving (Eq , Show , Data , Typeable)
newtype Binder a = Binder a
  deriving (Eq , Show , Data , Typeable)

----------------------------------------------------------------
-- Explicit parameters.

-- Increment all free variables:
-- If G |- e:B then G,A |- weaken e:B.
weaken1 :: Exp -> Exp
weaken1 = w 0
  where
  w :: Int -> Exp -> Exp
  w i (Var j)          = wVar i j
  w i (e1 :@ e2)       = w i e1 :@ w i e2
  w i (Lam (Binder e)) = Lam (Binder (w (succ i) e))

wVar :: Int -> Int -> Exp
wVar i j | i <= j    = Var (succ j)
         | otherwise = Var j

-- Substitute an expression for variable zero:
-- If G |- e1:A and G,A |- e2:B then G |- substitute e1 e2:B.
substitute1 :: (Exp -> Exp) -> Exp -> Exp -> Exp
substitute1 weaken = s 0
  where
  s :: Int -> Exp -> Exp -> Exp
  s i e0 (Var j)          = sVar i e0 j
  s i e0 (e1 :@ e2)       = s i e0 e1 :@ s i e0 e2
  s i e0 (Lam (Binder e)) = Lam (Binder (s (succ i) (weaken e0) e))

sVar :: Int -> Exp -> Int -> Exp
sVar i e0 j | i == j    = e0
            | i <  j    = Var (pred j)
            | otherwise = Var j

normalize1 :: (Exp -> Exp -> Exp) -> Exp -> Exp
normalize1 substitute = n
  where
  n :: Exp -> Exp
  n (Var i) = Var i
  n ((n -> e1') :@ (n -> e2'))
    | Lam (Binder e') <- e1' = n (substitute e2' e')
    | otherwise              = e1' :@ e2'
  n (Lam (Binder e)) = Lam (Binder (n e))

n1 = normalize1 (substitute1 weaken1)

freeVars1 :: Exp -> Set Int
freeVars1 = f 0
  where
  f :: Int -> Exp -> Set Int
  f i (Var j)          = fVar i j
  f i (e1 :@ e2)       = f i e1 `Data.Set.union` f i e2
  f i (Lam (Binder e)) = f (succ i) e

fVar :: Int -> Int -> Set Int
fVar i j | i <= j    = Data.Set.singleton $ j - i
         | otherwise = Data.Set.empty

----------------------------------------------------------------
-- Implicit (monadic) parameters.

weaken2 :: Exp -> Exp
weaken2 e = runReader (w e) 0
  where
  w :: Exp -> Reader Int Exp
  w (Var j) = do
    i <- ask
    return $ wVar i j
  w (e1 :@ e2) = (:@) <$> w e1 <*> w e2
  w (Lam (Binder e)) = Lam . Binder <$> local succ (w e)

substitute2 :: (Exp -> Exp) -> Exp -> Exp -> Exp
substitute2 weaken e0 e = runReader (s e) (0 , e0)
  where
  s :: Exp -> Reader (Int , Exp) Exp
  s (Var j) = do
    (i , e0) <- ask
    return $ sVar i e0 j
  s (e1 :@ e2)       = (:@) <$> s e1 <*> s e2
  s (Lam (Binder e)) = Lam . Binder <$> local (succ *** weaken) (s e)

n2 = normalize1 (substitute2 weaken2)

freeVars2 :: Exp -> Set Int
freeVars2 e = execWriter $ runReaderT (f e) 0
  where
  f :: Exp -> ReaderT Int (Writer (Set Int)) ()
  f (Var j)          = do i <- ask; tell $ fVar i j
  f (e1 :@ e2)       = f e1 >> f e2
  f (Lam (Binder e)) = local succ (f e)

----------------------------------------------------------------
-- New SYB traversal.

newtype MM m x = MM { unMM :: m x -> m x }
mkMM :: (Typeable a , Typeable b) => (m a -> m a) -> m b -> m b
mkMM t = maybe id unMM (gcast (MM t))
      -- Same as:
      -- unMM ((MM id) `ext0` (MM t))
      -- See: http://hackage.haskell.org/packages/archive/syb/latest/doc/html/src/Data-Generics-Aliases.html

-- Apply a 'GenericM' everywhere, transforming the results with a
-- 'GenericMM'.
type GenericMM m = Data a => m a -> m a
everywhereMM :: Monad m => GenericMM m -> GenericM m -> GenericM m
everywhereMM mm m x = mm (m =<< gmapM (everywhereMM mm m) x)

----------------------------------------------------------------
-- SYB.

type W = Reader Int
weaken3 :: Exp -> Exp
weaken3 e = runReader (w e) 0
  where
  w :: GenericM W
  w = everywhereMM (mkMM b) (mkM v)

  b :: W (Binder Exp) -> W (Binder Exp)
  b = local succ

  v :: Exp -> W Exp
  v (Var j) = do
    i <- ask
    return $ wVar i j
  v e = return e

type S = Reader (Int , Exp)
substitute3 :: (Exp -> Exp) -> Exp -> Exp -> Exp
substitute3 weaken e0 e = runReader (s e) (0 , e0)
  where
  s :: GenericM S
  s = everywhereMM (mkMM b) (mkM v)

  b :: S (Binder Exp) -> S (Binder Exp)
  b = local (succ *** weaken)

  v :: Exp -> S Exp
  v (Var j) = do
    (i , e0) <- ask
    return $ sVar i e0 j
  v e = return e

normalize3 :: (Exp -> Exp -> Exp) -> Exp -> Exp
normalize3 substitute = n
  where
  n :: GenericT
  n = everywhere (mkT a)

  a :: Exp -> Exp
  a (Lam (Binder e) :@ e2) = n (substitute e2 e)
  a e = e

n3 = normalize3 (substitute3 weaken3)

type F = ReaderT Int (Writer (Set Int))
freeVars3 :: Exp -> Set Int
freeVars3 e = execWriter $ runReaderT (f e) 0
  where
  f :: GenericM F
  f = everywhereMM (mkMM b) (mkM v)

  b :: F (Binder Exp) -> F (Binder Exp)
  b = local succ

  -- Need 'a -> m a' for 'mkM', although we really want 'a -> m ()'
  -- here.  Hence the 'undefined's.
  v :: Exp -> F Exp
  v (Var j) = do 
    i <- ask
    tell $ fVar i j
    return undefined
  v _ = return undefined

----------------------------------------------------------------
-- Pretty printers

pp :: Exp -> String
pp = p ["x" ++ show i | i <- [0..]] []
  where
  -- Print open exp with respect to (f)ree and (b)ound names.
  p :: [String] -> [String] -> Exp -> String
  p f b (Var i) = if i < length b then b !! i else w (show (Var i))
  p f b (e1 :@ e2) = l e1 (p f b e1) ++ " " ++ r e2 (p f b e2)
  p (x:f) b (Lam (Binder e)) = "\\" ++ x ++ ". " ++ p f (x:b) e

  -- Optionally (w)rap (l)eft and (r)ight subexpressions.
  w :: String  -> String
  w s = "(" ++ s ++ ")"
  l , r :: Exp -> String -> String
  l (Lam _)  = w
  l _        = id
  r (_ :@ _) = w
  r (Lam _)  = w
  r _        = id

ppp , pppn :: Exp -> IO ()
ppp  = putStrLn . pp
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
  print $ agree n1 n2 n3
  print $ agree freeVars1 freeVars2 freeVars3
  where
  agree f g h = and [ f e == g e && g e == h e | e <- egs ]
