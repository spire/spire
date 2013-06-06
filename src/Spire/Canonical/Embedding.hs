{-# LANGUAGE NamedFieldPuns #-}
module Spire.Canonical.Embedding (embedV , embedN , embedVC) where
import Spire.Expression.Types
import Spire.Canonical.HereditarySubstitution
import Spire.Canonical.Types
import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader
import Data.Generics

----------------------------------------------------------------------

embedV :: Val -> Infer
embedV = run embedV'

embedN :: Neut -> Infer
embedN = run embedN'

embedVC :: Val -> Check
embedVC = run embedVC'

run :: Data a => (a -> EmbedM b) -> a -> b
-- Promote 'Left' errors to exceptions.
run f x = either error id .
          runReader (runErrorT $ f x) $
            EmbedR { bound = [] , free = freeVarsDB0 x }

----------------------------------------------------------------------

data EmbedR = EmbedR { bound :: [Ident] , free :: [NomVar] }
type EmbedM = ErrorT String (Reader EmbedR)

embedV' :: Val -> EmbedM Infer
embedV' VUnit = return IUnit
embedV' VBool = return IBool
embedV' VString = return IString
embedV' VDesc = return IDesc
embedV' VProg = return IProg
embedV' VType = return IType
embedV' VTT = return ITT
embedV' VTrue = return ITrue
embedV' VFalse = return IFalse
embedV' (VQuotes str) = return $ IQuotes str

embedV' VDUnit = return IDUnit
embedV' VDRec = return IDRec
embedV' (VDSum d e) = IDSum <$> embedVC' d <*> embedVC' e
embedV' (VDPi aT fD) = IDPi <$> embedVC' aT <*> embedVBC' fD
embedV' (VDSg aT fD) = IDSg <$> embedVC' aT <*> embedVBC' fD

embedV' (VPi aT bT) = IPi <$> embedVC' aT <*> embedVBC' bT
embedV' (VSg aT bT) = ISg <$> embedVC' aT <*> embedVBC' bT
embedV' (VFix d) = IFix <$> embedVC' d
embedV' (VLam aT b) = ILamAnn <$> embedVC' aT <*> embedVB' b
embedV' (VPair aT bT a b) = IAnn <$>
  (CPair <$> embedVC' a <*> embedVC' b) <*>
  (Infer <$> (ISg <$> embedVC' aT <*> embedVBC' bT))
embedV' (VIn d a) = IAnn <$>
  (CIn <$> embedVC' a) <*>
  (Infer <$> (IFix <$> embedVC' d))
embedV' (Neut n) = embedN' n
embedV' (VDefs _) = throwError
  "TODO Embedding' Is programs is not supported yet."

embedN' :: Neut -> EmbedM Infer
embedN' (NVar n@(NomVar (l , k))) = do
  is <- asks bound
  if k >= length is
  then return $ IVar l         -- Free.
  else return $ IVar (is !! k) -- Bound.
embedN' (NStrAppendL s1 s2) = IStrAppend <$> embedNC' s1 <*> embedVC' s2
embedN' (NStrAppendR s1 s2) = IStrAppend <$> embedVC' s1 <*> embedNC' s2
embedN' (NStrEqL s1 s2) = IStrEq <$> embedNC' s1 <*> embedVC' s2
embedN' (NStrEqR s1 s2) = IStrEq <$> embedVC' s1 <*> embedNC' s2
embedN' (NIf b c1 c2) = IIf <$> embedNC' b <*> embedV' c1 <*> embedV' c2
embedN' (NCaseBool pT pt pf b) =
  ICaseBool <$> embedVBC' pT <*> embedVC' pt <*> embedVC' pf <*> embedNC' b
embedN' (NProj1 ab) = IProj1 <$> embedN' ab
embedN' (NProj2 ab) = IProj2 <$> embedN' ab
embedN' (NApp f a) = IApp <$> embedN' f <*> embedVC' a
embedN' (NDInterp d e) = IDInterp <$> embedNC' d <*> embedVC' e

----------------------------------------------------------------------

inferToCheck :: Infer -> Check
inferToCheck (IAnn a' _) = a'
inferToCheck (ILamAnn _ (Bound (l , a'))) = CLam $ Bound (l , Infer a')
inferToCheck a' = Infer a'

embedVB' :: Bound Val -> EmbedM (Bound Infer)
embedVB' = liftEmbedBound embedV'

embedNB' :: Bound Neut -> EmbedM (Bound Infer)
embedNB' = liftEmbedBound embedN'

embedVC' :: Val -> EmbedM Check
embedVC' v =  inferToCheck <$> embedV' v

embedNC' :: Neut -> EmbedM Check
embedNC' n = inferToCheck <$> embedN' n

embedVBC' :: Bound Val -> EmbedM (Bound Check)
embedVBC' = liftEmbedBound embedVC'

embedNBC' :: Bound Neut -> EmbedM (Bound Check)
embedNBC' = liftEmbedBound embedNC'

-- Lift an embedder for 'a's to an embedder for bound 'a's.
liftEmbedBound :: (a -> EmbedM b) -> Bound a -> EmbedM (Bound b)
liftEmbedBound embed (Bound (l , a)) = do
  EmbedR { bound , free } <- ask
  let freeNames     = [ l | NomVar (l , _) <- free ]
      (l' , bound') = extendIdents l bound freeNames
  a' <- local (\r -> r { bound = bound' }) $ embed a
  return $ Bound (l' , a')

-- Add 'l' to 'is', freshening by appending primes if necessary.
extendIdents :: Ident -> [Ident] -> [Ident] -> (Ident , [Ident])
extendIdents l bound free = if l `elem` bound ++ free &&
                       l /= "_" -- Don't freshen wild card.
                    then extendIdents (l ++ "'") bound free
                    else (l , l:bound)

----------------------------------------------------------------------