module Spire.Canonical.Embedding (embedV , embedN , embedVC) where
import Spire.Expression.Types
import Spire.Canonical.Types

----------------------------------------------------------------------

embedV :: Val -> Infer
embedV = embedV' []

embedN :: Neut -> Infer
embedN = embedN' []

embedVC :: Val -> Check
embedVC = embedVC' []

----------------------------------------------------------------------

embedV' :: [Ident] -> Val -> Infer
embedV' is VUnit = IUnit
embedV' is VBool = IBool
embedV' is VString = IString
embedV' is VDesc = IDesc
embedV' is VProg = IProg
embedV' is VType = IType
embedV' is VTT = ITT
embedV' is VTrue = ITrue
embedV' is VFalse = IFalse
embedV' is (VQuotes str) = IQuotes str

embedV' is VDUnit = IDUnit
embedV' is VDRec = IDRec
embedV' is (VDSum d e) = IDSum (embedVC' is d) (embedVC' is e)
embedV' is (VDPi aT fD) = IDPi (embedVC' is aT) (embedVBC' is fD)
embedV' is (VDSg aT fD) = IDSg (embedVC' is aT) (embedVBC' is fD)

embedV' is (VPi aT bT) = IPi (embedVC' is aT) (embedVBC' is bT)
embedV' is (VSg aT bT) = ISg (embedVC' is aT) (embedVBC' is bT)
embedV' is (VFix d) = IFix (embedVC' is d)
embedV' is (VLam aT b) = ILamAnn (embedVC' is aT) (embedVB' is b)
embedV' is (VPair aT bT a b) = IAnn
  (CPair (embedVC' is a) (embedVC' is b))
  (Infer (ISg (embedVC' is aT) (embedVBC' is bT)))
embedV' is (VIn d a) = IAnn
  (CIn (embedVC' is a))
  (Infer (IFix (embedVC' is d)))
embedV' is (Neut n) = embedN' is n
embedV' is (VDefs _) = error "TODO Embedding' Is programs is not supported yet."

embedN' :: [Ident] -> Neut -> Infer
embedN' is (NVar n@(NomVar (_ , k))) =
  if k >= length is
  -- XXX: this is more evidence that 'embed*' should be in a monad:
  -- then we could raise monadic errors, and thread the binders using
  -- a reader (in other words: once you give up and go into a monad,
  -- it's easier to do other monadic things).
  then error $
         "Internal error: DeBruijn variable unbound in 'embedN':\n" ++
         "var = " ++ show n ++ ", binders = " ++ show is
  else IVar (is !! k)
embedN' is (NStrAppendL s1 s2) = IStrAppend (embedNC' is s1) (embedVC' is s2)
embedN' is (NStrAppendR s1 s2) = IStrAppend (embedVC' is s1) (embedNC' is s2)
embedN' is (NStrEqL s1 s2) = IStrEq (embedNC' is s1) (embedVC' is s2)
embedN' is (NStrEqR s1 s2) = IStrEq (embedVC' is s1) (embedNC' is s2)
embedN' is (NIf b c1 c2) = IIf (embedNC' is b) (embedV' is c1) (embedV' is c2)
embedN' is (NCaseBool pT pt pf b) =
  ICaseBool (embedVBC' is pT) (embedVC' is pt) (embedVC' is pf) (embedNC' is b)
embedN' is (NProj1 ab) = IProj1 (embedN' is ab)
embedN' is (NProj2 ab) = IProj2 (embedN' is ab)
embedN' is (NApp f a) = IApp (embedN' is f) (embedVC' is a)
embedN' is (NDInterp d e) = IDInterp (embedNC' is d) (embedVC' is e)

----------------------------------------------------------------------

inferToCheck :: Infer -> Check
inferToCheck (IAnn a' _) = a'
inferToCheck (ILamAnn _ (Bound (l , a'))) = CLam $ Bound (l , Infer a')
inferToCheck a' = Infer a'

embedVB' :: [Ident] -> Bound Val -> Bound Infer
embedVB' is (Bound (l , a)) = Bound (l' , embedV' is' a)
  where
  (l' , is') = extendIdents l is

embedNB' :: [Ident] -> Bound Neut -> Bound Infer
embedNB' is (Bound (l , a)) = Bound (l' , embedN' is' a)
  where
  (l' , is') = extendIdents l is

embedVC' :: [Ident] -> Val -> Check
embedVC' is =  inferToCheck . embedV' is

embedNC' :: [Ident] -> Neut -> Check
embedNC' is = inferToCheck . embedN' is

embedVBC' :: [Ident] -> Bound Val -> Bound Check
embedVBC' is (Bound (l , a)) = Bound (l' , embedVC' is' a)
  where
  (l' , is') = extendIdents l is

embedNBC' :: [Ident] -> Bound Neut -> Bound Check
embedNBC' is (Bound (l , a)) = Bound (l' , embedNC' is' a)
  where
  (l' , is') = extendIdents l is

-- Add 'l' to 'is', freshening by appending primes if necessary.
extendIdents :: Ident -> [Ident] -> (Ident , [Ident])
extendIdents l is = if l `elem` is &&
                       l /= "_" -- Don't freshen wild card.
                    then extendIdents (l ++ "'") is
                    else (l , l:is)

----------------------------------------------------------------------