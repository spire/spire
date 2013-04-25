module Spire.Canonical.Embedding where
import Spire.Expression.Types
import Spire.Canonical.Types

----------------------------------------------------------------------

embedV :: Val -> Infer
embedV VUnit = IUnit
embedV VBool = IBool
embedV VString = IString
embedV VProg = IProg
embedV VType = IType
embedV VTT = ITT
embedV VTrue = ITrue
embedV VFalse = IFalse
embedV (VQuotes str) = IQuotes str

embedV (VPi aT bT) = IPi (embedVC aT) (embedVBC bT)
embedV (VSg aT bT) = ISg (embedVC aT) (embedVBC bT)
embedV (VLam aT b) = ILamAnn (embedVC aT) (embedVB b)
embedV (VPair aT bT a b) = IAnn
  (CPair (embedVC a) (embedVC b))
  (Infer (ISg (embedVC aT) (embedVBC bT)))
embedV (Neut n) = embedN n
embedV (VDefs _) = error "TODO Embedding programs is not supported yet."

embedN :: Neut -> Infer
embedN (NVar (NomVar (l , _))) = IVar l
embedN (NStrAppendL s1 s2) = IStrAppend (embedNC s1) (embedVC s2)
embedN (NStrAppendR s1 s2) = IStrAppend (embedVC s1) (embedNC s2)
embedN (NStrEqL s1 s2) = IStrEq (embedNC s1) (embedVC s2)
embedN (NStrEqR s1 s2) = IStrEq (embedVC s1) (embedNC s2)
embedN (NIf b c1 c2) = IIf (embedNC b) (embedV c1) (embedV c2)
embedN (NCaseBool pT pt pf b) =
  ICaseBool (embedVBC pT) (embedVC pt) (embedVC pf) (embedNC b)
embedN (NProj1 ab) = IProj1 (embedN ab)
embedN (NProj2 ab) = IProj2 (embedN ab)
embedN (NApp f a) = IApp (embedN f) (embedVC a)

----------------------------------------------------------------------

inferToCheck :: Infer -> Check
inferToCheck (IAnn a' _) = a'
inferToCheck (ILamAnn _ (Bound (l , a'))) = CLam $ Bound (l , Infer a')
inferToCheck a' = Infer a'

embedVB :: Bound Val -> Bound Infer
embedVB (Bound (l , a)) = Bound (l , embedV a)

embedNB :: Bound Neut -> Bound Infer
embedNB (Bound (l , a)) = Bound (l , embedN a)

embedVC :: Val -> Check
embedVC =  inferToCheck . embedV

embedNC :: Neut -> Check
embedNC = inferToCheck . embedN

embedVBC :: Bound Val -> Bound Check
embedVBC (Bound (l , a)) = Bound (l , embedVC a)

embedNBC :: Bound Neut -> Bound Check
embedNBC (Bound (l , a)) = Bound (l , embedNC a)

----------------------------------------------------------------------