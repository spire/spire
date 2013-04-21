module Spire.Canonical.Embedding where
import Spire.Expression.Types
import Spire.Canonical.Types

----------------------------------------------------------------------

embedV :: Val -> Infer
embedV VUnit = IUnit
embedV VBool = IBool
embedV VProg = IProg
embedV VType = IType
embedV VTT = ITT
embedV VTrue = ITrue
embedV VFalse = IFalse

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
embedN (NIf b c1 c2) = IIf (embedNC b) (embedV c1) (embedV c2)
embedN (NCaseBool pT pt pf b) =
  ICaseBool (embedVBC pT) (embedVC pt) (embedVC pf) (embedNC b)
embedN (NProj1 ab) = IProj1 (embedN ab)
embedN (NProj2 ab) = IProj2 (embedN ab)
embedN (NApp f a) = IApp (embedN f) (embedVC a)

----------------------------------------------------------------------

embedVB :: Bound Val -> Bound Infer
embedVB (Bound (l , a)) = Bound (l , embedV a)

embedNB :: Bound Neut -> Bound Infer
embedNB (Bound (l , a)) = Bound (l , embedN a)

embedVC :: Val -> Check
embedVC a = Infer $ embedV a

embedNC :: Neut -> Check
embedNC a = Infer $ embedN a

embedVBC :: Bound Val -> Bound Check
embedVBC (Bound (l , a)) = Bound (l , embedVC a)

embedNBC :: Bound Neut -> Bound Check
embedNBC (Bound (l , a)) = Bound (l , embedNC a)

----------------------------------------------------------------------