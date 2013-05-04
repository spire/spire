module Spire.Expression.Embedding where
import Spire.Canonical.Types
import Spire.Expression.Types
import Spire.Surface.Types

----------------------------------------------------------------------

embedI :: Infer -> Syntax
embedI ITT = STT
embedI ITrue = STrue
embedI IFalse = SFalse
embedI (IQuotes s) = SQuotes s
-- XXX: this is wrong: may need the domain typing info in 'c', but
-- there is nowhere to put it ... could maybe infer a type for the
-- 'ILamAnn', and then wrap with 'SAnn'?
embedI (ILamAnn c bi) = SLam (embedIB bi)
embedI IUnit = SUnit
embedI IBool = SBool
embedI IString = SString
embedI IDesc = SDesc
embedI IProg = error "TODO Embedding programs is not supported yet."
embedI IType = SType
embedI (IPi c bc) = SPi (embedC c) (embedCB bc)
embedI (ISg c bc) = SSg (embedC c) (embedCB bc)
embedI (IFix c) = SFix (embedC c)

embedI IDUnit = SDUnit
embedI IDRec = SDRec
embedI (IDSum c1 c2) = SDSum (embedC c1) (embedC c2)
embedI (IDPi c bc) = SDPi (embedC c) (embedCB bc)
embedI (IDSg c bc) = SDSg (embedC c) (embedCB bc)
embedI (IDInterp _ _) = error "TODO Embedding the meaning function of descriptions is not yet supported."

embedI (IDefs _) = error "TODO Embedding programs is not supported yet."
embedI (IVar v) = SVar v
embedI (IStrAppend c1 c2) = SStrAppend (embedC c1) (embedC c2)
embedI (IStrEq c1 c2) = SStrEq (embedC c1) (embedC c2)
embedI (IIf c i1 i2) = SIf (embedC c) (embedI i1) (embedI i2)
embedI (ICaseBool bc c1 c2 c3) = SCaseBool (embedCB bc) (embedC c1) (embedC c2) (embedC c3)
embedI (IProj1 i) = SProj1 (embedI i)
embedI (IProj2 i) = SProj2 (embedI i)
embedI (IApp i c) = SApp (embedI i) (embedC c)
embedI (IAnn c1 c2) = SAnn (embedC c1) (embedC c2)

embedC :: Check -> Syntax
embedC (CPair c1 c2) = SPair (embedC c1) (embedC c2)
embedC (CLam bc) = SLam (embedCB bc)
embedC (CIn c) = SIn (embedC c)
embedC (Infer i) = embedI i

----------------------------------------------------------------------

embedCB :: Bound Check -> Bound Syntax
embedCB (Bound (l , c)) = Bound (l , embedC c)

embedIB :: Bound Infer -> Bound Syntax
embedIB (Bound (l , i)) = Bound (l , embedI i)

embedD :: Def -> Statement
embedD (f , e , t) = SDef f (embedC e) (embedC t)

----------------------------------------------------------------------
