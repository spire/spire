module Spire.Surface.Elaborator where
import Data.List
import Control.Monad.Error
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Applicative
import Spire.Canonical.Types
import Spire.Surface.Types
import Spire.Expression.Types
import Spire.Bound
import qualified Bound.Scope.Simple as S

----------------------------------------------------------------------

elabProg :: SProg -> SpireM CProg
elabProg [] = return []
elabProg (SData _N _Ps _Is css : xs) = let
  _N' = elabName _N
  _E = elabEnum _N (map fst css)
  _P = elabParams _N _Ps
  _I = elabIndices _N (map fst _Ps) _Is
  _C = elabConstrs _N (map fst _Ps) (map snd css)
  _Form = elabForm _N
  _Injs = elabInjs _N (map fst css)
  _Elim = elabElim _N
  in elabProg $ [ _N' , _E , _P , _I , _C , _Form ]
    ++ _Injs ++ (_Elim : xs)
elabProg (SDef nm a _A : xs) = do
  _A' <- elab _A
  a'  <- elab a
  xs' <- elabProg xs
  return (CDef nm a' _A' : xs')

elabForm :: String -> Stmt
elabForm _N = SDef _N (nepic "Form" _N) (_Former _N)

elabElim :: String -> Stmt
elabElim _N = let nm = "elim" ++ _N
  in SDef nm (nepic "elim" _N) (nepic "Elim" _N)

elabInj :: String -> String -> Syntax -> Stmt
elabInj _N l t = SDef l
  (nepic "inj" _N `SApp` t)
  (nepic "Inj" _N `SApp` t)

elabInjs :: String -> [String] -> Stmts
elabInjs _N _E = snd $ mapAccumL
  (\ t l -> (SThere t , elabInj _N l t))
  SHere _E

elabName :: String -> Stmt
elabName _N = let nm = _N ++ "N"
  in SDef nm (SQuotes _N) sString

elabEnum :: String -> [String] -> Stmt
elabEnum _N _E = let
  nm = _N ++ "E"
  _E' = foldr (sCons . SQuotes) sNil _E
  in SDef nm _E' sEnum

elabParams :: String -> [(String , Syntax)] -> Stmt
elabParams _N _Ps = let
  nm = _N ++ "P"
  _P = foldr (\(nm , _A) -> sExt _A . SLam nm) sEmp _Ps
  in SDef nm _P sTel

elabIndices :: String -> [String] -> [(String , Syntax)] -> Stmt
elabIndices _N _Ps _Is = let
  nm = _N ++ "I"
  freeI = foldr (\(a , _A) -> sExt _A . SLam a) sEmp _Is
  _I = foldr SLam freeI _Ps
  in SDef nm (indices _N _I) (_Indices _N)

elabConstrs :: String -> [String] -> [[Constr]] -> Stmt
elabConstrs _N _Ps css = let
  nm = _N ++ "C"
  freeC = foldr SPair sTT (map elabConstr css)
  _C = foldr SLam freeC _Ps
  in SDef nm (constrs _N _C) (_Constrs _N)

elabConstr :: [Constr] -> Syntax
elabConstr [] = error "constructor without type signature"
elabConstr (Fix _I : []) = SEnd (foldr SPair sTT _I)
elabConstr (Fix _I : cs) = SRec (foldr SPair sTT _I) (elabConstr cs)
elabConstr (Arg nm _A : cs) = SArg nm _A (elabConstr cs)

----------------------------------------------------------------------

elab :: (Eq a , Free a) => Syntax -> SpireM (Check a)
elab = elabC

elabC :: (Eq a , Free a) => Syntax -> SpireM (Check a)

elabC SRefl          = return CRefl
elabC SHere          = return CHere
elabC (SThere t)     = CThere <$> elabC  t
elabC (SEnd   i)     = CEnd   <$> elabC  i
elabC (SRec   i  _D) = CRec   <$> elabC  i  <*> elabC  _D
elabC (SInit  xs)    = CInit  <$> elabC  xs
elabC (SArg nm _A _B) = CArg   <$> elabC  _A <*> elabBC (free nm) _B
elabC (SPair  a b)   = CPair  <$> elabC  a  <*> elabC  b
elabC (SLam nm b)     = CLam   <$> elabBC (free nm) b

elabC x@(SQuotes _)         = elabIC x
elabC x@(SPi _ _ _)           = elabIC x
elabC x@(SSg _ _ _)           = elabIC x
elabC x@(SEq _ _)           = elabIC x
elabC x@(SVar _)            = elabIC x
elabC x@(SIf _ _ _)         = elabIC x
elabC x@(SApp _ _)          = elabIC x
elabC x@(SAnn _ _)          = elabIC x
elabC x@(SWildCard)         = elabIC x

----------------------------------------------------------------------

elabI :: (Eq a , Free a) => Syntax -> SpireM (Infer a)

elabI (SQuotes s) = return . IQuotes $ s
elabI (SVar nm)   = return . IVar . free $ nm
elabI SWildCard   = return . IVar . free $ wildcard

elabI (SApp f a)    = IApp   <$> elabI f <*> elabC a
elabI (SIf b ct cf) = IIf    <$> elabC b <*> elabI ct <*> elabI cf
elabI (SAnn a _A)   = IAnn   <$> elabC a <*> elabC _A

elabI (SPi nm _A _B)       = IPi       <$> elabC _A <*> elabBC (free nm) _B
elabI (SSg nm _A _B)       = ISg       <$> elabC _A <*> elabBC (free nm) _B
elabI (SEq a b)         = IEq       <$> elabI a  <*> elabI b

-- once we have meta variables, we should always be able to infer a type for 
-- a lambda, by inserting a meta variable to type the domain of the lambda,
-- but a pair will still fail because any inferred type for the RHS
-- is a specialized version of a more general type (in which a universal variable
-- standing for the LHS is free).
elabI x@SRefl        = failUnannotated x
elabI x@SHere        = failUnannotated x
elabI x@(SThere _)   = failUnannotated x
elabI x@(SEnd   _)   = failUnannotated x
elabI x@(SRec  _ _)  = failUnannotated x
elabI x@(SInit _)    = failUnannotated x
elabI x@(SArg _ _ _) = failUnannotated x
elabI x@(SPair _ _)  = failUnannotated x
elabI x@(SLam _ _)   = failUnannotated x

----------------------------------------------------------------------

elabBC :: (Eq a , Free a) => a -> Syntax -> SpireM (SBind Nom Check a)
elabBC nm bnd = return . S.abstract1 nm =<< elabC bnd

failUnannotated :: Syntax -> SpireM (Infer a)
failUnannotated a = throwError $
  "Failed to infer the type of this term, please annotate it:\n" ++
  show a

elabIC :: (Eq a , Free a) => Syntax -> SpireM (Check a)
elabIC x = Infer <$> elabI x

----------------------------------------------------------------------
