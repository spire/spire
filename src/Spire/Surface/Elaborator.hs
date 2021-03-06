module Spire.Surface.Elaborator (elabProg) where
import Data.List
import Control.Monad.Except
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Applicative
import Unbound.LocallyNameless
import Spire.Canonical.Types
import Spire.Surface.Types
import Spire.Expression.Types

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
elabForm _N = sDef _N (nepic "Form" _N) (_Former _N)

elabElim :: String -> Stmt
elabElim _N = let nm = "elim" ++ _N
  in sDef nm (nepic "elim" _N) (nepic "Elim" _N)

elabInj :: String -> String -> Syntax -> Stmt
elabInj _N l t = sDef l
  (nepic "inj" _N `SApp` t)
  (nepic "Inj" _N `SApp` t)

elabInjs :: String -> [String] -> Stmts
elabInjs _N _E = snd $ mapAccumL
  (\ t l -> (SThere t , elabInj _N l t))
  SHere _E

elabName :: String -> Stmt
elabName _N = let nm = _N ++ "N"
  in sDef nm (SQuotes _N) sString

elabEnum :: String -> [String] -> Stmt
elabEnum _N _E = let
  nm = _N ++ "E"
  _E' = foldr (sCons . SQuotes) sNil _E
  in sDef nm _E' sEnum

elabParams :: String -> [(String , Syntax)] -> Stmt
elabParams _N _Ps = let
  nm = _N ++ "P"
  _P = foldr (\(nm , _A) -> sExt _A . sLam nm) sEmp _Ps
  in sDef nm _P sTel

elabIndices :: String -> [String] -> [(String , Syntax)] -> Stmt
elabIndices _N _Ps _Is = let
  nm = _N ++ "I"
  freeI = foldr (\(a , _A) -> sExt _A . sLam a) sEmp _Is
  _I = foldr sLam freeI _Ps
  in sDef nm (indices _N _I) (_Indices _N)

elabConstrs :: String -> [String] -> [[Constr]] -> Stmt
elabConstrs _N _Ps css = let
  nm = _N ++ "C"
  freeC = foldr SPair sTT (map elabConstr css)
  _C = foldr sLam freeC _Ps
  in sDef nm (constrs _N _C) (_Constrs _N)

elabConstr :: [Constr] -> Syntax
elabConstr [] = error "constructor without type signature"
elabConstr (Fix _I : []) = SEnd (foldr SPair sTT _I)
elabConstr (Fix _I : cs) = SRec (foldr SPair sTT _I) (elabConstr cs)
elabConstr (Arg a _A : cs) = SArg _A (sbind a $ elabConstr cs)

----------------------------------------------------------------------

elab :: Syntax -> SpireM Check
elab s = flip runReaderT [] . elabC $ s

type SpireM' = ReaderT [Nom] SpireM

elabC :: Syntax -> SpireM' Check

elabC SRefl          = return CRefl
elabC SHere          = return CHere
elabC (SThere t)     = CThere <$> elabC  t
elabC (SEnd   i)     = CEnd   <$> elabC  i
elabC (SRec   i  _D) = CRec   <$> elabC  i  <*> elabC  _D
elabC (SInit  xs)    = CInit  <$> elabC  xs
elabC (SArg   _A _B) = CArg   <$> elabC  _A <*> elabBC _B
elabC (SPair  a b)   = CPair  <$> elabC  a  <*> elabC  b
elabC (SLam   b)     = CLam   <$> elabBC b

elabC x@(SQuotes _)         = elabIC x
elabC x@(SPi _ _)           = elabIC x
elabC x@(SSg _ _)           = elabIC x
elabC x@(SEq _ _)           = elabIC x
elabC x@(SVar _)            = elabIC x
elabC x@(SIf _ _ _)         = elabIC x
elabC x@(SApp _ _)          = elabIC x
elabC x@(SAnn _ _)          = elabIC x
elabC x@(SWildCard)         = elabIC x

----------------------------------------------------------------------

elabI :: Syntax -> SpireM' Infer

elabI (SQuotes s) = return $ IQuotes s
elabI (SVar nm)   = return $ IVar nm

elabI SWildCard = return $ IVar (s2n wildcard)

elabI (SApp f a)    = IApp   <$> elabI f <*> elabC a
elabI (SIf b ct cf) = IIf    <$> elabC b <*> elabI ct <*> elabI cf
elabI (SAnn a _A)   = IAnn   <$> elabC a <*> elabC _A

elabI (SPi _A _B)       = IPi       <$> elabC _A <*> elabBC _B
elabI (SSg _A _B)       = ISg       <$> elabC _A <*> elabBC _B
elabI (SEq a b)         = IEq       <$> elabI a  <*> elabI b

-- once we have meta variables, we should always be able to infer a type for 
-- a lambda, by inserting a meta variable to type the domain of the lambda,
-- but a pair will still fail because any inferred type for the RHS
-- is a specialized version of a more general type (in which a universal variable
-- standing for the LHS is free).
elabI x@SRefl       = failUnannotated x
elabI x@SHere       = failUnannotated x
elabI x@(SThere _)  = failUnannotated x
elabI x@(SEnd   _)  = failUnannotated x
elabI x@(SRec  _ _) = failUnannotated x
elabI x@(SInit _)   = failUnannotated x
elabI x@(SArg  _ _) = failUnannotated x
elabI x@(SPair _ _) = failUnannotated x
elabI x@(SLam _)    = failUnannotated x

----------------------------------------------------------------------

elabBC :: Bind Nom Syntax -> SpireM' (Bind Nom Check)
elabBC bnd = do
  (nm , a) <- unbind bnd
  -- Store names in binding order.
  a'       <- local (++ [nm]) $ elabC a
  return   $  bind nm a'

elabBC3 :: Bind Nom3 Syntax -> SpireM' (Bind Nom3 Check)
elabBC3 bnd = do
  ((nm1 , nm2 , nm3) , a) <- unbind bnd
  -- Store names in binding order.
  a'       <- local (++ [nm1 , nm2 , nm3]) $ elabC a
  return   $  bind (nm1 , nm2 , nm3) a'

failUnannotated :: Syntax -> SpireM' Infer
failUnannotated a = throwError $
  "Failed to infer the type of this term, please annotate it:\n" ++
  show a

elabIC :: Syntax -> SpireM' Check
elabIC x = Infer <$> elabI x

----------------------------------------------------------------------
