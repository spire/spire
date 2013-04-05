module Spire.Surface where
import Spire.Neutral
import Control.Monad.Error

----------------------------------------------------------------------

type Result a = Either String a

data Check =
    CPair Check Check
  | CLam Check
  | Infer Infer
  deriving ( Eq, Show, Read )

data Infer =
    ITT | ITrue | IFalse
  | IUnit | IBool | IType
  | IPi Check Check
  | ISg Check Check
  | IVar Var
  | IIf Check Infer Infer
  | ICaseBool Check Check Check Check
  | IProj1 Infer
  | IProj2 Infer
  | IApp Infer Check
  | IAnn Check Check
  deriving ( Eq, Show, Read )

----------------------------------------------------------------------

evalC :: Check -> Val
evalC (CPair a b) = VPair (evalC a) (evalC b)
evalC (CLam f) = VLam (evalC f)
evalC (Infer a) = evalI a

evalI :: Infer -> Val
evalI ITT = VTT
evalI ITrue = VTrue
evalI IFalse = VFalse
evalI IUnit = VUnit
evalI IBool = VBool
evalI IType = VType
evalI (IPi a b) = VPi (evalC a) (evalC b)
evalI (ISg a b) = VSg (evalC a) (evalC b)
evalI (IVar i) = Neut $ NVar i
evalI (IIf b c1 c2) = evalIf (evalC b) (evalI c1) (evalI c2)
evalI (ICaseBool p pt pf b) = evalCaseBool (evalC p) (evalC pt) (evalC pf) (evalC b)
evalI (IProj1 ab) = evalProj1 (evalI ab)
evalI (IProj2 ab) = evalProj2 (evalI ab)
evalI (IApp f a) = evalApp (evalI f) (evalC a)
evalI (IAnn a _) = evalC a

----------------------------------------------------------------------

check :: Ctx -> Check -> Type -> Result Type
check ctx (CLam f) (VPi a b) = do
  check (a : ctx) f b
  return $ VPi a b
check ctx (CPair x y) (VSg a b) = do
  check ctx x a
  let x' = evalC x
  let b' = subV 0 x' b
  check ctx y b'
  return $ VSg a b'
  
check ctx (Infer tm) tp = do
  tp' <- infer ctx tm
  unless (tp == tp') $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ printV tp ++
    "\nInferred type:\n" ++ printV tp'
  return tp
check ctx tm tp = throwError "Ill-typed!"

infer :: Ctx -> Infer -> Result Type
infer ctx ITT = return VUnit
infer ctx ITrue = return VBool
infer ctx IFalse = return VBool
infer ctx IUnit = return VType
infer ctx IBool = return VType
infer ctx IType = return VType
infer ctx (IPi a b) = do
  check ctx a VType
  let a' = evalC a
  check (a' : ctx) b VType
  return VType
infer ctx (ISg a b) = do
  check ctx a VType
  let a' = evalC a
  check (a' : ctx) b VType
  return VType
infer ctx (IIf b c1 c2) = do
  check ctx b VBool
  c <- infer ctx c1
  c' <- infer ctx c2
  unless (c == c') $ throwError $
    "Ill-typed, conditional branches have different types!\n" ++
    "First branch:\n" ++ printV c ++
    "\nSecond branch:\n" ++ printV c'
  return c
infer ctx (ICaseBool p pt pf b) = do
  check (VBool : ctx) p VType
  let p' = evalC p
  check ctx pt (subV 0 VTrue p')
  check ctx pf (subV 0 VFalse p')
  check ctx b VBool
  return $ subV 0 (evalC b) p'
infer ctx (IProj1 xy) = do
  ab <- infer ctx xy
  case ab of
    VSg a b -> return a
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ show xy ++
      "\nProjected type:\n" ++ printV ab
infer ctx (IProj2 xy) = do
  ab <- infer ctx xy
  case ab of
    VSg a b -> return $ subV 0 (evalProj1 (evalI xy)) b
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ show xy ++
      "\nProjected type:\n" ++ printV ab
infer ctx (IApp f x) = do
  ab <- infer ctx f
  case ab of
    VPi a b -> do
      check ctx x a
      return (subV 0 (evalC x) b)
    _ -> throwError $
      "Ill-typed, application of non-function!\n" ++
      "Applied value:\n"  ++ show f ++
      "\nApplied type:\n"  ++ printV ab
infer ctx (IVar i) = return (ctx !! fromInteger i)
infer ctx (IAnn tm tp) = do
  check ctx tp VType
  let tp' = evalC tp
  check ctx tm tp'
  return tp'

----------------------------------------------------------------------