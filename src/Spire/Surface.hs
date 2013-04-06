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

check :: Ctx -> Check -> Type -> Result Val
check ctx (CLam f) (VPi a b) = do
  f' <- check (a : ctx) f b
  return $ VLam f'
check ctx (CPair x y) (VSg a b) = do
  x' <- check ctx x a
  y' <- check ctx y (subV 0 x' b)
  return $ VPair x' y'
  
check ctx (Infer tm) tp = do
  (tm' , tp') <- infer ctx tm
  unless (tp == tp') $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ printV tp ++
    "\nInferred type:\n" ++ printV tp'
  return $ tm'
check ctx tm tp = throwError "Ill-typed!"

----------------------------------------------------------------------

infer :: Ctx -> Infer -> Result (Val , Type)
infer ctx ITT    = return (VTT , VUnit)
infer ctx ITrue  = return (VTrue , VBool)
infer ctx IFalse = return (VFalse , VBool)
infer ctx IUnit  = return (VUnit , VType)
infer ctx IBool  = return (VBool , VType)
infer ctx IType  = return (VType , VType)
infer ctx (IPi a b) = do
  a' <- check ctx a VType
  b' <- check (a' : ctx) b VType
  return (VPi a' b' , VType)
infer ctx (ISg a b) = do
  a' <- check ctx a VType
  b' <- check (a' : ctx) b VType
  return (VSg a' b' , VType)
infer ctx (IIf b c1 c2) = do
  b'         <- check ctx b VBool
  (c1' , c)  <- infer ctx c1
  (c2' , c') <- infer ctx c2
  unless (c == c') $ throwError $
    "Ill-typed, conditional branches have different types!\n" ++
    "First branch:\n" ++ printV c ++
    "\nSecond branch:\n" ++ printV c'
  return (evalIf b' c1' c2' , c)
infer ctx (ICaseBool p pt pf b) = do
  p'  <- check (VBool : ctx) p VType
  pt' <- check ctx pt (subV 0 VTrue p')
  pf' <- check ctx pf (subV 0 VFalse p')
  b'  <- check ctx b VBool
  return (evalCaseBool p' pt' pf' b' , subV 0 b' p')
infer ctx (IProj1 xy) = do
  (xy' , ab) <- infer ctx xy
  case ab of
    VSg a b -> return (evalProj1 xy' , a)
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ show xy ++
      "\nProjected type:\n" ++ printV ab
infer ctx (IProj2 xy) = do
  (xy' , ab) <- infer ctx xy
  case ab of
    VSg a b -> return (evalProj2 xy' , subV 0 (evalProj1 xy') b)
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ show xy ++
      "\nProjected type:\n" ++ printV ab
infer ctx (IApp f x) = do
  (f' , ab) <- infer ctx f
  case ab of
    VPi a b -> do
      a' <- check ctx x a
      return (evalApp f' a' , subV 0 a' b)
    _ -> throwError $
      "Ill-typed, application of non-function!\n" ++
      "Applied value:\n"  ++ show f ++
      "\nApplied type:\n"  ++ printV ab
infer ctx (IVar i) = return (Neut (NVar i) , ctx !! fromInteger i)
infer ctx (IAnn tm tp) = do
  tp' <- check ctx tp VType
  tm' <- check ctx tm tp'
  return (tm' , tp')

----------------------------------------------------------------------