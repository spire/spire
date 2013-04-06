module Spire.Surface where
import Spire.Neutral
import Control.Monad.Error
import Data.List

----------------------------------------------------------------------

type Ident = String
type Ctx = [(Ident , Type)]
type Result a = Either String a

data Check =
    CPair Check Check
  | CLam Ident Check
  | Infer Infer
  deriving ( Eq, Show, Read )

data Infer =
    ITT | ITrue | IFalse
  | IUnit | IBool | IType
  | IPi Check Ident Check
  | ISg Check Ident Check
  | IVar Ident
  | IIf Check Infer Infer
  | ICaseBool Ident Check Check Check Check
  | IProj1 Infer
  | IProj2 Infer
  | IApp Infer Check
  | IAnn Check Check
  deriving ( Eq, Show, Read )

----------------------------------------------------------------------

check :: Ctx -> Check -> Type -> Result Val
check ctx (CLam l f) (VPi a b) = do
  f' <- check ((l , a) : ctx) f b
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
infer ctx (IPi a l b) = do
  a' <- check ctx a VType
  b' <- check ((l , a') : ctx) b VType
  return (VPi a' b' , VType)
infer ctx (ISg a l b) = do
  a' <- check ctx a VType
  b' <- check ((l , a') : ctx) b VType
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
infer ctx (ICaseBool l p pt pf b) = do
  p'  <- check ((l , VBool) : ctx) p VType
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
infer ctx (IVar l) =
  case findIndex (\(l' , _) -> l == l') ctx of
    Nothing -> throwError $
      "Variable not in context!\n" ++
      "Referenced variable:\n" ++ l ++
      "\nCurrent context:\n" ++ show (map fst ctx)
    Just i ->
      return (Neut (NVar (toInteger i)) , snd (ctx !! i))
infer ctx (IAnn tm tp) = do
  tp' <- check ctx tp VType
  tm' <- check ctx tm tp'
  return (tm' , tp')

----------------------------------------------------------------------