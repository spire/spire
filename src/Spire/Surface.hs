module Spire.Surface where
import Spire.Neutral
import Control.Monad.Error
import Data.List

----------------------------------------------------------------------

type Ident = String
type NomBound a = Bound (Ident , a)
type Ctx = [(Ident , Type)]
type Def = (Ident , Check , Check)

data Check =
    CPair Check Check
  | CLam (NomBound Check)
  | Infer Infer
  deriving ( Eq, Show, Read )

data Infer =
    ITT | ITrue | IFalse
  | ILamAnn Check (NomBound Infer)
  | IUnit | IBool | IProg | IType
  | IPi Check (NomBound Check)
  | ISg Check (NomBound Check)
  | IDefs [Def]
  | IVar Ident
  | IIf Check Infer Infer
  | ICaseBool (NomBound Check) Check Check Check
  | IProj1 Infer
  | IProj2 Infer
  | IApp Infer Check
  | IAnn Check Check
  deriving ( Eq, Show, Read )

----------------------------------------------------------------------

{-
Do not explicitly inspect `NomBound' variables in `check' and `infer'.
Instead, use helper functions like `checkExtend', which correctly
extend the context.
-}

check :: Ctx -> Check -> Type -> Result Val
check ctx (CLam b) (VPi aT bT) = do
  b' <- checkExtend2 aT ctx b bT
  return $ VLam aT b'
check ctx (CPair a b) (VSg aT bT) = do
  a' <- check ctx a aT
  b' <- check ctx b (suB a' bT)
  return $ VPair a' b'
check ctx (Infer a) bT = do
  (a' , aT) <- infer ctx a
  unless (aT == bT) $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ show bT ++
    "\n\nInferred type:\n" ++ show aT ++
    "\n\nContext:\n" ++ show ctx ++
    "\n\nUnevaluated value:\n" ++ show a
  return $ a'
check ctx a aT = throwError "Ill-typed!"

infer :: Ctx -> Infer -> Result (Val , Type)
infer ctx ITT    = return (VTT , VUnit)
infer ctx ITrue  = return (VTrue , VBool)
infer ctx IFalse = return (VFalse , VBool)
infer ctx IUnit  = return (VUnit , VType)
infer ctx IBool  = return (VBool , VType)
infer ctx IProg  = return (VProg , VType)
infer ctx IType  = return (VType , VType)
infer ctx (ILamAnn aT b) = do
  aT'       <- check ctx aT VType
  (b' , bT) <- inferExtend aT' ctx b
  return (VLam aT' b' , VPi aT' bT)
infer ctx (IPi aT bT) = do
  aT' <- check ctx aT VType
  bT' <- checkExtend aT' ctx bT VType
  return (VPi aT' bT' , VType)
infer ctx (ISg aT bT) = do
  aT' <- check ctx aT VType
  bT' <- checkExtend aT' ctx bT VType
  return (VSg aT' bT' , VType)
infer ctx (IDefs as) = do
  as' <- checkDefs [] ctx as
  return (VDefs as' , VProg)
infer ctx (IIf b c1 c2) = do
  b'         <- check ctx b VBool
  (c1' , cT1)  <- infer ctx c1
  (c2' , cT2) <- infer ctx c2
  unless (cT1 == cT2) $ throwError $
    "Ill-typed, conditional branches have different types!\n" ++
    "First branch:\n" ++ show cT1 ++
    "\nSecond branch:\n" ++ show cT2
  return (evalIf b' c1' c2' , cT1)
infer ctx (ICaseBool pT pt pf b) = do
  pT' <- checkExtend VBool ctx pT VType
  pt' <- check ctx pt (suB VTrue pT')
  pf' <- check ctx pf (suB VFalse pT')
  b'  <- check ctx b VBool
  return (evalCaseBool pT' pt' pf' b' , suB b' pT')
infer ctx (IProj1 ab) = do
  (ab' , abT) <- infer ctx ab
  case abT of
    VSg aT bT -> return (evalProj1 ab' , aT)
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ show ab ++
      "\nProjected type:\n" ++ show abT
infer ctx (IProj2 ab) = do
  (ab' , abT) <- infer ctx ab
  case abT of
    VSg aT bT -> return (evalProj2 ab' , suB (evalProj1 ab') bT)
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ show ab ++
      "\nProjected type:\n" ++ show abT
infer ctx (IApp f a) = do
  (f' , fT) <- infer ctx f
  case fT of
    VPi aT bT -> do
      a' <- check ctx a aT
      return (evalApp f' a' , suB a' bT)
    _ -> throwError $
      "Ill-typed, application of non-function!\n" ++
      "Applied value:\n"  ++ show f ++
      "\nApplied type:\n"  ++ show fT
infer ctx (IVar l) =
  case findIndex (\(l' , _) -> l == l') ctx of
    Nothing -> throwError $
      "Variable not in context!\n" ++
      "Referenced variable:\n" ++ l ++
      "\nCurrent context:\n" ++ show (map fst ctx)
    Just i ->
      return (Neut (NVar i) , snd (ctx !! i))
infer ctx (IAnn a aT) = do
  aT' <- check ctx aT VType
  a'  <- check ctx a aT'
  return (a' , aT')

----------------------------------------------------------------------

checkExtend2 :: Type -> Ctx -> NomBound Check -> Bound Type -> Result (Bound Val)
checkExtend2 aT ctx b (Bound bT) = checkExtend aT ctx b bT

checkExtend :: Type -> Ctx -> NomBound Check -> Type -> Result (Bound Val)
checkExtend aT ctx (Bound (l , b)) bT = return . Bound =<< check ((l , aT) : ctx) b bT

inferExtend :: Type -> Ctx -> NomBound Infer -> Result (Bound Val , Bound Type)
inferExtend aT ctx (Bound (l , b)) = do
  (b' , bT) <- infer ((l , aT) : ctx) b
  return (Bound b' , Bound bT)

checkDefs :: [Val] -> Ctx -> [Def] -> Result [(Val , Type)]
checkDefs x ctx [] = return []
checkDefs xs ctx ((l , a , aT) : as) = do
  aT' <- return . foldSub xs =<< check ctx aT VType
  a' <- return . foldSub xs =<< check ctx a aT'
  as' <- checkDefs (a' : xs) ((l , aT') : ctx) as
  return ((a' , aT') : as')

----------------------------------------------------------------------