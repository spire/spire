module Spire.Expression.CheckingAndEvaluation (checkDefsStable) where
import Spire.Canonical.Types
import Spire.Canonical.Embedding
import Spire.Canonical.HereditarySubstitution
import Spire.Expression.Types
import Spire.Surface.PrettyPrinting
import Control.Monad.Error
import Data.List

----------------------------------------------------------------------

check :: Ctx -> Check -> Type -> Result Val
check ctx (CLam b) (VPi aT bT) = do
  b' <- checkExtend2 aT ctx b bT
  return $ VLam aT b'
check ctx (CPair a b) (VSg aT bT) = do
  a' <- check ctx a aT
  b' <- check ctx b (sub a' bT)
  return $ VPair aT bT a' b'
check ctx (CIn a) (VFix d) = do
  a' <- check ctx a (evalDInterp d (VFix d))
  return $ VIn d a'
check ctx (Infer a) bT = do
  (a' , aT) <- infer ctx a
  unless (aT == bT) $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ prettyPrintError bT ++
    "\n\nInferred type:\n" ++ prettyPrintError aT ++
    "\n\nContext:\n" ++ prettyPrintError ctx ++
    "\n\nUnevaluated value:\n" ++ prettyPrintError a
  return $ a'
check ctx a aT = throwError "Ill-typed!"

infer :: Ctx -> Infer -> Result (Val , Type)
infer ctx ITT     = return (VTT , VUnit)
infer ctx ITrue   = return (VTrue , VBool)
infer ctx IFalse  = return (VFalse , VBool)
infer ctx IUnit   = return (VUnit , VType)
infer ctx IBool   = return (VBool , VType)
infer ctx IString = return (VString , VType)
infer ctx IDesc   = return (VDesc , VType)
infer ctx IProg   = return (VProg , VType)
infer ctx IType   = return (VType , VType)

infer ctx IDUnit  = return (VDUnit , VDesc)
infer ctx IDRec   = return (VDRec , VDesc)
infer ctx (IDSum d e) = do
  d' <- check ctx d VDesc
  e' <- check ctx e VDesc
  return (VDSum d' e' , VDesc)
infer ctx (IDPi aT fD) = do
  aT' <- check ctx aT VType
  fD' <- checkExtend aT' ctx fD VDesc
  return (VDPi aT' fD' , VDesc)
infer ctx (IDSg aT fD) = do
  aT' <- check ctx aT VType
  fD' <- checkExtend aT' ctx fD VDesc
  return (VDSg aT' fD' , VDesc)

infer ctx (IQuotes str) =
  return (VQuotes str , VString)
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
infer ctx (IFix d) = do
  d' <- check ctx d VDesc
  return (VFix d' , VType)
infer ctx (IDefs as) = do
  as' <- checkDefs [] ctx as
  let as'' = map (\(_ , a , aT) -> (a , aT))  as'
  return (VDefs as'' , VProg)
infer ctx (IStrAppend s1 s2) = do
 s1' <- check ctx s1 VString
 s2' <- check ctx s2 VString
 return (evalStrAppend s1' s2' , VString)
infer ctx (IStrEq s1 s2) = do
 s1' <- check ctx s1 VString
 s2' <- check ctx s2 VString
 return (evalStrEq s1' s2' , VBool)
infer ctx (IIf b c1 c2) = do
  b'          <- check ctx b VBool
  (c1' , cT1) <- infer ctx c1
  (c2' , cT2) <- infer ctx c2
  unless (cT1 == cT2) $ throwError $
    "Ill-typed, conditional branches have different types!\n" ++
    "First branch:\n" ++ prettyPrintError cT1 ++
    "\nSecond branch:\n" ++ prettyPrintError cT2
  return (evalIf b' c1' c2' , cT1)
infer ctx (ICaseBool pT pt pf b) = do
  pT' <- checkExtend VBool ctx pT VType
  pt' <- check ctx pt (sub VTrue pT')
  pf' <- check ctx pf (sub VFalse pT')
  b'  <- check ctx b VBool
  return (evalCaseBool pT' pt' pf' b' , sub b' pT')
infer ctx (IDInterp d e) = do
  d' <- check ctx d VDesc
  e' <- check ctx e VType
  return (evalDInterp d' e' , VType)
infer ctx (IProj1 ab) = do
  (ab' , abT) <- infer ctx ab
  case abT of
    VSg aT bT -> return (evalProj1 ab' , aT)
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ prettyPrintError ab ++
      "\nProjected type:\n" ++ prettyPrintError abT
infer ctx (IProj2 ab) = do
  (ab' , abT) <- infer ctx ab
  case abT of
    VSg aT bT -> return (evalProj2 ab' , sub (evalProj1 ab') bT)
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ prettyPrintError ab ++
      "\nProjected type:\n" ++ prettyPrintError abT
infer ctx (IApp f a) = do
  (f' , fT) <- infer ctx f
  case fT of
    VPi aT bT -> do
      a' <- check ctx a aT
      return (evalApp f' a' , sub a' bT)
    _ -> throwError $
      "Ill-typed, application of non-function!\n" ++
      "Applied value:\n"  ++ prettyPrintError f ++
      "\nApplied type:\n"  ++ prettyPrintError fT
infer ctx (IVar l) =
  -- XXX: this error check is dubious: the variable is looked up by
  -- name here, and by numeric index below.  These need not agree in
  -- the face of DeBruijn bugs ...
  case findIndex (\(l' , _) -> l == l') ctx of
    Nothing -> throwError $
      "Variable not in context!\n" ++
      "Referenced variable:\n" ++ l ++
      "\nCurrent context:\n" ++ show (map fst ctx)
    Just i ->
      return (Neut (NVar (NomVar (l , i))) , snd (ctx !! i))
infer ctx (IAnn a aT) = do
  aT' <- check ctx aT VType
  a'  <- check ctx a aT'
  return (a' , aT')

----------------------------------------------------------------------

checkExtend2 :: Type -> Ctx -> Bound Check -> Bound Type -> Result (Bound Val)
checkExtend2 aT ctx b (Bound (_ , bT)) = checkExtend aT ctx b bT

checkExtend :: Type -> Ctx -> Bound Check -> Type -> Result (Bound Val)
checkExtend aT ctx (Bound (l , b)) bT = do
  b' <- check ((l , aT) : ctx) b bT
  return $ Bound (l , b')

inferExtend :: Type -> Ctx -> Bound Infer -> Result (Bound Val , Bound Type)
inferExtend aT ctx (Bound (l , b)) = do
  (b' , bT) <- infer ((l , aT) : ctx) b
  return (Bound (l , b') , Bound (l , bT))

checkDefs :: [Val] -> Ctx -> [Def] -> Result [(Ident , Val , Type)]
checkDefs x ctx [] = return []
checkDefs xs ctx ((l , a , aT) : as) = do
  aT' <- return . foldSub xs =<< check ctx aT VType
  a' <- return . foldSub xs =<< check ctx a aT'
  as' <- checkDefs (a' : xs) ((l , aT') : ctx) as
  return ((l , a' , aT') : as')

checkDefsStable :: [Def] -> Result [Def]
checkDefsStable as = do
  as' <- checkDefs [] [] as
  let bs = embedDefs as'
  bs' <- checkDefs [] [] bs
  unless (as' == bs') $ throwError $
    "Embedding is unstable!"
  return bs
  where
  embedDefs = map (\(l , a , aT) -> (l , embedVC a , embedVC aT))

----------------------------------------------------------------------