module Spire.Expression.CheckingAndEvaluation (checkDefsStable) where
import Spire.Canonical.Types
import Spire.Canonical.Embedding
import Spire.Canonical.HereditarySubstitution
import Spire.Expression.Types
import Spire.Surface.PrettyPrinting
import Control.Monad.Error
import Control.Monad.Reader
import Data.List

----------------------------------------------------------------------

data CheckR = CheckR { ctx :: Ctx }
type CheckM = ReaderT CheckR Result

extendCtx :: Ident -> Type -> CheckM a -> CheckM a
extendCtx l tp = local (\r -> r { ctx = (l , tp) : ctx r })

run :: CheckM a -> CheckR -> Result a
run = runReaderT

----------------------------------------------------------------------

check :: Check -> Type -> CheckM Val
check (CLam b) (VPi aT bT) = do
  b' <- checkExtend2 aT b bT
  return $ VLam aT b'
check (CPair a b) (VSg aT bT) = do
  a' <- check a aT
  b' <- check b (sub a' bT)
  return $ VPair aT bT a' b'
check (CIn a) (VFix d) = do
  a' <- check a (evalDInterp d (VFix d))
  return $ VIn d a'
check (Infer a) bT = do
  ctx <- asks ctx
  (a' , aT) <- infer a
  unless (aT == bT) $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ prettyPrintError bT ++
    "\n\nInferred type:\n" ++ prettyPrintError aT ++
    "\n\nContext:\n" ++ prettyPrintError ctx ++
    "\n\nUnevaluated value:\n" ++ prettyPrintError a
  return $ a'
check a aT = throwError "Ill-typed!"

infer :: Infer -> CheckM (Val , Type)
infer ITT     = return (VTT , VUnit)
infer ITrue   = return (VTrue , VBool)
infer IFalse  = return (VFalse , VBool)
infer IUnit   = return (VUnit , VType)
infer IBool   = return (VBool , VType)
infer IString = return (VString , VType)
infer IDesc   = return (VDesc , VType)
infer IProg   = return (VProg , VType)
infer IType   = return (VType , VType)

infer IDUnit  = return (VDUnit , VDesc)
infer IDRec   = return (VDRec , VDesc)
infer (IDSum d e) = do
  d' <- check d VDesc
  e' <- check e VDesc
  return (VDSum d' e' , VDesc)
infer (IDPi aT fD) = do
  aT' <- check aT VType
  fD' <- checkExtend aT' fD VDesc
  return (VDPi aT' fD' , VDesc)
infer (IDSg aT fD) = do
  aT' <- check aT VType
  fD' <- checkExtend aT' fD VDesc
  return (VDSg aT' fD' , VDesc)

infer (IQuotes str) =
  return (VQuotes str , VString)
infer (ILamAnn aT b) = do
  aT'       <- check aT VType
  (b' , bT) <- inferExtend aT' b
  return (VLam aT' b' , VPi aT' bT)
infer (IPi aT bT) = do
  aT' <- check aT VType
  bT' <- checkExtend aT' bT VType
  return (VPi aT' bT' , VType)
infer (ISg aT bT) = do
  aT' <- check aT VType
  bT' <- checkExtend aT' bT VType
  return (VSg aT' bT' , VType)
infer (IFix d) = do
  d' <- check d VDesc
  return (VFix d' , VType)
infer (IDefs as) = do
  as' <- checkDefs [] as
  let as'' = map (\(_ , a , aT) -> (a , aT))  as'
  return (VDefs as'' , VProg)
infer (IStrAppend s1 s2) = do
 s1' <- check s1 VString
 s2' <- check s2 VString
 return (evalStrAppend s1' s2' , VString)
infer (IStrEq s1 s2) = do
 s1' <- check s1 VString
 s2' <- check s2 VString
 return (evalStrEq s1' s2' , VBool)
infer (IIf b c1 c2) = do
  b'          <- check b VBool
  (c1' , cT1) <- infer c1
  (c2' , cT2) <- infer c2
  unless (cT1 == cT2) $ throwError $
    "Ill-typed, conditional branches have different types!\n" ++
    "First branch:\n" ++ prettyPrintError cT1 ++
    "\nSecond branch:\n" ++ prettyPrintError cT2
  return (evalIf b' c1' c2' , cT1)
infer (ICaseBool pT pt pf b) = do
  pT' <- checkExtend VBool pT VType
  pt' <- check pt (sub VTrue pT')
  pf' <- check pf (sub VFalse pT')
  b'  <- check b VBool
  return (evalCaseBool pT' pt' pf' b' , sub b' pT')
infer (IDInterp d e) = do
  d' <- check d VDesc
  e' <- check e VType
  return (evalDInterp d' e' , VType)
infer (IProj1 ab) = do
  (ab' , abT) <- infer ab
  case abT of
    VSg aT bT -> return (evalProj1 ab' , aT)
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ prettyPrintError ab ++
      "\nProjected type:\n" ++ prettyPrintError abT
infer (IProj2 ab) = do
  (ab' , abT) <- infer ab
  case abT of
    VSg aT bT -> return (evalProj2 ab' , sub (evalProj1 ab') bT)
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ prettyPrintError ab ++
      "\nProjected type:\n" ++ prettyPrintError abT
infer (IApp f a) = do
  (f' , fT) <- infer f
  case fT of
    VPi aT bT -> do
      a' <- check a aT
      return (evalApp f' a' , sub a' bT)
    _ -> throwError $
      "Ill-typed, application of non-function!\n" ++
      "Applied value:\n"  ++ prettyPrintError f ++
      "\nApplied type:\n"  ++ prettyPrintError fT
infer (IVar l) = do
  ctx <- asks ctx
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
infer (IAnn a aT) = do
  aT' <- check aT VType
  a'  <- check a aT'
  return (a' , aT')

----------------------------------------------------------------------

checkExtend2 :: Type -> Bound Check -> Bound Type -> CheckM (Bound Val)
checkExtend2 aT b (Bound (_ , bT)) = checkExtend aT b bT

checkExtend :: Type -> Bound Check -> Type -> CheckM (Bound Val)
checkExtend aT (Bound (l , b)) bT = do
  b' <- extendCtx l aT $ check b bT
  return $ Bound (l , b')

inferExtend :: Type -> Bound Infer -> CheckM (Bound Val , Bound Type)
inferExtend aT (Bound (l , b)) = do
  (b' , bT) <- extendCtx l aT $ infer b
  return (Bound (l , b') , Bound (l , bT))

checkDefs :: [Val] -> [Def] -> CheckM [(Ident , Val , Type)]
checkDefs x [] = return []
checkDefs xs ((l , a , aT) : as) = do
  aT' <- return . foldSub xs =<< check aT VType
  a' <- return . foldSub xs =<< check a aT'
  as' <- extendCtx l aT' $ checkDefs (a' : xs) as
  return ((l , a' , aT') : as')

checkDefsStable :: [Def] -> Result [Def]
checkDefsStable as = run (checkDefsStableM as) (CheckR { ctx = [] })
  where
  checkDefsStableM as = do
    as' <- checkDefs [] as
    let bs = embedDefs as'
    bs' <- checkDefs [] bs
    unless (as' == bs') $ throwError $
      "Embedding is unstable!"
    return bs
  embedDefs = map (\(l , a , aT) -> (l , embedVC a , embedVC aT))

----------------------------------------------------------------------