module Spire.Canonical.Checking where
import Spire.Canonical.Types
import Spire.Canonical.HereditarySubstitution
import Control.Monad.Error

----------------------------------------------------------------------

{-
Do not explicitly inspect `Bound' variables in `inferV' and `inferN'.
Instead, use helper functions like `inferExtend', which correctly
extend the context.
-}

checkV :: VCtx -> Val -> Type -> Result ()
checkV ctx a bT = do
  aT <- inferV ctx a
  unless (aT == bT) $ throwError $
    "Ill-typed!\n" ++
    "Expected type:\n" ++ show bT ++
    "\n\nInferred type:\n" ++ show aT ++
    "\n\nContext:\n" ++ show ctx ++
    "\n\nValue:\n" ++ show a

checkN :: VCtx -> Neut -> Type -> Result ()
checkN ctx a bT = checkV ctx (Neut a) bT

inferV :: VCtx -> Val -> Result Type
inferV ctx VTT = return VUnit
inferV ctx VTrue = return VBool
inferV ctx VFalse = return VBool
inferV ctx VUnit = return VType
inferV ctx VBool = return VType
inferV ctx VProg = return VType
inferV ctx VType = return VType
inferV ctx (VPi aT bT) = do
  checkV ctx aT VType
  checkVExtend aT ctx bT VType
  return VType
inferV ctx (VSg aT bT) = do
  checkV ctx aT VType
  checkVExtend aT ctx bT VType
  return VType
inferV ctx (VPair a b) = do
  aT <- inferV ctx a
  bT <- inferVExtend aT ctx b
  return $ VSg aT bT
inferV ctx (VLam aT b) = do
  bT <- inferVExtend2 aT ctx b
  return $ VPi aT bT
inferV ctx (VDefs as) =
  error "TODO infer canonical definitions"
inferV ctx (Neut a) = inferN ctx a

inferN :: VCtx -> Neut -> Result Type
inferN ctx (NProj1 ab) = do
  abT <- inferN ctx ab
  case abT of
    VSg aT bT -> return aT
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ show ab ++
      "\nProjected type:\n" ++ show abT  
inferN ctx (NProj2 ab) = do
  abT <- inferN ctx ab
  case abT of
                       -- TODO could be syntactic subst
    VSg aT bT -> return $ suB (Neut (NProj1 ab)) bT
    _ -> throwError $
      "Ill-typed, projection of non-pair!\n" ++
      "Projected value:\n" ++ show ab ++
      "\nProjected type:\n" ++ show abT
inferN ctx (NCaseBool pT pt pf b) = do
  checkVExtend VBool ctx pT VType
  checkV ctx pt (suB VTrue pT)
  checkV ctx pt (suB VFalse pT)
  checkN ctx b VBool
        -- TODO could be syntactic subst
  return $ suB (Neut b) pT
inferN ctx (NIf b c1 c2) = do
  checkN ctx b VBool
  cT1 <- inferV ctx c1
  cT2 <- inferV ctx c2
  unless (cT1 == cT2) $ throwError $
    "Ill-typed, conditional branches have different types!\n" ++
    "First branch:\n" ++ show cT1 ++
    "\nSecond branch:\n" ++ show cT2
  return cT1
inferN ctx (NApp f a) = do
  fT <- inferN ctx f
  case fT of
    VPi aT bT -> do
      checkV ctx a aT
      return $ suB a bT
    _ -> throwError $
      "Ill-typed, application of non-function!\n" ++
      "Applied value:\n"  ++ show f ++
      "\nApplied type:\n"  ++ show fT
inferN ctx (NVar i) =
  if i >= length ctx
  then throwError $
    "Variable not in context!\n" ++
    "Referenced variable:\n" ++ show i ++
    "\nCurrent context:\n" ++ show ctx
  else return (ctx !! i)

----------------------------------------------------------------------

checkVExtend :: Type -> VCtx -> Bound Val -> Type -> Result ()
checkVExtend aT ctx (Bound b) bT = checkV (aT : ctx) b bT

inferVExtend2 :: Type -> VCtx -> Bound Val -> Result (Bound Val)
inferVExtend2 aT ctx (Bound b) = inferVExtend aT ctx b

inferVExtend :: Type -> VCtx -> Val -> Result (Bound Val)
inferVExtend aT ctx b = do
  bT <- inferV (aT : ctx) b
  return $ Bound bT

----------------------------------------------------------------------
