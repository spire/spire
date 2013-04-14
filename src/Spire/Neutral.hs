module Spire.Neutral where
import Control.Monad.Error

----------------------------------------------------------------------

newtype Bound a = Bound a
  deriving ( Eq, Show, Read )

type Var = Int
type Type = Val
type VDef = (Val , Type)
type Result a = Either String a
type VCtx = [Type]

data Val =
    VUnit | VBool | VProg | VType
  | VPi Type (Bound Type)
  | VSg Type (Bound Type)

  | VTT | VTrue | VFalse
  | VPair Val Val
  | VLam Type (Bound Val)      -- Abstracted over Neut (NVar 0)
  | VDefs [VDef]
  | Neut Neut
  deriving ( Eq, Show, Read )

data Neut =
    NVar Var
  | NIf Neut Val Val
  | NCaseBool (Bound Type) Val Val Neut
  | NProj1 Neut
  | NProj2 Neut
  | NApp Neut Val
  deriving ( Eq, Show, Read )

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

{-
Do not explicitly inspect `Bound' variables in `subV' and `subN'.
Instead, use helper functions like `subExtend', which correctly
increment the De Bruijn index.
-}

subV :: Var -> Val -> Val -> Val
subV i x (VPi aT bT) = VPi (subV i x aT) (subExtend i x bT)
subV i x (VSg aT bT) = VSg (subV i x aT) (subExtend i x bT)
subV i x (VPair a b) = VPair (subV i x a) (subV i x b)
subV i x (VLam aT f) = VLam (subV i x aT) (subExtend i x f)
subV i x (VDefs as) = VDefs (subVs i x as)
subV i x (Neut n) = subN i x n
subV _ _ a = a

subN :: Var -> Val -> Neut -> Val
subN i x (NVar j) | i == j = x
subN i x (NVar j) | i < j = Neut (NVar (j - succ i))
subN i x (NVar j) = Neut (NVar j)
subN i x (NIf b c1 c2) =
  evalIf (subN i x b) (subV i x c1) (subV i x c2)
subN i x (NCaseBool pT pt pf b) =
  evalCaseBool (subExtend i x pT) (subV i x pt) (subV i x pf) (subN i x b)
subN i x (NProj1 ab) = evalProj1 (subN i x ab)
subN i x (NProj2 ab) = evalProj2 (subN i x ab)
subN i x (NApp f a) =
  evalApp (subN i x f) (subV i x a)

----------------------------------------------------------------------

sub :: Val -> Val -> Val
sub = subV 0

suB :: Val -> Bound Val -> Val
suB x (Bound a) = sub x a

subExtend :: Var -> Val -> Bound Val -> Bound Val
subExtend i x (Bound a) = Bound $ subV (succ i) x a

----------------------------------------------------------------------

subs :: Val -> [VDef] -> [VDef]
subs = subVs 0

subVs :: Var -> Val -> [VDef] -> [VDef]
subVs i x [] = []
subVs i x ((a , aT) : as) = (subV i x a , subV i x aT) : subVs (succ i) x as

----------------------------------------------------------------------

evalIf :: Val -> Val -> Val -> Val
evalIf VTrue c1 c2 = c1
evalIf VFalse c1 c2 = c2
evalIf (Neut b) c1 c2 = Neut $ NIf b c1 c2
evalIf _ _ _ = error "Ill-typed evaluation of If"

evalCaseBool :: Bound Type -> Val -> Val -> Val -> Val
evalCaseBool pT pt pf VTrue = pt
evalCaseBool pT pt pf VFalse = pf
evalCaseBool pT pt pf (Neut b) = Neut $ NCaseBool pT pt pf b
evalCaseBool _ _ _ _ = error "Ill-typed evaluation of CaseBool"

evalProj1 :: Val -> Val
evalProj1 (VPair a b) = a
evalProj1 (Neut ab) = Neut $ NProj1 ab
evalProj1 _ = error "Ill-typed evaluation of Proj1"

evalProj2 :: Val -> Val
evalProj2 (VPair a b) = b
evalProj2 (Neut ab) = Neut $ NProj1 ab
evalProj2 _ = error "Ill-typed evaluation of Proj2"

evalApp :: Val -> Val -> Val
evalApp (VLam aT f) a = suB a f
evalApp (Neut f) a = Neut $ NApp f a
evalApp f a = error $
  "Ill-typed evaluation of App\n" ++
  "Function:\n" ++ show f ++ "\n" ++
  "Argument:\n" ++ show a

foldSub :: [Val] -> Val -> Val
foldSub xs a = helper (reverse xs) a
  where
  helper :: [Val] -> Val -> Val
  helper [] a = a
  helper (x : xs) a = helper xs (subV (length xs) x a)

----------------------------------------------------------------------