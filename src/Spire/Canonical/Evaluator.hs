{-# LANGUAGE MultiParamTypeClasses
           , FlexibleInstances
           , ViewPatterns
           , TupleSections
           #-}

module Spire.Canonical.Evaluator
  (lookupValAndType , lookupType , sub , sub2 , elim , app , app2)
where
import Unbound.LocallyNameless hiding ( Spine )
import Unbound.LocallyNameless.SubstM
import Spire.Canonical.Types
import Spire.Surface.PrettyPrinter
import Control.Applicative ((<$>) , (<*>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

----------------------------------------------------------------------

instance SubstM SpireM Value Spine
instance SubstM SpireM Value Elim
instance SubstM SpireM Value Value where
  substHookM (VNeut nm fs) = Just f
    where
    f nm' e = do
      fs' <- substM nm' e fs
      let head = if nm == nm' then e else vVar nm
      elims head fs'
  substHookM _ = Nothing

----------------------------------------------------------------------

sub :: Bind Nom Value -> Value -> SpireM Value
sub b x = do
  (nm , f) <- unbind b
  substM nm x f

elimB :: Bind Nom Value -> Elim -> SpireM (Bind Nom Value)
elimB bnd_f g = do
  (nm , f) <- unbind bnd_f
  bind nm <$> elim f g

subCompose :: Bind Nom Value -> (Value -> Value) -> SpireM (Bind Nom Value)
subCompose bnd_f g = do
  (nm , f) <- unbind bnd_f
  bind nm <$> substM nm (g (vVar nm)) f

sub2 :: Bind Nom2 Value -> (Value , Value) -> SpireM Value
sub2 b (x1 , x2) = do
  ((nm1 , nm2) , f) <- unbind b
  substsM [(nm1 , x1) , (nm2 , x2)] f

sub3 :: Bind Nom3 Value -> (Value , Value , Value) -> SpireM Value
sub3 b (x1 , x2 , x3) = do
  ((nm1 , nm2 , nm3) , f) <- unbind b
  substsM [(nm1 , x1) , (nm2 , x2) , (nm3 , x3)] f

app :: Value -> Value -> SpireM Value
app f x = elim f (EApp x)

app2 :: Value -> Value -> Value -> SpireM Value
app2 f x y = elims f (Pipe (Pipe Id (EApp x)) (EApp y))

----------------------------------------------------------------------

elim :: Value -> Elim -> SpireM Value
elim (VNeut nm fs) f        = return $ VNeut nm (Pipe fs f)
elim (VLam f)      (EApp a) = f `sub` a
elim _             (EApp _) = throwError "Ill-typed evaluation of function application"

elim VTT    (EElimUnit _P ptt)  = return ptt
elim _      (EElimUnit _P ptt)  = throwError "Ill-typed evaluation of elimUnit"

elim VTrue  (EElimBool _P pt _) = return pt
elim VFalse (EElimBool _P _ pf) = return pf
elim _      (EElimBool _P _  _) = throwError "Ill-typed evaluation of elimBool"

elim (VPair a b) (EElimPair _A _B _P ppair) = do
  ppair `sub2` (a , b)
elim _               (EElimPair _A _B _P ppair)  =
  throwError "Ill-typed evaluation of elimPair"

elim VRefl (EElimEq _A x _P prefl y) =
  return prefl
elim _               (EElimEq _A x _P prefl y)  =
  throwError "Ill-typed evaluation of elimEq"

elim VNil         (EElimEnum _P pn _)  =
  return pn
elim (VCons x xs) (EElimEnum _P pn pc) = do
  ih <- xs `elim` EElimEnum _P pn pc
  pc `sub3` (x , xs , ih)
elim _            (EElimEnum _P _ _)  =
  throwError "Ill-typed evaluation of elimEnum"

elim VEmp            (EElimTel _P pemp pext) =
  return pemp
elim (VExt _A bnd_B) (EElimTel _P pemp pext) = do
  (nm_a , _B) <- unbind bnd_B
  ih <- elim _B (EElimTel _P pemp pext)
  pext `sub3` (_A , VLam (bind nm_a _B) , VLam (bind nm_a ih))
elim _               (EElimTel _P pemp pext)  =
  throwError "Ill-typed evaluation of elimTel"

elim (VEnd i)        (EElimDesc _I _P pend prec parg) =
  pend `sub` i
elim (VRec i _D)     (EElimDesc _I _P pend prec parg) = do
  ih <- _D `elim` EElimDesc _I _P pend prec parg
  prec `sub3` (i , _D , ih)
elim (VArg _A bnd_B) (EElimDesc _I _P pend prec parg) = do
  (nm_a , _B) <- unbind bnd_B
  ih <- elim _B (EElimDesc _I _P pend prec parg)
  parg `sub3` (_A , VLam (bind nm_a _B) , VLam (bind nm_a ih))
elim _            (EElimDesc _I _P pend prec parg)  =
  throwError "Ill-typed evaluation of elimDesc"

elim (VInit xs) (EInd l _P _I _D p _M m i) = do
  let _X = vBind "i" (VFix l _P _I _D p)
  let ih = rBind2 "i" "x" $ \ j x -> rInd l _P _I _D p _M m (vVar j) x
  ihs <- _D `elim` EProve _I _X _M ih i xs
  m `sub3` (i , xs , ihs)
elim _            (EInd l _P _I _D p _M m i)  =
  throwError "Ill-typed evaluation of ind"

elim (VEnd j)        (EFunc _I _X i) =
  return $ VEq _I j _I i
elim (VRec j _D)     (EFunc _I _X i) =
  vProd <$> _X `sub` j <*> _D `elim` EFunc _I _X i
elim (VArg _A _B)    (EFunc _I _X i) =
  VSg _A <$> _B `elimB` EFunc _I _X i
elim _               (EFunc _I _X i) =
  throwError "Ill-typed evaluation of Func"

elim (VEnd j)        (EHyps _I _X _M i q) =
  return $ VUnit
elim (VRec j _D)     (EHyps _I _X _M i xxs) = do
  _A <- _X `sub` j
  _B <- _D `elim` EFunc _I _X i
  (x , xs) <- (,) <$> freshR "x" <*> freshR "xs"
  ppair <- vProd <$> _M `sub2` (j , vVar x) <*> _D `elim` EHyps _I _X _M i (vVar xs)
  xxs `elim` EElimPair _A (kBind _B) (kBind VType) (bind2 x xs ppair)
elim (VArg _A bnd_B)    (EHyps _I _X _M i axs) = do
  (a , _B) <- unbind bnd_B
  _B' <- _B `elim` EFunc _I _X i
  xs <- freshR "xs"
  ppair <- _B `elim` EHyps _I _X _M i (vVar xs)
  axs `elim` EElimPair _A (bind a _B') (kBind VType) (bind2 a xs ppair)
elim _D               (EHyps _I _X _M i xs) =
  throwError $
   "Ill-typed evaluation of Hyps:" ++
   "\nDescription:\n" ++ prettyPrint _D ++
   "\nPair:\n" ++ prettyPrint xs

elim (VEnd j)        (EProve _I _X _M m i q) =
  return $ VTT
elim (VRec j _D)     (EProve _I _X _M m i xxs) = do
  _A <- _X `sub` j
  _B <- _D `elim` EFunc _I _X i
  (nm_xxs , x , xs) <- (,,) <$> freshR "xxs" <*> freshR "x" <*> freshR "xs"
  _M' <- VRec j _D `elim` EHyps _I _X _M i (vVar nm_xxs)
  ppair <- VPair <$> m `sub2` (j , vVar x) <*> _D `elim` EProve _I _X _M m i (vVar xs)
  xxs `elim` EElimPair _A (kBind _B) (bind nm_xxs _M') (bind2 x xs ppair)
elim (VArg _A _B)    (EProve _I _X _M m i axs) = do
  (nm_axs , a , xs) <- (,,) <$> freshR "axs" <*> freshR "a" <*> freshR "xs"
  _Ba <- _B `sub` vVar a
  _B' <- _Ba `elim` (EFunc _I _X i)
  _M' <- VArg _A _B `elim` EHyps _I _X _M i (vVar nm_axs)
  ppair <- _Ba `elim` EProve _I _X _M m i (vVar xs)
  axs `elim` EElimPair _A (bind a _B') (bind nm_axs _M') (bind2 a xs ppair)
elim _               (EProve _I _X _M m i xs) =
  throwError "Ill-typed evaluation of prove"

elim VNil         (EBranches _P) =
  return VUnit
elim (VCons l _E)    (EBranches _P) = do
  _P' <- _P `subCompose` VThere
  vProd <$> _P `sub` VHere  <*> _E `elim` EBranches _P'
elim _             (EBranches _P) =
  throwError "Ill-typed evaluation of Branches"

elim VHere         (ECase (VCons l _E) _P ccs) = do
  _Pthere <- _P `subCompose` VThere
  _A <- _P `sub` VHere
  _B <- _E `elim` EBranches _Pthere
  let _M = _A
  c <- freshR "c"
  let ppair = vVar c
  ccs `elim` EElimPair _A (kBind _B) (kBind _M) (bind2 c wildcardR ppair)
elim (VThere t)    (ECase (VCons l _E) _P ccs) = do
  _Pthere <- _P `subCompose` VThere
  _A <- _P `sub` VHere
  _B <- _E `elim` EBranches _Pthere
  _M <- _P `sub` (VThere t)
  cs <- freshR "cs"
  ppair <- t `elim` ECase _E _Pthere (vVar cs)
  ccs `elim` EElimPair _A (kBind _B) (kBind _M) (bind2 wildcardR cs ppair)
elim _             (ECase _E _P ccs) =
  throwError "Ill-typed evaluation of case"

elims :: Value -> Spine -> SpireM Value
elims x Id = return x
elims x (Pipe fs f) = do
  x' <- elims x fs
  elim x' f

----------------------------------------------------------------------
-- Exported lookup functions.

lookupValAndType :: Nom -> SpireM (Value , Type)
lookupValAndType nm = do
  ctx <- asks ctx
  lookupCtx nm ctx

lookupType :: Nom -> SpireM Type
lookupType nm = snd <$> lookupValAndType nm

----------------------------------------------------------------------
-- Non-exported lookup functions.

lookupCtx :: Nom -> Tel -> SpireM (Value , Type)
lookupCtx nm (Extend (unrebind -> ((x , Embed _A) , xs))) =
  if nm == x
  then return (vVar nm , _A)
  else lookupCtx nm xs
lookupCtx nm Empty = do
  env <- asks env
  lookupEnv nm env

lookupEnv :: Nom -> Env -> SpireM (Value , Type)
lookupEnv nm (VDef x a _A : xs) =
  if nm == x
  then return (a , _A)
  else lookupEnv nm xs
lookupEnv nm [] = do
  env <- asks env
  ctx <- asks ctx
  uCtx <- gets unifierCtx
  throwError $
    "Variable not in context or environment!\n" ++
    "Referenced variable:\n" ++ prettyPrintError nm ++ "\n" ++
    "\nCurrent context:\n" ++ prettyPrintError ctx ++ "\n"
    -- "\nCurrent environment:\n" ++ prettyPrintError env ++ "\n" ++

----------------------------------------------------------------------
