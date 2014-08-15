{-# LANGUAGE MultiParamTypeClasses
           , FlexibleInstances
           , ViewPatterns
           , TupleSections
           #-}

module Spire.Canonical.Evaluator
  (lookupValAndType , lookupType , sub , sub2 , elim , app , app2)
where
import PatternUnify.Context
import Unbound.LocallyNameless hiding ( Spine )
import Unbound.LocallyNameless.SubstM
import Spire.Canonical.Types
import Spire.Canonical.Unification
import Spire.Surface.PrettyPrinter
import Control.Applicative ((<$>) , (<*>))
import Control.Monad.Error
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
elim (VPair a _)   EProj1   = return a
elim _             EProj1   = throwError "Ill-typed evaluation of proj1"
elim (VPair _ b)   EProj2   = return b
elim _             EProj2   = throwError "Ill-typed evaluation of proj2"

elim VTrue  (EElimBool _P pt _) = return pt
elim VFalse (EElimBool _P _ pf) = return pf
elim _      (EElimBool _P _  _) = throwError "Ill-typed evaluation of elimBool"

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

elim VRefl         (ESubst _P px) =
  return px
elim _             (ESubst _P px) =
  throwError "Ill-typed evaluation of subst"

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
elim (VRec j _D)     (EHyps _I _X _M i (VCons x xs)) =
  vProd <$> _M `sub2` (j , x) <*> _D `elim` EHyps _I _X _M i xs
elim (VArg _A _B)    (EHyps _I _X _M i (VCons a xs)) = do
  _Ba <- _B `sub` a
  _Ba `elim` EHyps _I _X _M i xs
elim _               (EHyps _I _X _M i xs) =
  throwError "Ill-typed evaluation of Hyps"

elim (VEnd j)        (EProve _I _X _M m i q) =
  return $ VTT
elim (VRec j _D)     (EProve _I _X _M m i (VCons x xs)) =
  vProd <$> m `sub2` (j , x) <*> _D `elim` EProve _I _X _M m i xs
elim (VArg _A _B)    (EProve _I _X _M m i (VCons a xs)) = do
  _Ba <- _B `sub` a
  _Ba `elim` EProve _I _X _M m i xs
elim _               (EProve _I _X _M m i xs) =
  throwError "Ill-typed evaluation of prove"

elim VNil         (EBranches _P) =
  return VUnit
elim (VCons l _E)    (EBranches _P) = do
  _P' <- _P `subCompose` VThere
  vProd <$> _P `sub` VHere  <*> _E `elim` EBranches _P'
elim _             (EBranches _P) =
  throwError "Ill-typed evaluation of Branches"

elim VHere         (ECase (VCons l _E) _P (VPair c cs)) =
  return c
elim (VThere t)    (ECase (VCons l _E) _P (VPair c cs)) = do
  _P' <- _P `subCompose` VThere
  t `elim` ECase _E _P' cs
elim _             (ECase _E _P cs) =
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
  uCtx <- gets unifierCtx
  lookupMV nm uCtx

lookupMV :: Nom -> UnifierCtx -> SpireM (Value , Type)
lookupMV nm (E x (_T , _) : es) =
  if nm == (translate x)
  then (vVar nm , ) <$> tm2Value _T
  else lookupMV nm es
lookupMV nm (Q _ _ : es) = lookupMV nm es
lookupMV nm [] = do
  env <- asks env
  ctx <- asks ctx
  uCtx <- gets unifierCtx
  throwError $
    "Variable not in context, environment, or unifier context!\n" ++
    "Referenced variable:\n" ++ prettyPrintError nm ++ "\n" ++
    "\nCurrent context:\n" ++ prettyPrintError ctx ++ "\n" ++
    "\nCurrent environment:\n" ++ prettyPrintError env ++ "\n" ++
    "\nCurrent unifier context:\n" ++ prettyPrintError uCtx

----------------------------------------------------------------------
