{-# LANGUAGE ViewPatterns
           , TupleSections
           , NoMonomorphismRestriction
 #-}
module Spire.Canonical.Unification where
import Control.Applicative ((<*>) , (<$>))
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Unbound.LocallyNameless hiding ( Spine )

import Common.BwdFwd
import PatternUnify.Tm
import PatternUnify.Context
import qualified PatternUnify.Test
import Spire.Canonical.Types
import Spire.Options hiding (debug)

import Spire.Surface.PrettyPrinter
import Spire.Debug

----------------------------------------------------------------------

unify :: Spire.Canonical.Types.Type -> Value -> Value -> SpireM Bool
unify _T v1 v2 = do
  let p = prettyPrintError
  solveMetaVars <- asks (metavars . conf)
    `debug` "unify " ++ p _T ++ " " ++ p v1 ++ " " ++ p v2
  if solveMetaVars
  then unify' _T v1 v2
  else return $ v1 == v2

unify' _T v1 v2 = do
  declareProblem _T v1 v2
  uCtx <- gets unifierCtx
  case PatternUnify.Test.unify uCtx `debug` "unify': before: " ++ prettyPrintError uCtx of
    -- XXX: should report this error. What we really need is a stack
    -- of errors?
    Left _err -> throwError ("unify': " ++ _err) -- return False
    Right uCtx' -> do modify (\r -> r { unifierCtx = uCtx' })
                        `debug` ("unify': after: " ++ prettyPrintError uCtx')
                      return True

----------------------------------------------------------------------

value2Tm :: Value -> SpireM Tm
value2Tm v = case v of
  VBool -> return $ C Bool
  VType -> return $ C Type
  VPi _A _B -> Pi <$> value2Tm _A <*> mapBindM value2Tm _B
  VSg _A _B -> Sig <$> value2Tm _A <*> mapBindM value2Tm _B
  VTrue -> return $ C True'
  VFalse -> return $ C False'
  VPair x y -> C <$> (Pair <$> value2Tm x <*> value2Tm y)
  VLam b -> L <$> mapBindM value2Tm b
  VNeut x s -> N (nom2Head x) <$> spine2BwdElim s
  VUnit -> return $ C Unit
  VTT   -> return $ C Tt

  VEq  _ _ _ _ -> unsupported
  VFix _ _ _   -> unsupported
  VString      -> unsupported
  VQuotes _    -> unsupported
  VEnum        -> unsupported
  VDesc _      -> unsupported
  VTag _       -> unsupported
  VNil         -> unsupported
  VRefl        -> unsupported
  VHere        -> unsupported
  VThere _     -> unsupported
  VEnd   _     -> unsupported
  VCons _ _    -> unsupported
  VRec  _ _    -> unsupported
  VInit _      -> unsupported
  VArg  _ _    -> unsupported
  where
    nom2Head x = if isMV x
                 then M (translate x)
                 else V (translate x) Only

    elim2Elim e = case e of
      EApp v -> A <$> value2Tm v
      EProj1 -> return Hd
      EProj2 -> return Tl
      EElimBool b x y -> If <$> mapBindM value2Tm b <*> value2Tm x <*> value2Tm y

      EFunc _ _ _       -> unsupported
      EElimEnum _ _ _   -> unsupported
      ESubst _ _        -> unsupported
      EBranches _       -> unsupported
      ECase _  _ _      -> unsupported

    spine2BwdElim Id = return B0
    spine2BwdElim (Pipe s e) = (:<) <$> spine2BwdElim s <*> elim2Elim e

    unsupported = throwError $ "Unsupported input in value2Tm: " ++ show v

tm2Value :: Tm -> SpireM Value
tm2Value t = case t of
  L b -> VLam <$> mapBindM tm2Value b
  C Type -> return VType
  C (Pair x y) -> VPair <$> tm2Value x <*> tm2Value y
  C Bool -> return VBool
  C True' -> return VTrue
  C False' -> return VFalse
  C Unit -> return VUnit
  C Tt -> return VTT
  Pi t b -> VPi <$> tm2Value t <*> mapBindM tm2Value b
  Sig t b -> VSg <$> tm2Value t <*> mapBindM tm2Value b
  N h es -> VNeut <$> head2Nom h <*> bwdElim2Spine es
  _ -> throwError $ "Unsupported input in tm2Value: " ++ show t
  where
    head2Nom (V n Only) = return $ translate n
    head2Nom h@(V _ _) = throwError $ "Attempt to translate twin: " ++ show h
    head2Nom (M n) = return $ translate n

    elim2Elim e = case e of
      A t -> EApp <$> tm2Value t
      Hd -> return EProj1
      Tl -> return EProj2
      If b x y -> EElimBool <$> mapBindM tm2Value b <*> tm2Value x <*> tm2Value y
      _ -> throwError $ "Unsupported input in elim2Elim: " ++ show e

    bwdElim2Spine B0 = return Id
    bwdElim2Spine (be :< e) = Pipe <$> bwdElim2Spine be <*> elim2Elim e

-- XXX: this could replace most uses of unbind in our code, if the
-- function 'f' also had access to the translated name.
--
-- See e.g. checkExtend, checkExtend2, elabBC, and embedVB
mapBindM :: (Fresh m , Functor m , Alpha b , Alpha b' , Rep a' , Rep a)
         => (b -> m b') -> Bind (Name a) b -> m (Bind (Name a') b')
mapBindM f b = do
  (x , e) <- unbind b
  bind (translate x) <$> f e

----------------------------------------------------------------------
-- XXX: names here and below are confusing.

-- Generate and declare a fresh mvar and its type, and return the
-- mvar.
declareFreshMV :: String -> SpireM Spire.Canonical.Types.Nom
declareFreshMV name = do
  mv <- freshMV name
  declareMV mv
  return mv

----------------------------------------------------------------------

-- Declare an mvar.  A fresh mvar type for the mvar is created, and
-- pushed into the environment along with the mvar.
declareMV :: Spire.Canonical.Types.Nom -> SpireM ()
declareMV mv = do
  mvT <- freshMV $ mv2String mv ++ "_T"
  -- The order here matters. Earlier things are bound for later things
  -- / the context is read from left to right.  Gundry's code checks
  -- the order later, e.g. if I reverse the order here I get:
  --
  --   spire: validate: dependency error: ?1 occurs before its declaration
  --   when validating
  --   (? : ??1, ?1 : Set := Set ,)
  --
  -- from examples/metavars/ImplicitAnnotation.spire.
  pushMV mvT VType
  pushMV mv  (vVar mvT)

declareMVOfType :: Spire.Canonical.Types.Type -> Spire.Canonical.Types.Nom -> SpireM ()
declareMVOfType _T mv = pushMV mv _T

-- Push a new mvar decl into the unifier state.
pushMV :: Spire.Canonical.Types.Nom -> Spire.Canonical.Types.Type -> SpireM ()
pushMV nm _T = do
  _T' <- value2Tm _T
  (pushEntry $ E (translate nm) (_T', HOLE))
    `debug` "pushMV: " ++ p nm ++ " : " ++ p _T
  where
    p = prettyPrintError

declareProblem :: Spire.Canonical.Types.Type -> Value -> Value -> SpireM ()
declareProblem _T v1 v2 = do
  [ _T' , v1' , v2' ] <- mapM value2Tm [ _T , v1 , v2 ]
  ctx <- tel2List <$> asks ctx
  params <- forM ctx $ \(x , _S) ->
            (translate x , ) . P <$> value2Tm _S
  let eq = Unify (EQN _T' v1' _T' v2')
      prob = foldr (\(x , _S) p -> All _S (bind x p))
                   eq
                   params
  pushEntry (Q Active prob)

pushEntry :: Entry -> SpireM ()
-- The order here matters!
pushEntry e = modify (\r -> r { unifierCtx = unifierCtx r ++ [e] })
