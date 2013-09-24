{-# LANGUAGE ViewPatterns
           , TupleSections
 #-}
module Spire.Canonical.Unification where
import Control.Applicative ((<*>) , (<$>))
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Common.BwdFwd
import PatternUnify.Tm
import PatternUnify.Context
-- import PatternUnify.Tm hiding (Elim)
-- import qualified PatternUnify.Tm as T
import Spire.Canonical.Types
import Unbound.LocallyNameless hiding ( Spine )

----------------------------------------------------------------------

value2Tm :: Value -> SpireM Tm
value2Tm v = case v of
  VBool -> return $ C Bool
  VType -> return $ C Type
  VPi _A _B -> Pi <$> value2Tm _A <*> mapBindM value2Tm _B
  VSg _A _B -> Sig <$> value2Tm _A <*> mapBindM value2Tm _B
  VTrue -> return $ C Tt
  VFalse -> return $ C Ff
  VPair x y -> C <$> (Pair <$> value2Tm x <*> value2Tm y)
  VLam b -> L <$> mapBindM value2Tm b
  VNeut x s -> N (nom2Head x) <$> spine2BwdElim s
  -- XXX: no support for unit type right now!
  _ -> throwError $ "Unsupported input in value2Tm: " ++ show v
  where
    nom2Head x = if isMV x
                 then M (translate x)
                 else V (translate x) Only

    elim2Elim e = case e of
      EApp v -> A <$> value2Tm v
      EProj1 -> return Hd
      EProj2 -> return Tl
      ECaseBool b x y -> If <$> mapBindM value2Tm b <*> value2Tm x <*> value2Tm y

    spine2BwdElim Id = return B0
    spine2BwdElim (Pipe s e) = (:<) <$> spine2BwdElim s <*> elim2Elim e

tm2Value :: Tm -> SpireM Value
tm2Value t = case t of
  L b -> VLam <$> mapBindM tm2Value b
  C Type -> return VType
  C (Pair x y) -> VPair <$> tm2Value x <*> tm2Value y
  C Bool -> return VBool
  C Tt -> return VTrue
  C Ff -> return VFalse
  Pi t b -> VPi <$> tm2Value t <*> mapBindM tm2Value b
  Sig t b -> VSg <$> tm2Value t <*> mapBindM tm2Value b
  N h es -> VNeut <$> head2Nom h <*> bwdElim2Spine es
  -- XXX: not sure which of 'Set' and 'Type' we want to translate.
  _ -> throwError $ "Unsupported input in tm2Value: " ++ show t
  where
    head2Nom (V n Only) = return $ translate n
    head2Nom h@(V _ _) = throwError $ "Attempt to translate twin: " ++ show h
    head2Nom (M n) = return $ translate n

    elim2Elim e = case e of
      A t -> EApp <$> tm2Value t
      Hd -> return EProj1
      Tl -> return EProj2
      If b x y -> ECaseBool <$> mapBindM tm2Value b <*> tm2Value x <*> tm2Value y
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

-- Push a new mvar decl into the unifier state.
declareMV :: Spire.Canonical.Types.Nom -> Spire.Canonical.Types.Type -> SpireM ()
declareMV nm _T = do
  _T' <- value2Tm _T
  pushEntry $ E (translate nm) (_T', HOLE)

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
pushEntry e = modify (\r -> r { unifierCtx = e : unifierCtx r })
