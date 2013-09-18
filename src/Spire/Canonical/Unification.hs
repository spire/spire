module Spire.Canonical.Unification where
import Control.Applicative ((<*>) , (<$>))
import Control.Monad.Error
import Common.BwdFwd
import PatternUnify.Tm
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
tm2Value = undefined

-- XXX: this could replace most uses of unbind in our code, if the
-- function 'f' also had access to the translated name.
--
-- See e.g. checkExtend, checkExtend2, elabBC, and embedVB
mapBindM :: (Fresh m , Functor m , Alpha b , Alpha b' , Rep a' , Rep a)
         => (b -> m b') -> Bind (Name a) b -> m (Bind (Name a') b')
mapBindM f b = do
  (x , e) <- unbind b
  bind (translate x) <$> f e
