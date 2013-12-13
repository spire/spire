module Spire.Canonical.Embedder where
import Control.Applicative
import Data.Monoid (mempty)
import Unbound.LocallyNameless hiding ( Spine )
import Spire.Canonical.Types
import Spire.Expression.Types

----------------------------------------------------------------------

embedV :: Value -> FreshM Check

embedV VTT           = return $ Infer ITT
embedV VTrue         = return $ Infer ITrue
embedV VFalse        = return $ Infer IFalse
embedV VUnit         = return $ Infer IUnit
embedV VBool         = return $ Infer IBool
embedV VType         = return $ Infer IType

embedV (VSg _A _B)   = Infer <$> (ISg <$> embedV _A <*> embedVB _B)
embedV (VPi _A _B)   = Infer <$> (IPi <$> embedV _A <*> embedVB _B)
embedV (VPair a b)   = CPair <$> embedV a <*> embedV b
embedV (VLam b)      = CLam <$> embedVB b

embedV (VNeut nm fs) = Infer <$> embedN nm fs

----------------------------------------------------------------------

embedN :: Nom -> Spine -> FreshM Infer

embedN nm Id                 = return  $  IVar nm
embedN nm (Pipe fs (EApp a)) = IApp   <$> embedN nm fs <*> embedV a
embedN nm (Pipe fs EProj1)   = IProj1 <$> embedN nm fs
embedN nm (Pipe fs EProj2)   = IProj2 <$> embedN nm fs

embedN nm (Pipe fs (ECaseBool _P pt pf)) =
  ICaseBool <$> embedVB _P <*>
    embedV pt <*> embedV pf <*> (Infer <$> embedN nm fs)

----------------------------------------------------------------------

embedVB :: Bind Nom Value -> FreshM (Bind Nom Check)
embedVB bnd_a = do
  (nm , a) <- unbind bnd_a
  a'       <- embedV a
  return   $ bind nm a'

embedVDef :: VDef -> FreshM CDef
embedVDef (VDef nm a _A) = CDef nm <$> embedV a  <*> pure mempty
                                   <*> embedV _A <*> pure mempty

----------------------------------------------------------------------