{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  #-}

module Spire.Canonical.Checker where
import Control.Monad.Error
import Control.Monad.Reader
import Unbound.LocallyNameless hiding ( Spine )
import Spire.Canonical.Types
import Spire.Canonical.Evaluator

----------------------------------------------------------------------

recheckProg :: VProg -> SpireM ()
recheckProg [] = return ()
recheckProg (VDef _ a _A : xs) = do
  checkV _A VType
  checkV a _A
  recheckProg xs
  return ()

----------------------------------------------------------------------

checkV :: Value -> Type -> SpireM ()
checkV VTT    VUnit = return ()
checkV VTT    _     = throwError "Ill-typed!"
checkV VTrue  VBool = return ()
checkV VTrue  _     = throwError "Ill-typed!"
checkV VFalse VBool = return ()
checkV VFalse _     = throwError "Ill-typed!"

checkV VUnit  VType = return ()
checkV VUnit  _     = throwError "Ill-typed!"
checkV VBool  VType = return ()
checkV VBool  _     = throwError "Ill-typed!"
checkV VType  VType = return ()
checkV VType  _     = throwError "Ill-typed!"

checkV (VSg _A _B) VType = do
  checkV _A VType
  checkVExtend _A _B VType
checkV (VSg _A _B) _ =
  throwError "Ill-typed!"

checkV (VPi _A _B) VType = do
  checkV _A VType
  checkVExtend _A _B VType
checkV (VPi _A _B) _ =
  throwError "Ill-typed!"

checkV (VLam b) (VPi _A _B) =
  checkVExtend2 _A b _B
checkV (VLam _) _ =
  throwError "Ill-typed!"

checkV (VPair a b) (VSg _A _B) = do
  checkV a _A
  checkV b =<< _B `sub` a
checkV (VPair _ _) _ =
  throwError "Ill-typed!"

checkV (VNeut nm fs) _B = do
  _B' <- inferN nm fs
  unless (_B == _B') $
    throwError "Ill-typed!"

----------------------------------------------------------------------

inferN :: Nom -> Spine -> SpireM Type
inferN nm Id = lookupType nm

inferN nm (Pipe fs (EApp a)) = do
  _AB <- inferN nm fs
  case _AB of
    VPi _A _B -> do
      checkV a _A
      _B `sub` a
    _         -> throwError "Ill-typed!"

inferN nm (Pipe fs EProj1) = do
  _AB <- inferN nm fs
  case _AB of
    VSg _A _B -> return _A
    _         -> throwError "Ill-typed!"

inferN nm (Pipe fs EProj2) = do
  _AB <- inferN nm fs
  case _AB of
    VSg _A _B -> _B `sub` VNeut nm (Pipe fs EProj1)
    _         -> throwError "Ill-typed!"

inferN nm (Pipe fs (ECaseBool _P _ _)) = do
  _A <- inferN nm fs
  case _A of
    VBool -> _P `sub` VNeut nm fs
    _     -> throwError "Ill-typed!"  

----------------------------------------------------------------------

checkVExtend :: Type -> Bind Nom Value -> Type -> SpireM ()
checkVExtend _A bnd_b _B = do
  (x , b) <- unbind bnd_b
  extendCtx x _A $ checkV b _B

checkVExtend2 :: Type -> Bind Nom Value -> Bind Nom Type -> SpireM ()
checkVExtend2 _A bnd_b bnd_B = do
  (nm , b) <- unbind bnd_b
  _B       <- bnd_B `sub` vVar nm
  extendCtx nm _A $ checkV b _B

----------------------------------------------------------------------