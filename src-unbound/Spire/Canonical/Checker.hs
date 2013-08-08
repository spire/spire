{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , ViewPatterns
  #-}

module Spire.Canonical.Checker where
import Control.Monad.Error
import Control.Monad.Reader
import Unbound.LocallyNameless
import Spire.Unbound.SubstM
import Spire.Canonical.Types
import Spire.Canonical.Evaluator

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

checkV (Elim nm xs) _B = do
  ctx <- asks ctx
  _A  <- inferVar nm ctx
  _B' <- inferEs (vVar nm) _A xs
  unless (_B == _B') $ throwError "Ill-typed!"

checkV a _A = undefined

----------------------------------------------------------------------

inferVar :: Nom -> Tel -> SpireM Type
inferVar = undefined

----------------------------------------------------------------------

inferEs :: Value -> Type -> [Elim] -> SpireM Type
inferEs a _A [] = return _A
inferEs a _A (e : es) = do
  _A' <- inferE a _A e
  a'  <- elim a e
  inferEs a' _A' es

----------------------------------------------------------------------

{-
Here 'Type' is the type of what is being eliminated and 'Value' is that
value as a Spine. We infer the type of the result of 
the elimination.
In other words, 'Value' will always be a (Nom , [Elim]) pair -- a 
spine application.
-}

inferE :: Value -> Type -> Elim -> SpireM Type

inferE _ (VPi _A _B) (EApp a) = do
  checkV a _A
  _B $$ a

inferE _ (VSg _A _B) EProj1 = do
  return _A

inferE ab (VSg _A _B) EProj2 = do
  a <- elim ab EProj1
  _B $$ a

inferE _ _ _ = undefined


----------------------------------------------------------------------

-- inferE :: Nom -> [Elim] -> Type -> [Elim] -> SpireM Type

-- inferE nm xs (VPi _A _B) (y@(EApp a) : ys) = do
--   checkV a _A
--   _B' <- _B $$ a
--   inferE nm (snoc xs y) _B' ys

-- inferE nm xs (VSg _A _B) (y@EProj1 : ys) = do
--   --  return _A
--   undefined

-- -- inferE (VSg _A _B) EProj2 =

-- inferE _ _ _ _ = undefined