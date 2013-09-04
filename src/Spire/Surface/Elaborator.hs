module Spire.Surface.Elaborator (elabProg) where
import Control.Monad.Error
import Control.Monad.Writer
import Control.Applicative
import Data.Traversable
import Unbound.LocallyNameless
import Spire.Canonical.Types
import Spire.Surface.Types
import Spire.Expression.Types

----------------------------------------------------------------------

elabProg :: SProg -> SpireM CProg
elabProg [] = return []
elabProg (SDef nm a _A : xs) = do
  _A'    <- elab _A
  a'     <- elab a
  xs'    <- elabProg xs
  return (CDef nm a' _A' : xs')

----------------------------------------------------------------------

-- Bind a name corresponding to a wild card: the type of a wild card
-- unknown, so we must add another hole for it.
bindWildName :: Nom -> Check -> SpireM Check
bindWildName nm c = do
  _T <- fresh . s2n $ "WILD_TYPE"
  -- ?T:Type. ?nm:T. c
  return . hole _T (Infer IType) . hole nm (Infer . IVar $ _T) $ c
  where
  hole nm _T e = Infer . IBindMeta $ bindHole nm _T e

-- Iterated 'bindWildName'
bindWildNames :: [Nom] -> Check -> SpireM Check
bindWildNames nms c = foldM (flip bindWildName) c (reverse nms)

elab :: Syntax -> SpireM Check
elab s = do
  (c , nms) <- runWriterT $ elabC s
  bindWildNames nms c

----------------------------------------------------------------------

type SpireM' = WriterT [Nom] SpireM

elabC :: Syntax -> SpireM' Check

elabC (SPair a b) = CPair <$> elabC  a <*> elabC b
-- The case where we bind meta vars corresponding to wildcards.  For
-- example, given the input program
--
--   (\x. id _ 3 , 4)
--
-- we elaborate to
--
--   (\x. ?T:Type. ?alpha:T. id alpha x , 4)
--
-- and not
--
--   (\x. id (?T:Type. ?alpha:T. alpha) x , 4)
--
-- or
--
--   ?T:Type. ?alpha:T. (\x. id alpha x , 4) .
--
-- It might also make sense to bind these wildcare related metavars
-- when we encounter an explicit metavar binding, since we might want
-- the explicit binding to be in scope for the wildcard -- we stop
-- here at lambda so that its var will be in scope for the wild card
-- -- but since we don't really expect explicit metavar bindings in
-- input programs, we ignore that case ...
--
-- NOTE: Since we want to use the writer state (names) here, and not
-- propagate it upwards, we work outside the writer monad and then
-- inject the result with 'lift'. Alternatively, we could do
-- everything in the writer monad, and capture the writer state with:
--
--   (e' , nms) <- censor (const []) . listen $ elabC e
elabC (SLam b)    = lift $ do
  (nm , e)   <- unbind b
  (e' , nms) <- runWriterT $ elabC e
  e''        <- bindWildNames nms e'
  return . CLam $ bind nm e''

elabC x@STT         = elabIC x
elabC x@STrue       = elabIC x
elabC x@SFalse      = elabIC x
elabC x@SUnit       = elabIC x
elabC x@SBool       = elabIC x
elabC x@SType       = elabIC x
elabC x@(SPi _ _)   = elabIC x
elabC x@(SSg _ _)   = elabIC x
elabC x@(SVar _)    = elabIC x
elabC x@(SProj1 _)  = elabIC x
elabC x@(SProj2 _)  = elabIC x
elabC x@(SIf _ _ _) = elabIC x
elabC x@(SApp _ _)  = elabIC x
elabC x@(SAnn _ _)  = elabIC x
elabC x@(SWildCard) = elabIC x
elabC x@(SBindMeta _)       = elabIC x
elabC x@(SCaseBool _ _ _ _) = elabIC x

----------------------------------------------------------------------

elabI :: Syntax -> SpireM' Infer

elabI STT       = return ITT
elabI STrue     = return ITrue
elabI SFalse    = return IFalse
elabI SUnit     = return IUnit
elabI SBool     = return IBool
elabI SType     = return IType
elabI (SVar nm) = return $ IVar nm

elabI SWildCard = do
  nm <- fresh $ s2n "WILD"
  tell [nm]
  return $ IVar nm
elabI (SBindMeta b) = do
  -- Approximatley: map 'elabC' over the components of the 'BindMeta'.
  (nm , _T , mt , e) <- unbindMeta b
  _T' <- elabC _T
  mt' <- Data.Traversable.mapM elabC mt
  e'  <- elabC e
  return . IBindMeta $ bindMeta nm _T' mt' e'

elabI (SProj1 ab)   = IProj1 <$> elabI ab
elabI (SProj2 ab)   = IProj2 <$> elabI ab
elabI (SApp f a)    = IApp   <$> elabI f <*> elabC a
elabI (SIf b ct cf) = IIf    <$> elabC b <*> elabI ct <*> elabI cf
elabI (SAnn a _A)   = IAnn   <$> elabC a <*> elabC _A

elabI (SCaseBool _P ct cf b) =
  ICaseBool <$> elabBC _P <*> elabC ct <*> elabC cf <*> elabC b

elabI (SPi _A _B) = IPi <$> elabC _A <*> elabBC _B
elabI (SSg _A _B) = ISg <$> elabC _A <*> elabBC _B

-- Once we have meta variables, we should always be able to infer a type for 
-- a lambda, by inserting a meta variable to type the domain of the lambda,
-- but a pair will still fail because any inferred type for the RHS
-- is a specialized version of a more general type (in which a universal variable
-- standing for the LHS is free).
elabI x@(SPair _ _) = failUnannotated x
elabI x@(SLam _)    = failUnannotated x

----------------------------------------------------------------------

elabBC :: Bind Nom Syntax -> SpireM' (Bind Nom Check)
elabBC bnd = do
  (nm , a) <- unbind bnd
  a'       <- elabC a
  return   $  bind nm a'

failUnannotated :: Syntax -> SpireM' Infer
failUnannotated a = throwError $
  "Failed to infer the type of this term, please annotate it:\n" ++
  show a

elabIC :: Syntax -> SpireM' Check
elabIC x = Infer <$> elabI x

----------------------------------------------------------------------
