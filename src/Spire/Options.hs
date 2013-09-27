-- For CmdArgs. See
-- http://hackage.haskell.org/packages/archive/cmdargs/latest/doc/html/System-Console-CmdArgs-Implicit.html
{-# OPTIONS_GHC -fno-cse #-}

{-# LANGUAGE DeriveDataTypeable
  , ScopedTypeVariables
  #-}
module Spire.Options (getOpts , Conf(..)) where

import Data.Data
import Data.List (intercalate)
import System.Console.CmdArgs

----------------------------------------------------------------------

data Conf = Conf { metavars :: Bool
--                 , engine :: ThmProver
--                 , idirs :: [FilePath] -- "Include" directories
                 , file :: FilePath
                 } deriving (Show, Data, Typeable)

getOpts :: IO Conf
getOpts = cmdArgs $ Conf
  { metavars = def
    &= help "Use unification to solve for metavars. This will be on by default once implicit solving actually works ..."

  , file = def
    &= argPos 0
    &= typFile

-- Example: enumerating a type; default value; specifying the name of
-- the type enumerated?
{-
    -- Interesting: The lower case versions of the names still work
    -- ??? E.g. you can say '--engine equinox'.
  , engine = Equinox -- The default option.
    &= typ "PROVER"
    &= help ("Use the specified theorem prover. The default is Equinox. The available provers are "++showAll Equinox
++". The prover configurations are in ThmProver.hs.")
-}

-- Example: use built in type; explain 'explicit' option.
{-
  , idirs = ["."] -- Always check current dir first.
    &= explicit -- Don't guess switch names for this option
    &= name "idir" &= name "i"
--    &= ignore -- Don't actually display this option.
    &= typDir
    &= help "Add DIR to the paths searched for imports. This option may be specified multiple times. Import dirs are searched in the order specified, with an implicit \".\" (current dir) first."
-}

  } &=
  verbosity &=
  program "spire" &=
  -- Avoid stupid '-?' default for help switch.
  helpArg [explicit, name "h", name "help"] &=
  summary "Spire Evaluating Type Checker, V 1/0" &=
  details [ "Long description,"
          , "one string"
          , "per line."
          ]
  where
  showAll :: forall a. (Bounded a, Enum a, Show a) => a -> String
  showAll _ = intercalate ", " $ map show [(minBound::a)..maxBound]
