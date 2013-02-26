open import Spire.Prelude
open import Spire.TypeChecker
module spire where

postulate run : TypeChecker → IO Unit
{-# IMPORT Spire.CLI #-}
{-# COMPILED run Spire.CLI.run #-}

main : IO Unit
main = run checkType


