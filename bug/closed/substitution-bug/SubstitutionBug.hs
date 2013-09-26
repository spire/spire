{-# LANGUAGE NoMonomorphismRestriction #-}
import Unbound.LocallyNameless
import Spire.Surface.PrettyPrinter
import Spire.Canonical.Types
import Spire.Canonical.Evaluator
import Spire.Pipeline

s :: String -> Nom
s = s2n

msg1 = do
  let x = s "x"
      y = s "y"
      z = s "z"
      e = VNeut z (Pipe Id (EApp (VNeut y Id)))
      b = bind y e
  b_x <- b `sub` (VNeut x Id)
  -- b'' <- substM y x e
  let p = prettyPrintError
      msg = "x = " ++ p x ++ "\n" ++
            -- "e = " ++ p e ++ "\n" ++
            "b = " ++ p (VLam b) ++ "\n" ++
            "b x = " ++ p b_x
  return msg

msg2 = do
  let x = s "x"
      y = s "y"
      z = y
      e = VNeut z (Pipe Id (EApp (VNeut y Id)))
      b = bind y e
  b_x <- b `sub` (VNeut x Id)
  -- b'' <- substM y x e
  let p = prettyPrintError
      msg = "x = " ++ p x ++ "\n" ++
            -- "e = " ++ p e ++ "\n" ++
            "b = " ++ p (VLam b) ++ "\n" ++
            "b x = " ++ p b_x
  return msg

msg3 = do
  let x = s "x"
      y = s "y"
      e = VNeut y Id
      b = bind y e
  b_x <- b `sub` (VNeut x Id)
  -- b'' <- substM y x e
  let p = prettyPrintError
      msg = "x = " ++ p x ++ "\n" ++
            -- "e = " ++ p e ++ "\n" ++
            "b = " ++ p (VLam b) ++ "\n" ++
            "b x = " ++ p b_x
  return msg

main = mapM_ (putStrLn . (++"\n") . run) [ msg1 , msg2 , msg3 ]
  where
  run x | Right m <- runSpireM x = m
