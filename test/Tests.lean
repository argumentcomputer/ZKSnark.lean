import zkSNARK
import zkSNARK.ConstraintSystem
import Tests.MyCircuit

def main (args : List String) : IO UInt32 := do
  try
    zkSNARK.sayHello "world"
    pure 0
  catch e =>
    IO.eprintln <| "error: " ++ toString e -- avoid "uncaught exception: ..."
    pure 1

