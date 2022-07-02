import ZkSNARK.ConstraintSystem
import ZkSNARK

def main : IO UInt32 := do
  try
    ZkSNARK.sayHello "world"
    pure 0
  catch e =>
    IO.eprintln <| "error: " ++ toString e -- avoid "uncaught exception: ..."
    pure 1