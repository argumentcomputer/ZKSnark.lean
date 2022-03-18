
import ZKSNark.ConstraintSystem

namespace ZKSnark



end ZKSNark

def main (args : List String) : IO UInt32 := do
  try
    pure 0
  catch e =>
    IO.eprintln <| "error: " ++ toString e
    pure 1

