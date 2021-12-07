
namespace zkSNARK

def sayHello (name : String) : IO Unit := do
  println! "Hello {name}!"

end zkSNARK

def main (args : List String) : IO UInt32 := do
  try
    zkSNARK.sayHello "world"
    pure 0
  catch e =>
    IO.eprintln <| "error: " ++ toString e -- avoid "uncaught exception: ..."
    pure 1

