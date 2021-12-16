import zkSNARK
import zkSNARK.ConstraintSystem

open zkSNARK
universe u

structure MyCircuit where
  /-
  The input to SHA-256d we are proving that we know.
  Set to `None` when we are verifying a proof
  (and do not have the witness data).
  -/
  preimage: Option ByteArray

instance (Scalar : Type u) [PrimeField Scalar] : Circuit Scalar MyCircuit where
  synthesize : {CS : Type u} [ConstraintSystem CS] → (self : A) → ResultM CS := do
    /-
    Compute the values for the bits of the preimage. If we are verifying a proof,
    we still need to create the same constraints, so we return an equivalent-size
    Vec of None (indicating that the value of each bit is unknown).
    -/
    let bit_values : Array (Option UInt8) ← if let some preimage := self.preimage
      then ByteArray.map preimage (fun byte => )
      else List.repeat none (80 * 8)
    
