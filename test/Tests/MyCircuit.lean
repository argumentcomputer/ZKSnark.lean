import zkSNARK
import zkSNARK.ConstraintSystem

open zkSNARK
universe u


structure MyCircuit : Type u where
  /-
  The input to SHA-256d we are proving that we know.
  Set to `None` when we are verifying a proof
  (and do not have the witness data).
  -/
  preimage: Option ByteArray

instance (Scalar : Type u) [PrimeField Scalar] : Circuit Scalar MyCircuit where
  synthesize : {CS : Type u} → [ConstraintSystem CS Scalar] → (self : MyCircuit) → ResultM SynthesisError CS PUnit := do
    /-
    Compute the values for the bits of the preimage. If we are verifying a proof,
    we still need to create the same constraints, so we return an equivalent-size
    Vec of None (indicating that the value of each bit is unknown).
    -/
    let bit_values : Array (Option UInt8) ← if let some preimage := self.preimage
      then ByteArray.map preimage (λ byte => map [0:8] (λ i => ((Nat.shiftRight byte i) && 1) == 1)))
      else List.repeat none (80 * 8);

    let preimage_bits ← for (i, optb) in Array.enumerate bit_values do
      match optb 
        | some b => true
        | _ => false
    /- let hash ← sha256d preimage_bits -/
    return ()

    
