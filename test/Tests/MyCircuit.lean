import ZKSnark
import ZKSnark.Utils

open ZKSnark
open ResultM
universe u


structure MyCircuit : Type u where
  /-
  The input to SHA-256d we are proving that we know.
  Set to `None` when we are verifying a proof
  (and do not have the witness data).
  -/
  preimage: Option ByteArray

namespace MyCircuit

def synthesize {CS Scalar: Type u} [ConstraintSystem CS Scalar] (self : MyCircuit) : ResultM SynthesisError CS PUnit := do {
    /-
    Compute the values for the bits of the preimage. If we are verifying a proof,
    we still need to create the same constraints, so we return an equivalent-size
    Vec of None (indicating that the value of each bit is unknown).
    -/
    let bit_values : Array (Option UInt8) := 
      if let some preimage := self.preimage
      then (ByteArray.map (λ byte => map [0:8] (λ i => ((byte >>> i) && 1) == 1)) preimage)
      else Array.mk (List.replicate (80 * 8) none);

    let preimage_bits := for (i, optb) in Array.enumerate bit_values do {
      match optb with
        | some b => true;
        | _ => false;
    }
    /- let hash ← sha256d preimage_bits -/
    return PUnit.unit;
  }

instance (Scalar : Type u) [PrimeField Scalar] : Circuit Scalar MyCircuit where
  synthesize := MyCircuit.synthesize


end MyCircuit    
