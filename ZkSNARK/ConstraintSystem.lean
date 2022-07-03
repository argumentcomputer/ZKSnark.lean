/- Rank 1 Constraint System
-/
namespace zkSNARK.ConstraintSystem

universe u v

class Field (F : Type u)

/-
Elements of a given prime field
-/
class PrimeField (F : Type u) [Field F]

/-
Represents the index of either an input variable or
auxiliary variable.
-/
inductive Index
  | Input (index : USize)
  | Aux (index : USize)

structure Indexer (T : Type u) : Type u where
  values : (Array (Prod USize T))
  lastInserted : (Option (Prod USize USize))
deriving Inhabited

structure LinearCombination (Scalar : Type u) [Field Scalar] [PrimeField Scalar] : Type u where
  inputs : (Indexer Scalar)
  aux : (Indexer Scalar)
deriving Inhabited
  
inductive SynthesisError
    -- During synthesis, we lacked knowledge of a variable assignment.
    --[error("an assignment for a variable could not be computed")]
    | AssignmentMissing
    -- During synthesis, we divided by zero.
    --[error("division by zero")]
    | DivisionByZero
    -- During synthesis, we constructed an unsatisfiable constraint system.
    --[error("unsatisfiable constraint system")]
    | Unsatisfiable
    -- During synthesis, our polynomials ended up being too high of degree
    --[error("polynomial degree is too large")]
    | PolynomialDegreeTooLarge
    -- During proof generation, we encountered an identity in the CRS
    --[error("encountered an identity element in the CRS")]
    | UnexpectedIdentity
    -- During proof generation, we encountered an I/O error with the CRS
    --[error("encountered an I/O error: {0}")]
    | IoError --(--[from] io::Error),
    -- During verification, our verifying key was malformed.
    --[error("malformed verifying key")]
    | MalformedVerifyingKey
    -- During CRS generation, we observed an unconstrained auxiliary variable
    --[error("auxiliary variable was unconstrained")]
    | UnconstrainedVariable
    -- During GPU multiexp/fft, some GPU related error happened
    --[error("encountered a GPU error: {0}")]
    | GPUError
    --[error("attempted to aggregate malformed proofs: {0}")]
    | MalformedProofs (s: String)
    --[error("malformed SRS")]
    | MalformedSrs
    --[error("non power of two proofs given for aggregation")]
    | NonPowerOfTwo
    --[error("incompatible vector length: {0}")]
    | IncompatibleLengthVector (s: String)
    --[error("invalid pairing")]
    | InvalidPairing

class ConstraintSystem (CS: Type v) (Scalar: Type u) [Field Scalar] [PrimeField Scalar]


inductive Result (α ε: Type u)
  | ok    : α → Result α ε
  | error : ε → Result α ε
/-
Computations are expressed in terms of arithmetic circuits, in particular
rank-1 quadratic constraint systems. The `Circuit` trait represents a
circuit that can be synthesized. The `synthesize` method is called during
CRS generation and during proving.
-/
class inductive Circuit (Scalar: Type u) [Field Scalar]
    [PrimeField Scalar] {CS: Type v} [ConstraintSystem CS Scalar]
    -- Synthesize the circuit into a rank-1 quadratic constraint system.
| synthesize : (self : Circuit Scalar) → (cs: CS) → (r : Result Unit SynthesisError) -> Circuit
Scalar