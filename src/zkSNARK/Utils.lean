/-
Utilities and types.
-/

universe u

namespace Array

def enumerate {A : Type u} (as : Array A) : Array (Nat × A) :=
  Array.mk as.toList.enum

end Array

namespace ResultM

/-
A result wich keeps track of a state. Result Error State Ok. Modified EStateM.
-/
inductive Result (ε σ α : Type u) where
  | ok    : α → σ → Result ε σ α
  | error : ε → σ → Result ε σ α

variable {ε σ α : Type u}

instance [Inhabited ε] [Inhabited σ] : Inhabited (Result ε σ α) where
  default := Result.error arbitrary arbitrary

end ResultM

open ResultM (Result) in
def ResultM (ε σ α : Type u) := σ → Result ε σ α

namespace ResultM

variable {ε σ α β : Type u}

instance [Inhabited ε] : Inhabited (ResultM ε σ α) where
  default := fun s => Result.error arbitrary s

@[inline] protected def pure (a : α) : ResultM ε σ α := fun s =>
  Result.ok a s

@[inline] protected def set (s : σ) : ResultM ε σ PUnit := fun _ =>
  Result.ok ⟨⟩ s

@[inline] protected def get : ResultM ε σ σ := fun s =>
  Result.ok s s

@[inline] protected def modifyGet (f : σ → Prod α σ) : ResultM ε σ α := fun s =>
  match f s with
  | (a, s) => Result.ok a s

@[inline] protected def throw (e : ε) : ResultM ε σ α := fun s =>
  Result.error e s

/-- Auxiliary instance for saving/restoring the "backtrackable" part of the state. -/
class Backtrackable (δ : outParam (Type u)) (σ : Type u) where
  save    : σ → δ
  restore : σ → δ → σ

@[inline] protected def tryCatch {δ} [Backtrackable δ σ] {α} (x : ResultM ε σ α) (handle : ε → ResultM ε σ α) : ResultM ε σ α := fun s =>
  let d := Backtrackable.save s
  match x s with
  | Result.error e s => handle e (Backtrackable.restore s d)
  | ok               => ok

@[inline] protected def orElse {δ} [Backtrackable δ σ] (x₁ : ResultM ε σ α) (x₂ : Unit → ResultM ε σ α) : ResultM ε σ α := fun s =>
  let d := Backtrackable.save s;
  match x₁ s with
  | Result.error _ s => x₂ () (Backtrackable.restore s d)
  | ok               => ok

@[inline] def adaptExcept {ε' : Type u} (f : ε → ε') (x : ResultM ε σ α) : ResultM ε' σ α := fun s =>
  match x s with
  | Result.error e s => Result.error (f e) s
  | Result.ok a s    => Result.ok a s

@[inline] protected def bind (x : ResultM ε σ α) (f : α → ResultM ε σ β) : ResultM ε σ β := fun s =>
  match x s with
  | Result.ok a s    => f a s
  | Result.error e s => Result.error e s

@[inline] protected def map (f : α → β) (x : ResultM ε σ α) : ResultM ε σ β := fun s =>
  match x s with
  | Result.ok a s    => Result.ok (f a) s
  | Result.error e s => Result.error e s

@[inline] protected def seqRight (x : ResultM ε σ α) (y : Unit → ResultM ε σ β) : ResultM ε σ β := fun s =>
  match x s with
  | Result.ok _ s    => y () s
  | Result.error e s => Result.error e s

instance : Monad (ResultM ε σ) where
  bind     := ResultM.bind
  pure     := ResultM.pure
  map      := ResultM.map
  seqRight := ResultM.seqRight

instance {δ} [Backtrackable δ σ] : OrElse (ResultM ε σ α) where
  orElse := ResultM.orElse

instance : MonadStateOf σ (ResultM ε σ) where
  set       := ResultM.set
  get       := ResultM.get
  modifyGet := ResultM.modifyGet

instance {δ} [Backtrackable δ σ] : MonadExceptOf ε (ResultM ε σ) where
  throw    := ResultM.throw
  tryCatch := ResultM.tryCatch

@[inline] def run (x : ResultM ε σ α) (s : σ) : Result ε σ α :=
  x s

@[inline] def run' (x : ResultM ε σ α) (s : σ) : Option α :=
  match run x s with
  | Result.ok v _   => some v
  | Result.error .. => none

@[inline] def dummySave : σ → PUnit := fun _ => ⟨⟩

@[inline] def dummyRestore : σ → PUnit → σ := fun s _ => s

/- Dummy default instance -/
instance nonBacktrackable : Backtrackable PUnit σ where
  save    := dummySave
  restore := dummyRestore

end ResultM
