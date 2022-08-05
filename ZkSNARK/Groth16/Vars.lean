import Mathbin.Data.Finsupp.Basic

section

inductive Vars : Type
  | α : Vars
  | β : Vars
  | γ : Vars
  | δ : Vars

instance : DecidableEq Vars := 
  fun a b => match a, b with
   | .α, .α => isTrue rfl
   | .α, .β => isFalse (fun h => Vars.noConfusion h)
   | .α, .γ => isFalse (fun h => Vars.noConfusion h)
   | .α, .δ => isFalse (fun h => Vars.noConfusion h)
   | .β, .α => isFalse (fun h => Vars.noConfusion h)
   | .β, .β => isTrue rfl
   | .β, .γ => isFalse (fun h => Vars.noConfusion h)
   | .β, .δ => isFalse (fun h => Vars.noConfusion h)
   | .δ, .α => isFalse (fun h => Vars.noConfusion h)
   | .δ, .β => isFalse (fun h => Vars.noConfusion h)
   | .δ, .γ => isFalse (fun h => Vars.noConfusion h)
   | .δ, .δ => isTrue rfl
   | .γ, .δ => isFalse (fun h => Vars.noConfusion h)
   | .γ, .γ => isTrue rfl
   | .γ, .β => isFalse (fun h => Vars.noConfusion h)
   | .γ, .α => isFalse (fun h => Vars.noConfusion h)

lemma finsupp_vars_eq_ext (f g : Vars →₀ ℕ) : (f = g) ↔ 
  (f Vars.α = g Vars.α ∧ f Vars.β = g Vars.β ∧ f Vars.γ = g Vars.γ ∧ f Vars.δ = g Vars.δ) := by
  rw [Finsupp.ext_iff]
  apply Iff.intro
  · intro h
    apply And.intro 
    exact h Vars.α
    apply And.intro 
    exact h Vars.β
    apply And.intro 
    exact h Vars.γ
    exact h Vars.δ
  · intro h
    intro a
    induction a
    apply And.left h
    apply And.left (And.right h)
    apply And.left (And.right (And.right h))
    apply And.right (And.right (And.right h))