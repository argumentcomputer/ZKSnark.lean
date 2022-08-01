import Mathbin.Data.Finsupp.Basic

section

inductive Vars : Type
  | α : Vars
  | β : Vars
  | γ : Vars
  | δ : Vars
  deriving BEq

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