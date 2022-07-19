import Mathbin.Data.MvPolynomial.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Ring

open MvPolynomial

section

universe u

variable {F : Type u} [Field F]

variable {vars : Type}
variable [DecidableEq vars]

noncomputable def increment (f : vars →₀ ℕ) (s : vars) : (vars →₀ ℕ) := f + Finsupp.single s (1 : ℕ)

variable (f g : vars →₀ ℕ)

noncomputable def decrement (f : vars →₀ ℕ) (s : vars) : (vars →₀ ℕ) := f - Finsupp.single s (1 : ℕ)

lemma inc_nochange (f : vars →₀ ℕ) {s a : vars} (hsa : ¬ s = a) : increment f s a = f a := by
  change coeFn f a + coeFn (Finsupp.single s 1) a =  coeFn f a
  rw [Finsupp.single_eq_of_ne hsa]
  ring

lemma inc_change (f : vars →₀ ℕ) {s a : vars} (hsa : s = a) : increment f s a = f a + 1 := by
  change coeFn f a + coeFn (Finsupp.single s 1) a =  coeFn f a + 1
  rw [hsa, Finsupp.single_eq_same]

lemma dec_nochange (f : vars →₀ ℕ) {s a : vars} (hsa : ¬ s = a) : decrement f s a = f a := by
  change coeFn f a - coeFn (Finsupp.single s 1) a =  coeFn f a
  rw [Finsupp.single_eq_of_ne hsa]
  ring

lemma dec_change (f : vars →₀ ℕ) {s a : vars} (hsa : s = a) : decrement f s a = f a - 1 := by
  change coeFn f a - coeFn (Finsupp.single s 1) a =  coeFn f a - 1
  rw [hsa, Finsupp.single_eq_same]


-- The fact that I need to include all of these lemmas is weird...
lemma coefn_funlike {α : vars →₀ ℕ} : coeFn α = FunLike.coe α := by rfl

lemma one_eq_one (n : ℕ) : n - 1 = n - One.one := by rfl 

lemma equal_dec_equal 
  (s : vars) (f g : vars →₀ ℕ) 
  (hf : 0 < f s) 
  (hg : 0 < g s) 
  (hxy : decrement f s = decrement g s) : 
  f = g := 
by 
  apply Finsupp.ext
  intro a
  rw [FunLike.ext_iff] at hxy
  specialize hxy a
  by_cases h : s = a
  · rw [coefn_funlike, coefn_funlike] at *
    rw [dec_change f h, dec_change g h, 
        one_eq_one, one_eq_one, 
        ← Nat.pred_eq_sub_one (FunLike.coe f a), 
        ← Nat.pred_eq_sub_one (FunLike.coe g a)] at hxy
    rw [h] at hf hg
    exact Nat.pred_injₓ hf hg hxy
  · rw [coefn_funlike, coefn_funlike] at *
    rw [dec_nochange f h, dec_nochange g h] at hxy
    exact hxy

lemma inc_dec_nonzero_equal 
  (s : vars) (f : vars →₀ ℕ) (hf : 0 < f s) : 
  increment (decrement f s) s = f := 
by
  apply Finsupp.ext
  intro a
  by_cases h : s = a
  · change (coeFn f) a - (coeFn $ Finsupp.single s 1) a + (coeFn $ Finsupp.single s 1) a = coeFn f a
    rw [h, Finsupp.single_eq_same]
    rw [← coefn_funlike, h] at hf
    exact Nat.succ_pred_eq_of_posₓ hf
  · change (coeFn f) a - (coeFn $ Finsupp.single s 1) a + (coeFn $ Finsupp.single s 1) a = coeFn f a
    rw [Finsupp.single_eq_of_ne h]
    ring

lemma dec_inc_equal (s : vars) (f : vars →₀ ℕ) : decrement (increment f s) s = f := by
  apply Finsupp.ext
  intro a
  by_cases h : s = a
  · change (coeFn f) a + (coeFn $ Finsupp.single s 1) a - (coeFn $ Finsupp.single s 1) a = coeFn f a
    rw [h, Finsupp.single_eq_same]
    ring
  · change (coeFn f) a + (coeFn $ Finsupp.single s 1) a - (coeFn $ Finsupp.single s 1) a = coeFn f a
    rw [Finsupp.single_eq_of_ne h]
    ring

/-
the div_X function in data.polynomial.div returns a polynomial in the form of a curly-brace enclosed support, to_fun, mem_support_to_fun
This is because a polynomial is defined as an add_monoid_algebra, which is a finsupp function, which has these three fields
Explicity
  support is the support of the function
  to_fun is the function itself
  mem_support_to_fun is the proof that the function is nonzero exacly on it's defined support
Frankly, this function should be generalized to all mv_polynomials
Not just mv_polynomials over vars
TODO generalize this method and add to mathlib candidates folder
-/
noncomputable def div_X_v2 (p : MvPolynomial vars F) (s : vars) 
             (h : (∀ m : vars →₀ ℕ, m s = 0 -> p.coeff m = 0)) 
             : MvPolynomial vars F where
  toFun              := fun m => p.coeff (increment m s)
  support            := p.support.image (fun m => decrement m s)
  mem_support_to_fun := by
    intro a
    dsimp
    apply Iff.intro
    · intro h1
      have h2 := Finset.mem_image.1 h1
      rcases h2 with ⟨a_1, H, h3⟩
      rw [Eq.symm h3]
      clear h3
      clear h1
      have h4 : p.coeff a_1 ≠ 0 := (p.mem_support_to_fun a_1).1 H
      clear H
      suffices h6 : increment (decrement a_1 s) s = a_1
      rw [h6]
      exact h4
      have h7 : a_1 s ≠ 0
      intro foo
      apply h4
      apply h
      exact foo
      have h8 := Nat.pos_of_ne_zero h7
      apply inc_dec_nonzero_equal s a_1
      sorry -- exact h8 -- some annoying LE vs. < issues
    · intro h1
      apply Finset.mem_image.2
      apply Exists.intro (increment a s)
      apply Exists.intro
      exact dec_inc_equal s a
      exact (p.mem_support_to_fun (increment a s)).2 h1

/-- In the product of a polynomial with a variable, the coefficients of all terms without that variable are zero -/
lemma coeff_mul_X_eq_zero (a : MvPolynomial vars F) (s : vars) (m : vars →₀ ℕ) :
  m s = (0 : ℕ) → (a * (MvPolynomial.x s : MvPolynomial vars F)).coeff m = 0 :=
by 
  intro hc
  rw [coeff_mul_X']
  apply if_neg
  rw [Finsupp.not_mem_support_iff, coefn_funlike, hc]
  rfl

-- TODO: the converse of the above statement
lemma right_cancel_X_mul {a b : MvPolynomial vars F} (s : vars) 
  (h : a * (x s : MvPolynomial vars F) = b * (x s : MvPolynomial vars F)) :
  a = b :=
by 
  apply MvPolynomial.ext _ _ (λ m => ?_)
  rw [← coeff_mul_X m s a, ← coeff_mul_X m s b, h]

lemma left_cancel_X_mul {a b : MvPolynomial vars F} (s : vars) 
  (h : (x s : MvPolynomial vars F) * a = (x s : MvPolynomial vars F) * b):
  a = b :=
by 
  apply right_cancel_X_mul s
  rw [_root_.mul_comm, h, _root_.mul_comm]

-- For all monomials with no X component, the coefficient of a is zero
-- a * b = c
-- then for all monomials with no X component, the coefficient of a is zero
lemma mul_no_constant_no_constant (a b c : MvPolynomial vars F) (s : vars) :
  (∀ m : vars →₀ ℕ, m s = 0 → a.coeff m = 0) → (a * b = c) → ∀ m : vars →₀ ℕ, m s = 0 -> c.coeff m = 0 :=
by
  intros ha heq m hc
  let aDivX := div_X_v2 a s ha
  have h1 : aDivX * (@x F vars _ s) = a
  · rw [ext_iff]
    intro m2
    rw [coeff_mul_X']
    by_cases h : HasMem.Mem s m2.support
    · have h2 : aDivX.coeff (Sub.sub m2 (Finsupp.single s One.one)) = a.coeff m2 := by
        have h3 : aDivX.coeff (Sub.sub m2 (Finsupp.single s One.one)) = a.coeff (increment (Sub.sub m2 (Finsupp.single s One.one)) s) := rfl
        rw [h3]
        clear h3
        have h4 : a.coeff (increment (Sub.sub m2 (Finsupp.single s One.one)) s) = a.coeff (increment (decrement m2 s) s) := rfl
        rw [h4]
        clear h4
        have h5 := (m2.mem_support_to_fun s).1 h
        have h6 := inc_dec_nonzero_equal s m2 (sorry) -- (Nat.pos_of_ne_zero h5) -- doesn't work because of LE vs < 
        rw [h6]
      change (if HasMem.Mem s m2.support then coeff (Sub.sub m2 (Finsupp.single s One.one)) aDivX else Zero.zero) = coeff m2 a
      rw [h2]
      clear h2
      apply if_pos
      exact h
    · have h7 : a.coeff m2 = 0 := by
        apply ha
        by_contra a_1
        apply h ((m2.mem_support_to_fun s).2 a_1)
      rw [h7]
      apply if_neg
      exact h 
  · have h4 : (aDivX * (@x F vars _ s)) * b = c := by
      rw [h1]
      exact heq
    clear h1
    rw [←h4]
    conv => 
      lhs
      congr
      skip
      rw [_root_.mul_comm, ←_root_.mul_assoc]
    apply coeff_mul_X_eq_zero
    exact hc