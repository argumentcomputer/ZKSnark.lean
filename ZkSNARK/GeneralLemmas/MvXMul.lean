import Mathbin.Data.MvPolynomial.Basic

noncomputable section

open Classical BigOperators

open Set Function Finsupp AddMonoidAlgebra

universe u v
variable {R : Type u} 

namespace MvPolynomial
variable {σ : Type _} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiringₓ

variable [CommSemiringₓ R] {p q : MvPolynomial σ R}

section DecidableEq

variable [DecidableEq σ] (a : σ)

--lemma coeff_X_mul' (m) (s : σ) (p : MvPolynomial σ R) :
--   coeff m (X s * p) = if s ∈ m.support then coeff (m - Finsupp.single s 1) p else 0 := 
-- by
--  rw [mul_comm]
--  rw [MvPolynomial.coeff_mul_X']

end DecidableEq

lemma coeff_mul_X_pow (m : σ →₀ ℕ) (n : ℕ) (s : σ) (p : MvPolynomial σ R) :
  coeff (m + single s n : σ →₀ ℕ) (p * (x s : MvPolynomial σ R) ^ n : MvPolynomial σ R) = coeff m p := by
  have : HasMem.Mem (m, single s n) (m + single s n).antidiagonal := sorry -- mem_antidiagonal.2 _,
  rw [coeff_mul, ← Finset.insert_erase this, Finset.sum_insert (Finset.not_mem_erase _ _),
      Finset.sum_eq_zero, add_zeroₓ, coeff_X_pow, if_pos, mul_oneₓ]
  simp only [eq_self_iff_true]
  intro ⟨i,j⟩ hij
  rw [Finset.mem_erase, mem_antidiagonal] at hij
  by_cases H : single s n = j
  · subst j
    sorry
  · rw [coeff_X_pow, if_neg H, _root_.mul_zero]

-- # TODO
-- lemma support_X_pow [nontrivial R] : (X n ^ e : MvPolynomial σ R).support = {single n e} :=
-- by rw [X_pow_eq_single, support_monomial, if_neg]; exact one_ne_zero

lemma coeff_mul_X_pow' (m : σ →₀ ℕ) (n : ℕ) (s : σ) (p : MvPolynomial σ R) :
  coeff m (p * (x s : MvPolynomial σ R) ^ n : MvPolynomial σ R) = if n ≤ m s then coeff (m - single s n : σ →₀ ℕ) p else 0 := 
by sorry
  -- # TODO: what to do with `nontriviality` and `split_ifs`?
  -- nontriviality R,
  -- split_ifs with h h,
  -- { conv_rhs {rw ← coeff_mul_X_pow _ n s},
  --   congr' with  t,
  --   by_cases hj : s = t,
  --   { subst t, simp only [nat_sub_apply, add_apply, single_eq_same], exact (nat.sub_eq_iff_eq_add h).mp rfl,
  --     },
  --   { simp [single_eq_of_ne hj] } },
  -- { rw ← not_mem_support_iff, intro hm, apply h,
  --   have H := support_mul _ _ hm, simp only [Finset.mem_bUnion] at H,
  --   rcases H with ⟨j, hj, i', hi', H⟩,
  --   rw [support_X_pow, Finset.mem_singleton] at hi', subst i',
  --   rw Finset.mem_singleton at H, subst m,
  --   rw [add_apply, single_apply, if_pos rfl],
  --   finish, }

-- lemma coeff_X_pow_mul' (m) (n : ℕ) (s : σ) (p : MvPolynomial σ R) :
--   coeff m ((x s : MvPolynomial σ R) ^ n * p) = if n ≤ m s then coeff (m - finsupp.single s n : σ →₀ ℕ) p else 0 := by 
--   sorry
-- begin
--   rw mul_comm,
--   rw coeff_mul_X_pow',
-- end


-- # TODO: 
-- Bolton mentions this below; 
-- "For some reason, this lemma is actually useless
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Extracting.20constant.20from.20sum"
-- unification is smart enough to figure out that `Finset.mul_sum` works 
-- without the need to specialize lemmas like this

lemma sum_X_mul {α : Type u} (r : Finset α) (f : α -> MvPolynomial σ R) (s : σ) : 
  (∑ x in r, (MvPolynomial.x s : MvPolynomial σ R) * f x) = (x s : MvPolynomial σ R) * (∑ x in r, f x) := 
by rw [Finset.mul_sum]

lemma sum_C_mul {α : Type u} {r : Finset α} {f : α -> MvPolynomial σ R} (e : R) : 
  (∑ x in r, (c e : MvPolynomial σ R) * f x) = (c e : MvPolynomial σ R) * (∑ x in r, f x) :=
by rw [Finset.mul_sum]

lemma sum_C_hom {α : Type u} {r : Finset α} {f : α -> R} : 
  ((∑ x in r, c (f x)) : MvPolynomial σ R) = (c (∑ x in r, f x) : MvPolynomial σ R) := 
by sorry -- exact Finset.sum_hom r c

-- -- TODO add to mathlib
-- instance (s : σ →₀ ℕ) : is_add_monoid_hom (@monomial R σ _ s) := 
-- {
--   map_add := begin
--     intros x y,
--     exact monomial_add.symm,
--   end,
--   map_zero := monomial_zero,
-- }

lemma sum_monomial_hom {α : Type u} {r : Finset α} {f : α -> R}  (s : σ →₀ ℕ) : 
   ((∑ x in r, monomial s (f x)) : MvPolynomial σ R) = monomial s (∑ x in r, f x)
 := by sorry -- Finset.mul_sum r (monomial s)


lemma extract_mul_from_sum {α : Type u} {r : Finset α} {f : α -> MvPolynomial σ R} (p : MvPolynomial σ R) : 
   (∑ x in r, p * f x) = p * (∑ x in r, f x) := 
by rw [Finset.mul_sum]


-- lemma C_mul_C (a a' : R) : (C a) * (C a') = (C (a * a') : MvPolynomial σ R) := by simp


-- lemma C_mul_monomial' (a a' : R) (s : σ →₀ ℕ) : (monomial s a') * C a  = monomial s (a' * a) :=
-- by sorry
-- simp [C_apply, monomial, single_mul_single]

-- lemma C_to_monomial (a : R) : @C _ σ _ a = monomial 0 (a) := by exact C_apply

-- -- For some reason, this lemma is actually useless https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Extracting.20constant.20from.20sum
-- -- I expect many other lemmas in theis file may be useless as well
-- -- TODO investigate and clean up
-- lemma Finset_sum_C {α : Type u} {r : Finset α} {f : α -> R} (e : R) : 
--   (∑ x in r, (C (f x) : MvPolynomial σ R)) = C (∑ x in r, f x)
-- := 
-- begin
--   rw Finset.sum_hom,
-- end

lemma rearrange1 (n : ℕ) (v1 v2 : σ) (p : MvPolynomial σ R) :
  ((MvPolynomial.x v1) ^ n) * ((MvPolynomial.x v2) * p) = (MvPolynomial.x v2) * ((MvPolynomial.x v1 ^ n) * p) := 
  by sorry
  --by ring

/--
lemma rearrange2 (n : ℕ) (f : R) (v1 : σ) (p : MvPolynomial σ R) :
  (MvPolynomial.x v1 ^ n) * ((MvPolynomial.c f) * p) = (MvPolynomial.c f) * ((MvPolynomial.x v1 ^ n) * p) := 
  by sorry
  -- by ring

-- -- move constants right of X
lemma rearrange_constants_right (f : R) (v1 : σ) : 
  (MvPolynomial.c f) * MvPolynomial.x v1 = (MvPolynomial.x v1) * (MvPolynomial.c f)
:= by sorry
-- by ring

lemma rearrange_constants_right_with_extra (f : R) (v1 : σ) (p : MvPolynomial σ R) : 
  (MvPolynomial.c f) * ((MvPolynomial.x v1) * p) = (MvPolynomial.X v1) * (MvPolynomial.C f * p)
:= by ring


lemma rearrange_constants_right_hard (f : R) (p : Polynomial R) : 
   Polynomial.c f * p = (p) * (Polynomial.c f)
:= by ring

lemma rearrange_sums_right_with_extra {α : Type u} {r : Finset α} {f : α → MvPolynomial σ R} (s : σ) (p : MvPolynomial σ R) : 
   (∑ x in r, f x) * (X s * p) = X s * (∑ x in r, f x) * p
:= by ring

lemma rearrange_sums_right {α : Type u} {r : Finset α} {f : α → MvPolynomial σ R} (s : σ) : 
   (∑ x in r, f x) * X s = X s * (∑ x in r, f x)
:= by ring

-- -- move constants right of X
lemma rearrange_smul_right (n : ℕ) (a : R) (v1 : σ) (p : MvPolynomial σ R) : 
  a • (MvPolynomial.x v1 * p) = (MvPolynomial.x v1) * (a • p)
:= by rw [mul_smul_comm]

lemma rearrange_001 (f : R) (p1 p2 p3 : Polynomial R) : 
  (Polynomial.c f) * p1 = p2 + p3 ↔ p2 + p3 = (Polynomial.c f) * p1 := by
   split
    { intro h, rw h }
    { intro h, rw h }

lemma rearrange_002 (f : R) (p1 p2 p3 : Polynomial R) : 
  p1 * (Polynomial.c f) = p2 + p3 ↔ p2 + p3 = p1 * (Polynomial.c f) := by
   split
    { intro h, rw h }
    { intro h, rw h }
-/

lemma add_mul_distrib (a b c d : R) : a + b * c + b * d = a + b * (c + d) :=
by ring

lemma add_mul_distrib' (a b c d : R) : a + c * b + d * b = a + b * (c + d) :=
by ring

end CommSemiringₓ

end MvPolynomial