import Mathbin

import Mathbin.Data.Finset
import Mathbin.Data.Finsupp

section

open MvPolynomial

@[simp] 
lemma eq_zero_of_zero_eq (R : Type u) [HasZero R] (r : R) : 0 = r ↔ r = 0 :=
  by exact eq_comm

@[simp] lemma zero_sub_eq_iff (R : Type u) [AddCommGroup R] (a b : R) : 0 - a = b ↔ a + b = 0 := by
  apply Iff.intro
  · intro h
    rw [←h]
    sorry --abel

register_simp_attr polynomial_nf "Attribute for lemmas that are used in the conversion of mv_polynomial expressions to a normal form consisting of adds of sums of muls of mv_polynomials"

attribute [polynomial_nf] Polynomial.eval₂
attribute [polynomial_nf] Polynomial.sum
attribute [polynomial_nf] Finsupp.sum
attribute [polynomial_nf] mul_add
attribute [polynomial_nf] add_mul
attribute [polynomial_nf] Finset.sum_mul
attribute [polynomial_nf] Finset.mul_sum
attribute [polynomial_nf] Finset.sum_add_distrib
