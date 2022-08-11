import Mathbin

open MvPolynomial

@[simp] 
lemma eq_zero_of_zero_eq (R : Type u) [HasZero R] (r : R) : 0 = r ↔ r = 0 :=
  by exact eq_comm

@[simp] lemma zero_sub_eq_iff (R : Type u) [AddCommGroup R] (a b : R) : 0 - a = b ↔ a + b = 0 := by
  apply Iff.intro
  · intro h
    rw [←h]
    sorry
  · sorry

register_simp_attr polynomial_nf 
  "Attribute for lemmas that are used in the conversion of mv_polynomial expressions to a normal form consisting of adds of sums of muls of mv_polynomials"

attribute [polynomial_nf] Polynomial.eval₂
attribute [polynomial_nf] Polynomial.sum
attribute [polynomial_nf] Finsupp.sum
attribute [polynomial_nf] mul_add
attribute [polynomial_nf] add_mul
attribute [polynomial_nf] Finset.sum_mul
attribute [polynomial_nf] Finset.mul_sum
attribute [polynomial_nf] Finset.sum_add_distrib
attribute [polynomial_nf] mul_assoc
attribute [polynomial_nf] finsupp.smul_sum
attribute [polynomial_nf] mul_smul_comm
attribute [polynomial_nf] smul_add
attribute [polynomial_nf] mul_smul
attribute [polynomial_nf] smul_mul_assoc

register_simp_attr polynomial_nf_2
  "Attribute for lemmas that are used in the conversion of mv_polynomial expressions to a normal form consisting of adds of sums of muls of mv_polynomials"

attribute [polynomial_nf_2] mul_add
attribute [polynomial_nf_2] add_mul
attribute [polynomial_nf_2] finset.sum_add_distrib
attribute [polynomial_nf_2] sum_X_mul
attribute [polynomial_nf_2] sum_C_mul
attribute [polynomial_nf_2] rearrange_constants_right
attribute [polynomial_nf_2] rearrange_constants_right_with_extra
attribute [polynomial_nf_2] rearrange_sums_right
attribute [polynomial_nf_2] rearrange_sums_right_with_extra
attribute [polynomial_nf_2] C_mul_C
attribute [polynomial_nf_2] finset.sum_hom
attribute [polynomial_nf_2] mv_polynomial.smul_eq_C_mul
attribute [polynomial_nf_2] mul_assoc
attribute [polynomial_nf_2] finsupp.smul_sum
attribute [polynomial_nf_2] mul_smul_comm
attribute [polynomial_nf_2] smul_add
attribute [polynomial_nf_2] mul_smul
attribute [polynomial_nf_2] smul_mul_assoc

register_simp_attr polynomial_nf_3
  "Attribute for lemmas that are used in the conversion of mv_polynomial expressions to a normal form consisting of adds of sums of muls of mv_polynomials"

attribute [polynomial_nf_3] mul_add
attribute [polynomial_nf_3] add_mul
attribute [polynomial_nf_3] finset.sum_add_distrib
attribute [polynomial_nf_3] mul_sum_symm
attribute [polynomial_nf_3] rearrange_constants_right
attribute [polynomial_nf_3] rearrange_constants_right_with_extra
attribute [polynomial_nf_3] rearrange_sums_right
attribute [polynomial_nf_3] rearrange_sums_right_with_extra
attribute [polynomial_nf_3] C_mul_C
attribute [polynomial_nf_3] finset.sum_hom
attribute [polynomial_nf_3] mv_polynomial.smul_eq_C_mul
attribute [polynomial_nf_3] mul_assoc
