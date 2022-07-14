import Mathbin.Data.MvPolynomial.Basic
import Mathbin.Data.Polynomial.Div
import Mathbin.Data.Polynomial.FieldDivision

section

universe u

variable {R : Type u} [CommSemiringₓ R]

/-- Converting a single variable polynomial to a multivariable polynomial and back yields the same polynomial -/
lemma multivariable_to_single_variable (S : Type) (s : S) (f : S → Polynomial R) (hf : f s = @Polynomial.x R _) (t : Polynomial R) : 
  ((t.eval₂ MvPolynomial.c (MvPolynomial.x s)).eval₂ Polynomial.c f) = t := by 
  rw [Polynomial.eval₂, Polynomial.sum]
  simp_rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  conv_lhs => 
  · congr skip
    ext
    rw [hf, Polynomial.X_pow_eq_monomial, ←Polynomial.monomial_zero_left, Polynomial.monomial_mul_monomial]
    simp_rw [zero_addₓ, mul_oneₓ]
  rw [t.as_sum_support.symm]