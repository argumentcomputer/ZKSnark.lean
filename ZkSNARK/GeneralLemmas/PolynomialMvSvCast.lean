import Mathbin

open MvPolynomial
open Polynomial

section

namespace PolynomialMvSvCast

variable {R : Type u} [semi : Semiringₓ R][comm : CommSemiringₓ R]

#check @Polynomial.x
#check @MvPolynomial.c
#check Polynomial.eval₂

/- Converting a single variable polynomial to a multivariable polynomial and back yields the same polynomial -/
lemma multivariable_to_single_variable (S : Type) (s : S) 
     (f : S → Polynomial R) (t : Polynomial R) (hf : f s = Polynomial.x) : 
     ((t.eval₂ MvPolynomial.c s (MvPolynomial.x s)).eval₂ Polynomial.c f) = t := by sorry
/-
  -- ext,
  rw [Polynomial.eval₂]
  -- rw polynomial.coeff_sum,
  rw [Polynomial.sum]
  conv =>
    lhs
    congr
    skip
    funext
    rw [hf]
    rw [Polynomial.X_pow_eq_monomial]
    rw [←Polynomial.monomial_zero_left]
    rw [Polynomial.monomial_mul_monomial]
    simp
  -- rw ←polynomial.coeff,
  rw [t.as_sum_support.symm]
-/
end PolynomialMvSvCast