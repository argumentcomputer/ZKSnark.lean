import Mathbin

namespace MonomialPow

universe u

variable {R : Type u}
variable {_ : Type_}

-- variable [CommSemiringₓ R]

-- open MvPolynomial

/- Converting a single variable polynomial to a multivariable polynomial  
and back yields the same polynomial 
lemma monomial_pow {s : Finsupp S →₀ ℕ} {a : R} {n : ℕ} :
  monomial s a ^ n = monomial (n • s) (a ^ n) := by
  induction n
  rw [monomial_eq]
  simp
  -- rw nat.succ_eq_add_one,
  simp [pow_succ, succ_nsmul]
  rw [n_ih]
  rw [monomial_mul]
  -- library_search,


end MonomialPow