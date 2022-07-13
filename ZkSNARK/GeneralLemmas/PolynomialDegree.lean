import Mathbin

namespace PolynomialDegree

open BigOperators

variable {F : Type u}
variable [Field F]

lemma natDegreeProductForm (m : ℕ) (f : Finₓ m → F) : 
  Polynomial.natDegree (∏ i in (Finset.finRange m), (Polynomial.x - Polynomial.c (f i))) = m := by
  sorry
/-
  -- rw [t]
  rw [Polynomial.nat_degree_prod]
  simp
  intros i hi
  exact Polynomial.X_sub_C_ne_zero (f i)


lemma monicOfProductForm (m : ℕ) (f : Finₓ m → F) : 
  (∏ i in (Finset.range m), (Polynomial.x - Polynomial.c (f i))).Monic := by
  apply Polynomial.monic_prod_of_monic
  intros i hi
  exact Polynomial.monic_X_sub_C (f i)
-/
end PolynomialDegree