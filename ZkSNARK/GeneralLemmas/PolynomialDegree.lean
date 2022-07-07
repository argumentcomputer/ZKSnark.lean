import Mathbin

namespace PolynomialDegree

open BigOperators

variable {F : Type u}
variable [Field F]

lemma natDegreeProductForm (m : ℕ) (f : Fin m → F) : 
  Polynomial.natDegree (∏ i in (Finset.range m), (Polynomial.X - Polynomial.C (f i))) = m := by
  -- rw t,
  rw [Polynomial.nat_degree_prod]
  simp
  intros i hi
  exact Polynomial.X_sub_C_ne_zero (f i)

lemma monicOfProductForm (m : ℕ) (f : Fin m → F) : 
  (∏ i in (Finset.range m), (Polynomial.X - Polynomial.C (f i))).Monic := by
  apply Polynomial.monic_prod_of_monic
  intros i hi
  exact Polynomial.monic_X_sub_C (f i)

end PolynomialDegree