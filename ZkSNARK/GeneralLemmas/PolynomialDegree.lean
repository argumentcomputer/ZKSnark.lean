import Mathbin

namespace PolynomialDegree

open BigOperators

variable {F : Type u}
variable [Field F]

lemma natDegreeProductForm (m : ℕ) (f : Finₓ m → F) : 
  Polynomial.natDegree (∏ i in (Finset.finRange m), (Polynomial.x - Polynomial.c (f i))) = m := by
  -- rw [Polynomial.nat_degree_prod]
  sorry

lemma monicOfProductForm (m : ℕ) (f : Finₓ m → F) : 
  (∏ i in (Finset.finRange m), (x - Polynomial.c (f i))).Monic := by
  apply Polynomial.monic_prod_of_monic
  intros i hi
  sorry
  -- exact Polynomial.monic_X_sub_C (f i)

end PolynomialDegree