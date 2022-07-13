import Mathlib
import Mathbin.Data.MvPolynomial.Basic
import Mathbin.Data.Polynomial.Div

-- Checking some imports used in 
-- <https://github.com/BoltonBailey/formal-snarks-project/blob/master/src/general_lemmas/mv_X_mul.lean>
-- and
-- <https://github.com/BoltonBailey/formal-snarks-project/blob/master/src/general_lemmas/polynomial_mv_sv_cast.lean>

#check @Finsupp.single
#check @Finset.sum_insert
#check MvPolynomial
#check MvPolynomial.coeff_mul_X'
#check Finset.sum_hom_rel
#check Polynomial.eval₂
#check Polynomial.X_pow_eq_monomial
#check Polynomial.monomial_zero_left
#check Polynomial.multiplicity_finite_of_degree_pos_of_monic