import Mathbin

import ZkSNARK.GeneralLemmas.MvDivisibility
import ZkSNARK.Groth16.Vars

noncomputable section

namespace Groth16
open Finset Polynomial

variable {F : Type u} [Field F]

/- n_stmt - the statement size, 
n_wit - the witness size -/ 
variable {n_stmt n_wit n_var : ℕ}

/- u_stmt and u_wit are fin-indexed collections of polynomials from the square span program -/
variable (u_stmt : Finₓ n_stmt → F[X] )
variable (u_wit : Finₓ n_wit → F[X] )
variable (v_stmt : Finₓ n_stmt → F[X] )
variable (v_wit : Finₓ n_wit → F[X] )
variable (w_stmt : Finₓ n_stmt → F[X] )
variable (w_wit : Finₓ n_wit → F[X] )

-- def l : ℕ := n_stmt
-- def m : ℕ := n_wit

/- The roots of the polynomial t -/
variable (r : Finₓ n_wit → F)
/-- t is the polynomial divisibility by which is used to verify satisfaction of the SSP -/
def t : F[X] := 
  ∏ i in finRange n_wit, (x : F[X]) - c (r i)

lemma nat_degree_t : (t r).natDegree = n_wit := by
  rw [t, Polynomial.nat_degree_prod]
  have h1 : ∀ x : F, RingHom.toFun Polynomial.c x = coeFn Polynomial.c x
  · intro
    rw [RingHom.to_fun_eq_coe]
  conv_lhs =>
  · congr
    skip
    ext
    simp_rw [h1 (r _), Polynomial.nat_degree_X_sub_C]
  rw [Finset.sum_const, Finset.fin_range_card, Algebra.id.smul_eq_mul, mul_oneₓ]
  intros
  apply Polynomial.X_sub_C_ne_zero

lemma monic_t : Polynomial.Monic (t r) := by
  rw [t]
  apply Polynomial.monic_prod_of_monic
  intros
  exact Polynomial.monic_X_sub_C (r _)

lemma degree_t_pos (hm : 0 < n_wit) : 0 < (t r).degree := by
  suffices h : (t r).degree = some n_wit
  · rw [h]
    apply WithBot.some_lt_some.2
    exact hm

  have h := nat_degree_t r
  rw [Polynomial.natDegree] at h

  revert h -- this is needed because degree (t r) is not substituted in h otherwise
  induction degree (t r)

  · intro h
    rw [Option.get_or_else_none] at h
    rw [eq_comm]
    rw [← h] at hm
    exfalso
    simp at hm
  
  intro h
  rw [Option.get_or_else_some] at h
  rw [h]

-- Single variable form of V_wit
def V_wit_sv (a_wit : Finₓ n_wit → F) : Polynomial F := 
  ∑ i in finRange n_wit, a_wit i • u_wit i

/- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
def V_stmt_sv (a_stmt : Finₓ n_stmt → F) : Polynomial F := 
  ∑ i in finRange n_stmt, a_stmt i • u_stmt i

/- Checks whether a statement witness pair satisfies the SSP -/
def satisfying (a_stmt : Finₓ n_stmt → F) (a_wit : Finₓ n_wit → F) := 
  (((∑ i in finRange n_stmt, a_stmt i • u_stmt i)
    + ∑ i in finRange n_wit, a_wit i • u_wit i) 
  *
  ((∑ i in finRange n_stmt, a_stmt i • v_stmt i)
    + ∑ i in finRange n_wit, a_wit i • v_wit i)
  -
  ((∑ i in finRange n_stmt, a_stmt i • w_stmt i)
    + ∑ i in finRange n_wit, a_wit i • w_wit i)) %ₘ t r = 0

-- run_cmd mk_simp_attr `crs

end Groth16