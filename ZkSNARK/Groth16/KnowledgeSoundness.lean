import Mathbin

import ZkSNARK.GeneralLemmas.MvDivisibility
import ZkSNARK.Groth16.Vars

noncomputable section

namespace Groth16
open Finset Polynomial

variable {F : Type u} [field : Field F]

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

/- t is the polynomial divisibility by which is used to verify satisfaction of the SSP -/
def t : Polynomial F := 
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
    + ∑ i in finRange n_wit, a_wit i • w_wit i) : F[X]) %ₘ (t r) = 0

/- The coefficients of the CRS elements in the algebraic adversary's representation -/
register_simp_attr crs "Attribute for defintions of CRS elements"

/- The crs elements 
These funtions are actually multivariate Laurent polynomials of the toxic waste samples, 
but we represent them here as functions on assignments of the variables to values.
-/
def crs_α  (f : Vars → F) (x : F) : F := f Vars.α

def crs_β (f : Vars → F) (x : F) : F := f Vars.β

def crs_γ (f : Vars → F) (x : F) : F := f Vars.γ

def crs_δ (f : Vars → F) (x : F) : F := f Vars.δ

def crs_powers_of_x (i : Finₓ n_var) (f : Vars → F) (x : F) : F := (x)^(i : ℕ)

def crs_l (i : Finₓ n_stmt) (f : Vars → F) (x : F) : F := 
  ((f Vars.β / f Vars.γ) * (u_stmt i).eval (x)
  +
  (f Vars.α / f Vars.γ) * (v_stmt i).eval (x)
  +
  (w_stmt i).eval (x)) / f Vars.γ

def crs_m (i : Finₓ n_wit) (f : Vars → F) (x : F) : F := 
  ((f Vars.β / f Vars.δ) * (u_wit i).eval (x)
  +
  (f Vars.α / f Vars.δ) * (v_wit i).eval (x)
  +
  (w_wit i).eval (x)) / f Vars.δ

def crs_n (i : Finₓ (n_var - 1)) (f : Vars → F) (x : F) : F := 
  ((x)^(i : ℕ)) * (t r).eval x / f Vars.δ

variable { A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ  : F }
variable { A_x B_x C_x : Finₓ n_var → F }
variable { A_l B_l C_l : Finₓ n_stmt → F }
variable { A_m B_m C_m : Finₓ n_wit → F }
variable { A_h B_h C_h : Finₓ (n_var - 1) → F }


/- Polynomial forms of the adversary's proof representation -/
def A (f : Vars → F) (x : F) : F := 
  (A_α * crs_α f x)
  +
  (A_β * crs_β f x : F)
  + 
  A_γ * crs_γ f x
  +
  A_δ * crs_δ f x
  +
  ∑ i in (finRange n_var), (A_x i) * (crs_powers_of_x i f x)
  +
  ∑ i in (finRange n_stmt), (A_l i) ⬝ crs_l i f x
  +
  ∑ i in (finRange n_wit), (A_m i) * (crs_m i f x)
  +
  ∑ i in (finRange (n_var-1)), (A_h i) * (crs_n i f x)

def B (f : Vars → F) (x : F) : F  := 
  (((B_α * crs_α f x)
  +
  B_β * crs_β f x
  + 
  B_γ * crs_γ f x
  +
  B_δ * crs_δ f x
  +
  ∑ i in (finRange n_var), (B_x i) * (crs_powers_of_x i f x)
  +
  ∑ i in (finRange n_stmt), (B_l i) * (crs_l i f x)
  +
  ∑ i in (finRange n_wit), (B_m i) * (crs_m i f x)
  +
  ∑ i in (finRange (n_var - 1)), (B_h i) * (crs_n i f x)) : F)

def C (f : Vars → F) (x : F) : F  := 
  C_α * crs_α f x
  +
  C_β * crs_β f x
  + 
  C_γ * crs_γ f x
  +
  C_δ * crs_δ f x
  +
  ∑ i in (finRange n_var), (C_x i) * (crs_powers_of_x i f x)
  +
  ∑ i in (finRange n_stmt), (C_l i) * (crs_l i f x)
  +
  ∑ i in (finRange n_wit), (C_m i) * (crs_m i f x)
  +
  ∑ i in (finRange (n_var - 1)), (C_h i) * (crs_n i f x)

open MvPolynomial

def Groth16Polynomial := MvPolynomial Vars (Polynomial F)

/- The modified crs elements 
these are multivariate (non-Laurent!) polynomials of the toxic waste samples, 
obtained by multiplying the Laurent polynomial forms of the CRS through by γδ. 
We will later prove that the laurent polynomial equation is equivalent to a similar equation of the modified crs elements, allowing us to construct a proof in terms of polynomials -/
def crs'_α  : @Groth16Polynomial F field := ((Polynomial.x Vars.α) * (Polynomial.x Vars.γ) * (Polynomial.x Vars.δ)) : @Groth16Polynomial F field

def crs'_β : @Groth16Polynomial F field  := (Polynomial.x Vars.β) * (Polynomial.x Vars.γ) * (Polynomial.x Vars.δ)

def crs'_γ : @Groth16Polynomial F field := (Polynomial.x Vars.γ) * (Polynomial.x Vars.γ) * (Polynomial.x Vars.δ)

def crs'_δ : @Groth16Polynomial F field  := (Polynomial.x Vars.δ) * (Polynomial.x Vars.γ) * (Polynomial.x Vars.δ)

def crs'_powers_of_x (i : Finₓ n_var) : @Groth16Polynomial F field := 
  (Polynomial.c (Polynomial.x ^ (i : ℕ))) * (Polynomial.x Vars.γ) * (Polynomial.x Vars.δ)
-- We define prodcuts of these crs elements without the division, then later claim identities. Is this right?

def crs'_l (i : Finₓ n_stmt) : @Groth16Polynomial F field := 
  ((Polynomial.x Vars.β) * (Polynomial.x Vars.δ)) * Polynomial.c (u_stmt i)
  +
  ((Polynomial.x Vars.α) * (Polynomial.x Vars.δ)) * MvPolynomial.c (v_stmt i)
  +
  (Polynomial.x Vars.δ) * Polynomial.c (w_stmt i)

def crs'_m (i : Finₓ n_wit) : @Groth16Polynomial F field := 
  ((Polynomial.x Vars.β) * (Polynomial.x Vars.γ)) * Polynomial.c (u_wit i)
  +
  ((Polynomial.x Vars.α) * (Polynomial.x Vars.γ)) * Polynomial.c (v_wit i)
  +
  (Polynomial.x Vars.γ) * Polynomial.c (w_wit i)


def crs'_t (i : Finₓ (n_var - 1)) : @Groth16Polynomial F field := 
  (Polynomial.x Vars.γ) * Polynomial.c ((Polynomial.x)^(i : ℕ) * t)

def verified (a_stmt : Finₓ n_stmt → F ) : Prop := A * B = crs_α * crs_β + (∑ i in finRange n_stmt, a_stmt i • crs_l i ) * crs_γ + C * crs_δ

def verified' (a_stmt : Finₓ n_stmt → F ) : Prop := A' * B' = crs'_α * crs'_β + (∑ i in finRange n_stmt, (Polynomial.c (a_stmt i)) • crs'_l i ) * crs'_γ + C' * crs'_δ


end Groth16