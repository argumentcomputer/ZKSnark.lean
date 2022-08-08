import Mathbin

import ZkSNARK.GeneralLemmas.MvDivisibility
import ZkSNARK.Groth16.Vars

noncomputable section

namespace Groth16
open Finset Polynomial BigOperators

variable {F : Type u} [field : Field F]

/- n_stmt - the statement size, 
n_wit - the witness size -/ 
variable {n_stmt n_wit n_var : ℕ}

/- u_stmt and u_wit are fin-indexed collections of polynomials from the square span program -/
variable {u_stmt : Finₓ n_stmt → F[X]}
variable {u_wit : Finₓ n_wit → F[X]}
variable {v_stmt : Finₓ n_stmt → F[X]}
variable {v_wit : Finₓ n_wit → F[X]}
variable {w_stmt : Finₓ n_stmt → F[X]}
variable {w_wit : Finₓ n_wit → F[X]}

-- def l : ℕ := n_stmt
-- def m : ℕ := n_wit

/- The roots of the polynomial t -/
variable (r : Finₓ n_wit → F)

/- t is the polynomial divisibility by which is used to verify satisfaction of the SSP -/
def t : F[X] := ∏ i in finRange n_wit, (x : F[X]) - c (r i)

lemma nat_degree_t : (t r).natDegree = n_wit := by
  rw [t, Polynomial.nat_degree_prod]
  have h1 : ∀ x : F, RingHom.toFun c x = coeFn Polynomial.c x
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
variable (F)
def crs_α  (f : Vars → F) : F := f Vars.α

def crs_β (f : Vars → F) : F := f Vars.β

def crs_γ (f : Vars → F) : F := f Vars.γ

def crs_δ (f : Vars → F) : F := f Vars.δ

def crs_powers_of_x (i : Finₓ n_var) (x : F) : F := (x)^(i : ℕ)

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

variable {F}
variable { A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ  : F }
variable { A_x B_x C_x : Finₓ n_var → F }
variable { A_l B_l C_l : Finₓ n_stmt → F }
variable { A_m B_m C_m : Finₓ n_wit → F }
variable { A_h B_h C_h : Finₓ (n_var - 1) → F }

#check crs_α
#check crs_n
#check crs_l
#check crs_m

/- Polynomial forms of the adversary's proof representation -/
def A (f : Vars → F) (x : F) : F := 
  (A_α * crs_α F f)
  +
  A_β * crs_β F f
  + 
  A_γ * crs_γ F f
  +
  A_δ * crs_δ F f
  +
  ∑ i in (finRange n_var), (A_x i) * (crs_powers_of_x F i x)
  +
  ∑ i in (finRange n_stmt), (A_l i) * (@crs_l F field n_stmt u_stmt v_stmt w_stmt i f x)
  +
  ∑ i in (finRange n_wit), (A_m i) * (@crs_m F field n_wit u_wit v_wit w_wit i f x)
  +
  ∑ i in (finRange (n_var - 1)), (A_h i) * (crs_n F r i f x)

def B (f : Vars → F) (x : F) : F := 
  B_α * crs_α F f
  +
  B_β * crs_β F f
  + 
  B_γ * crs_γ F f
  +
  B_δ * crs_δ F f
  +
  ∑ i in (finRange n_var), (B_x i) * (crs_powers_of_x F i x)
  +
  ∑ i in (finRange n_stmt), (B_l i) * (@crs_l F field n_stmt u_stmt v_stmt w_stmt i f x)
  +
  ∑ i in (finRange n_wit), (B_m i) * (@crs_m F field n_wit u_wit v_wit w_wit i f x)
  +
  ∑ i in (finRange (n_var - 1)), (B_h i) * (crs_n F r i f x)

def C (f : Vars → F) (x : F) : F  := 
  C_α * crs_α F f
  +
  C_β * crs_β F f
  + 
  C_γ * crs_γ F f
  +
  C_δ * crs_δ F f
  +
  ∑ i in (finRange n_var), (C_x i) * (crs_powers_of_x F i x)
  +
  ∑ i in (finRange n_stmt), (C_l i) * (@crs_l F field n_stmt u_stmt v_stmt w_stmt i f x)
  +
  ∑ i in (finRange n_wit), (C_m i) * (@crs_m F field n_wit u_wit v_wit w_wit i f x)
  +
  ∑ i in (finRange (n_var - 1)), (C_h i) * (crs_n F r i f x)



/- The modified crs elements 
these are multivariate (non-Laurent!) polynomials of the toxic waste samples, 
obtained by multiplying the Laurent polynomial forms of the CRS through by γδ. 
We will later prove that the laurent polynomial equation is equivalent to a similar equation of the modified crs elements, allowing us to construct a proof in terms of polynomials -/
def crs'_α  : MvPolynomial Vars (Polynomial F) := (MvPolynomial.x Vars.α) * (MvPolynomial.x Vars.γ) * (MvPolynomial.x Vars.δ)

def crs'_β : MvPolynomial Vars (Polynomial F) := (MvPolynomial.x Vars.β) * (MvPolynomial.x Vars.γ) * (MvPolynomial.x Vars.δ)

def crs'_γ : MvPolynomial Vars (Polynomial F) := (MvPolynomial.x Vars.γ) * (MvPolynomial.x Vars.γ) * (MvPolynomial.x Vars.δ)

def crs'_δ : MvPolynomial Vars (Polynomial F) := (MvPolynomial.x Vars.δ) * (MvPolynomial.x Vars.γ) * (MvPolynomial.x Vars.δ)

def crs'_powers_of_x (i : Finₓ n_var) : MvPolynomial Vars (Polynomial F) := 
  (MvPolynomial.c ((MvPolynomial.x)^(i : ℕ))) * (MvPolynomial.x Vars.γ) * (MvPolynomial.x Vars.δ)
-- We define prodcuts of these crs elements without the division, then later claim identities. Is this right?

def crs'_l (i : Finₓ n_stmt) : MvPolynomial Vars (Polynomial F) := 
  ((MvPolynomial.x Vars.β) * (MvPolynomial.x Vars.δ)) * MvPolynomial.c (u_stmt i)
  +
  ((MvPolynomial.x Vars.α) * (MvPolynomial.x Vars.δ)) * MvPolynomial.c (v_stmt i)
  +
  (MvPolynomial.x Vars.δ) * (MvPolynomial.c (w_stmt i))

def crs'_m (i : Finₓ n_wit) : MvPolynomial Vars (Polynomial F) := 
  ((MvPolynomial.x Vars.β) * (MvPolynomial.x Vars.γ)) * MvPolynomial.c (u_wit i)
  +
  ((MvPolynomial.x Vars.α) * (MvPolynomial.x Vars.γ)) * MvPolynomial.c (v_wit i)
  +
  (MvPolynomial.x Vars.γ) * MvPolynomial.c (w_wit i)


def crs'_t (i : Finₓ (n_var - 1)) : MvPolynomial Vars (Polynomial F) := 
  (MvPolynomial.x Vars.γ) *(MvPolynomial.c (((MvPolynomial.x)^(i : ℕ)) * t))

/- Polynomial form of A in the adversary's proof representation -/
def A'  : MvPolynomial Vars (Polynomial F) := 
  crs'_α * (MvPolynomial.c (Polynomial.c A_α))
  + -- TODO
  crs'_β * MvPolynomial.c (Polynomial.c A_β)
  + 
  crs'_γ * MvPolynomial.c (Polynomial.c A_γ)
  +
  crs'_δ * MvPolynomial.c (Polynomial.c A_δ)
  +
  (MvPolynomial.x Vars.γ) * (MvPolynomial.x Vars.δ) * MvPolynomial.c (∑ i in (finRange n_var), (Polynomial.c  (A_x i) * Polynomial.x ^ (i : ℕ)))
  +
  ∑ i in (finRange n_stmt), (crs'_l i) * MvPolynomial.c (Polynomial.c (A_l i))
  +
  ∑ i in (finRange n_wit), (crs'_m i) * MvPolynomial.c (Polynomial.c (A_m i))
  +
  ∑ i in (finRange (n_var - 1)), (crs'_t i) * MvPolynomial.c (Polynomial.c (A_h i))

/- Polynomial form of B in the adversary's proof representation -/
def B'  : MvPolynomial Vars (Polynomial F) := 
  crs'_α * MvPolynomial.c (c (B_α))
  +
  crs'_β * MvPolynomial.c (c (B_β))
  + 
  crs'_γ * MvPolynomial.c (c (B_γ))
  +
  crs'_δ * MvPolynomial.c (c (B_δ))
  +
  (Polynomial.x Vars.γ) * (Polynomial.x Vars.δ) * MvPolynomial.c (∑ i in (finRange n_var), (Polynomial.c (B_x i) * Polynomial.x ^ (i : ℕ)))
  +
  ∑ i in (finRange n_stmt), (crs'_l i) * MvPolynomial.c (Polynomial.c (B_l i))
  +
  ∑ i in (finRange n_wit), (crs'_m i) * MvPolynomial.c (Polynomial.c (B_m i))
  +
  ∑ i in (finRange (n_var - 1)), (crs'_t i) * MvPolynomial.c (Polynomial.c (B_h i))

/- Polynomial form of C in the adversary's proof representation -/
def C'  : MvPolynomial Vars (Polynomial F) := 
  crs'_α * MvPolynomial.c (Polynomial.c (C_α))
  + -- TODO
  crs'_β * MvPolynomial.c (Polynomial.c (C_β))
  + 
  crs'_γ * MvPolynomial.c (Polynomial.c (C_γ))
  +
  crs'_δ * MvPolynomial.c (Polynomial.c (C_δ))
  +
  (MvPolynomial.x Vars.γ) * (MvPolynomial.x Vars.δ) * MvPolynomial.c (∑ i in (finRange n_var), (Polynomial.c (C_x i) * Polynomial.x ^ (i : ℕ)))
  +
  ∑ i in (finRange n_stmt), (crs'_l i) * MvPolynomial.c (Polynomial.c (C_l i))
  +
  ∑ i in (finRange n_wit), (crs'_m i) * MvPolynomial.c (Polynomial.c (C_m i))
  +
  ∑ i in (finRange (n_var - 1)), (crs'_t i) * MvPolynomial.c (Polynomial.c (C_h i))


def  verified (a_stmt : Finₓ n_stmt → F ) : Prop := 
  A * B = crs_α * crs_β + ((∑ i in finRange n_stmt, a_stmt i * crs_l i ) * crs_γ + C * crs_δ : F)

def verified' (a_stmt : Finₓ n_stmt → F ) : Prop := 
  A' * B' = crs'_α * crs'_β + ((∑ i in finRange n_stmt, (c (a_stmt i)) * crs'_l i ) * crs'_γ + C' * crs'_δ : F)

lemma modification_equivalence (a_stmt : Finₓ n_stmt → F) : 
  verified a_stmt -> verified' a_stmt := by sorry

open Finsupp

lemma coeff0023 (a_stmt : Finₓ n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (i : Finₓ n_var) in finRange n_var, (c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
        c B_γ + (c A_γ) *
        (∑ (i : Finₓ n_var) in finRange n_var, (c (B_x i)) * x ^ (i : Nat)) =
    0 := by sorry

lemma coeff0013 (a_stmt : Finₓ n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * (c (A_m x))) * (c B_γ) +
          (∑ (x : Finₓ (n_var - 1)) in
               finRange (n_var - 1),
               ((Polynomial.x)^(x : ℕ)) * (t * c (A_h x))) *
            c B_γ + (c A_γ) * (∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * (c (B_m x))) +
      (c A_γ) * (∑ (x : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (x : ℕ)) * (t * c (B_h x))) = 
    0 := by sorry

lemma coeff0012 (a_stmt : Finₓ n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * (c (A_m x))) *
            (∑ (i : Finₓ n_var) in finRange n_var, (c (B_x i)) * (Polynomial.x ^ (i : ℕ))) +
          (∑ (x : Finₓ (n_var - 1)) in finRange (n_var - 1), Polynomial.x ^ (x : ℕ) * (t * Polynomial.c (A_h x))) *
            ∑ (i : Finₓ n_var) in finRange n_var, (c (B_x i)) * (Polynomial.x ^ (i : ℕ)) +
        (∑ (i : Finₓ n_var) in finRange n_var, (c (A_x i)) * (Polynomial.x ^ (i : ℕ))) *
          ∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * (Polynomial.x (B_m x)) +
      (∑ (i : Finₓ n_var) in finRange n_var, (c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
        ∑ (x : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (x : ℕ)) * (t * Polynomial.c (B_h x)) =
    0 := by sorry

lemma coeff0002 (a_stmt : Finₓ n_stmt → F) (eqn : verified' a_stmt) :
  ((∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * Polynomial.c (A_m x)) *
          ∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * Polynomial.c (B_m x) +
        (∑ (x : Finₓ (n_var - 1)) in
             finRange (n_var - 1),
             (Polynomial.x ^ (x : ℕ)) * (t * Polynomial.c (A_h x))) *
          ∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * Polynomial.c (B_m x) +
      ((∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * Polynomial.c (A_m x)) *
           ∑ (x : Finₓ (n_var - 1)) in
             finRange (n_var - 1),
             (Polynomial.x ^ (x : ℕ)) * (t * Polynomial.c (B_h x)) +
         (∑ (x : Finₓ (n_var - 1)) in
              finRange (n_var - 1),
              (Polynomial.x ^ (x : ℕ)) * (t * Polynomial.c (A_h x))) *
           ∑ (x : Finₓ (n_var - 1)) in
             finRange (n_var - 1),
             (Polynomial.x ^ (x : ℕ)) * (t * Polynomial.c (B_h x)))) = 0 := by sorry

lemma coeff0011 (a_stmt : Finₓ n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * (Polynomial.c (A_m x))) *
            ∑ (x : Finₓ n_stmt) in finRange n_stmt, (w_stmt x) * Polynomial.c (B_l x) +
          (∑ (x : Finₓ (n_var - 1)) in
               finRange (n_var - 1),
               (Polynomial.x ^ (x : ℕ)) * (t * Polynomial.c (A_h x))) *
            ∑ (x : Finₓ n_stmt) in finRange n_stmt, (w_stmt x) * Polynomial.c (B_l x) +
        (∑ (x : Finₓ n_stmt) in finRange n_stmt, (w_stmt x) * Polynomial.c (A_l x)) *
          ∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * Polynomial.c (B_m x) +
      (∑ (x : Finₓ n_stmt) in finRange n_stmt, (w_stmt x) * Polynomial.c (A_l x)) *
        ∑ (x : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (x : ℕ)) * (t * Polynomial.c (B_h x)) =
    0 := by sorry

lemma coeff0020 (a_stmt : Finₓ n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : Finₓ n_stmt) in finRange n_stmt, w_stmt x * Polynomial.c (A_l x) = 0) ∨
    (∑ (x : Finₓ n_stmt) in finRange n_stmt, w_stmt x * Polynomial.c (B_l x) = 0) :=
  by sorry

lemma coeff0021 (a_stmt : Finₓ n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : Finₓ n_stmt) in finRange n_stmt, (w_stmt x) * Polynomial.c (A_l x)) *
        ∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * Polynomial.x ^ (i : ℕ) +
      (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
        ∑ (x : Finₓ n_stmt) in finRange n_stmt, (w_stmt x) * Polynomial.c (B_l x) =
    0 := by sorry

lemma coeff0022 (a_stmt : Finₓ n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : Finₓ n_stmt) in finRange n_stmt, (w_stmt x) * Polynomial.c (A_l x)) * Polynomial.c B_γ +
              ((∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * Polynomial.c (A_m x)) *
                   Polynomial.c B_δ +
                 (∑ (x : Finₓ (n_var - 1)) in
                      finRange (n_var - 1),
                      (Polynomial.x ^ (x : ℕ)) * (t * Polynomial.c (A_h x))) *
                   Polynomial.c B_δ) +
            (∑ (i : Finₓ n_var) in finRange n_var, Polynomial.c (A_x i) * Polynomial.x ^ (i : ℕ)) *
              (∑ (i : Finₓ n_var) in finRange n_var, Polynomial.c (B_x i) * Polynomial.x ^ (i : ℕ)) +
          (Polynomial.c A_γ) * (∑ (x : Finₓ n_stmt) in finRange n_stmt, (w_stmt x) * Polynomial.c (B_l x)) +
        (Polynomial.c A_δ) * (∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * Polynomial.c (B_m x)) +
      (Polynomial.c A_δ) * (∑ (x : Finₓ (n_var - 1)) in finRange (n_var - 1), Polynomial.x ^ (x : ℕ) * (t * Polynomial.c (B_h x))) =
    ∑ (x : Finₓ n_stmt) in finRange n_stmt, Polynomial.c (a_stmt x) * (w_stmt x) +
      (∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * Polynomial.c (C_m x) +
         ∑ (x : Finₓ (n_var - 1)) in finRange (n_var - 1), Polynomial.x ^ (x : ℕ) * (t * Polynomial.c (C_h x))) := by sorry

lemma coeff0024 (a_stmt : Finₓ n_stmt → F) (eqn : verified' a_stmt) :
 Polynomial.c A_γ = 0 ∨ Polynomial.c B_γ = 0 := by sorry

lemma coeff0111 (a_stmt : Finₓ n_stmt → F) (eqn : verified' a_stmt) : Prop
  (∑ (x : Finₓ n_wit) in finRange n_wit, w_wit x * Polynomial.c (A_m x)) *
              (∑ (x : Finₓ n_stmt) in finRange n_stmt, (u_stmt x) * Polynomial.c (B_l x) +
            (∑ (x : Finₓ (n_var - 1)) in
                 finRange (n_var - 1),
                 (Polynomial.x ^ (x : ℕ)) * (t * Polynomial.c (A_h x))) *
              ∑ (x : Finₓ n_stmt) in finRange n_stmt, (u_stmt x) * Polynomial.c (B_l x) +
          (∑ (x : Finₓ n_wit) in finRange n_wit, (u_wit x) * Polynomial.c (A_m x)) *
            ∑ (x : Finₓ n_stmt) in finRange n_stmt, (w_stmt x) * Polynomial.c (B_l x) +
        ((∑ (x : Finₓ n_stmt) in finRange n_stmt, (w_stmt x) * Polynomial.c (A_l x)) *
             ∑ (x : Finₓ n_wit) in finRange n_wit, (u_wit x) * Polynomial.c (B_m x) +
           (∑ (x : Finₓ n_stmt) in finRange n_stmt, (u_stmt x) * Polynomial.c (A_l x)) *
             ∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * Polynomial.c (B_m x)) +
      (∑ (x : Finₓ n_stmt) in finRange n_stmt, (u_stmt x) * Polynomial.c (A_l x)) *
        ∑ (x : Finₓ (n_var - 1)) in finRange (n_var - 1), Polynomial.x ^ (x : ℕ) * (t * Polynomial.c (B_h x)) = 0 := by sorry

lemma coeff0033 (a_stmt :  Finₓ n_stmt → F) (eqn : verified' a_stmt) :
  (c A_δ) * c B_γ + (c A_γ) * c B_δ = c C_γ := by sorry

lemma coeff0102 (a_stmt : Finₓ n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit) x * c (A_m x)) *
            ∑ (x : Finₓ n_wit) in finRange n_wit, (u_wit x) * c (B_m x) +
          (∑ (x : Finₓ (n_var - 1)) in
               finRange (n_var - 1),
               Polynomial.x ^ (x : nat) * (t * c (A_h x))) *
            ∑ (x : Finₓ n_wit) in finRange n_wit, (u_wit x) * c (B_m x) +
        (∑ (x : Finₓ n_wit) in finRange n_wit, (u_wit x) * c (A_m x)) *
          ∑ (x : Finₓ n_wit) in finRange n_wit, (w_wit x) * c (B_m x) +
      (∑ (x : Finₓ n_wit) in finRange n_wit, (u_wit x) * c (A_m x)) *
        ∑ (x : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (x : ℕ)) * (t * c (B_h x)) =
    0 := by sorry



end Groth16