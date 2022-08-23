import Mathbin

import ZkSNARK.GeneralLemmas.MvDivisibility
import ZkSNARK.Groth16.Vars

noncomputable section

namespace Groth16
open Finset Polynomial BigOperators

/- The finite field parameter of our SNARK -/
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
def t : F[X] := ∏ i in finRange n_wit, (x : F[X]) - Polynomial.c (r i)


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
def V_wit_sv (a_wit : Finₓ n_wit → F) :  F[X] := 
  ∑ i in finRange n_wit, a_wit i • u_wit i

/- The statement polynomial that the verifier computes from the statement bits, 
as a single variable polynomial -/
def V_stmt_sv (a_stmt : Finₓ n_stmt → F) : F[X] := 
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

/- The CRS elements 
These funtions are actually multivariate Laurent polynomials of the toxic waste samples, 
but we represent them here as functions on assignments of the variables to values.
-/
variable (F)
def crs_α  (f : Vars → F) : F := f Vars.α

def crs_β (f : Vars → F) : F := f Vars.β

def crs_γ (f : Vars → F) : F := f Vars.γ

def crs_δ (f : Vars → F) : F := f Vars.δ

def crs_powers_of_x (i : Finₓ n_var) (a : F) : F := (a)^(i : ℕ)

def crs_l (i : Finₓ n_stmt) (f : Vars → F) (a : F) : F := 
  ((f Vars.β / f Vars.γ) * (u_stmt i).eval (a)
  +
  (f Vars.α / f Vars.γ) * (v_stmt i).eval (a)
  +
  (w_stmt i).eval (a)) / f Vars.γ

def crs_m (i : Finₓ n_wit) (f : Vars → F) (a : F) : F := 
  ((f Vars.β / f Vars.δ) * (u_wit i).eval (a)
  +
  (f Vars.α / f Vars.δ) * (v_wit i).eval (a)
  +
  (w_wit i).eval (a)) / f Vars.δ

def crs_n (i : Finₓ (n_var - 1)) (f : Vars → F) (a : F) : F := 
  ((a)^(i : ℕ)) * (t r).eval a / f Vars.δ

variable {F}
variable { A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ  : F }
variable { A_x B_x C_x : Finₓ n_var → F }
variable { A_l B_l C_l : Finₓ n_stmt → F }
variable { A_m B_m C_m : Finₓ n_wit → F }
variable { A_h B_h C_h : Finₓ (n_var - 1) → F }

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
We will later prove that the Laurent polynomial equation is equivalent to a 
similar equation of the modified crs elements, allowing us to construct 
a proof in terms of polynomials -/
def crs'_α  : MvPolynomial Vars F[X] := 
  let pol₁ := (MvPolynomial.x Vars.α : MvPolynomial Vars F[X])
  let pol₂ := (MvPolynomial.x Vars.γ : MvPolynomial Vars F[X])
  let pol₃ := (MvPolynomial.x Vars.δ : MvPolynomial Vars F[X])
  (pol₁ * pol₂) * pol₃

def crs'_β : MvPolynomial Vars F[X] := 
  let pol₁ := (MvPolynomial.x Vars.β : MvPolynomial Vars F[X])
  let pol₂ := (MvPolynomial.x Vars.γ : MvPolynomial Vars F[X])
  let pol₃ := (MvPolynomial.x Vars.δ : MvPolynomial Vars F[X])
  (pol₁ * pol₂) * pol₃

def crs'_γ : MvPolynomial Vars F[X] :=
  let pol₁ := (MvPolynomial.x Vars.γ : MvPolynomial Vars F[X])
  let pol₂ := (MvPolynomial.x Vars.γ : MvPolynomial Vars F[X])
  let pol₃ := (MvPolynomial.x Vars.δ : MvPolynomial Vars F[X])
  (pol₁ * pol₂) * pol₃

def crs'_δ : MvPolynomial Vars F[X] :=
  let pol₁ := (MvPolynomial.x Vars.δ : MvPolynomial Vars F[X])
  let pol₂ := (MvPolynomial.x Vars.γ : MvPolynomial Vars F[X])
  let pol₃ := (MvPolynomial.x Vars.δ : MvPolynomial Vars F[X])
  (pol₁ * pol₂) * pol₃

def crs'_powers_of_x (i : Finₓ n_var) : MvPolynomial Vars F[X] := 
  let pol₁ := (MvPolynomial.c ((Polynomial.x)^(i : ℕ)) : MvPolynomial Vars F[X])
  let pol₂ := (MvPolynomial.x Vars.γ : MvPolynomial Vars F[X])
  let pol₃ := (MvPolynomial.x Vars.δ : MvPolynomial Vars F[X])
  (pol₁ * pol₂) * pol₃
-- We define prodcuts of these crs elements without the division, then later claim identities. Is this right?

def crs'_l (i : Finₓ n_stmt) : MvPolynomial Vars F[X] :=
  let pol₁ := (MvPolynomial.x Vars.α : MvPolynomial Vars F[X])
  let pol₂ := (MvPolynomial.x Vars.β : MvPolynomial Vars F[X])
  let pol₃ := (MvPolynomial.x Vars.δ : MvPolynomial Vars F[X])
  let pol₄ := (MvPolynomial.c (u_stmt i) : MvPolynomial Vars F[X])
  let pol₅ := (MvPolynomial.c (v_stmt i) : MvPolynomial Vars F[X])
  let pol₆ := (MvPolynomial.c (w_stmt i) : MvPolynomial Vars F[X])
  (pol₂ * pol₃) * pol₄
  +
  (pol₁  * pol₃) * pol₅
  +
  pol₃ * pol₆

def crs'_m (i : Finₓ n_wit) : MvPolynomial Vars F[X] :=
  let pol₁ := (MvPolynomial.x Vars.α : MvPolynomial Vars F[X])
  let pol₂ := (MvPolynomial.x Vars.β : MvPolynomial Vars F[X])
  let pol₃ := (MvPolynomial.x Vars.γ : MvPolynomial Vars F[X])
  let pol₄ := (MvPolynomial.c (u_wit i) : MvPolynomial Vars F[X])
  let pol₅ := (MvPolynomial.c (v_wit i) : MvPolynomial Vars F[X])
  let pol₆ := (MvPolynomial.c (w_wit i) : MvPolynomial Vars F[X])
  (pol₂ * pol₃) * pol₄
  +
  (pol₁ * pol₃) * pol₅
  +
  pol₃ * pol₆


def crs'_t (i : Finₓ (n_var - 1)) : MvPolynomial Vars F[X] :=
  let pol₁ := (MvPolynomial.x Vars.γ : MvPolynomial Vars F[X])
  let pol₂ := ((((Polynomial.x)^(i : ℕ)) * (t r)) : F[X])
  let pol₃ := (MvPolynomial.c pol₂ : MvPolynomial Vars F[X])
  pol₁ * pol₃

/- Polynomial form of A in the adversary's proof representation -/
def A'  : MvPolynomial Vars F[X] :=
  let pol_c := (Polynomial.c A_α : F[X])
  let pol₁ := (MvPolynomial.c pol_c : MvPolynomial Vars F[X])
  let pol₂ := (@crs'_α F field : MvPolynomial Vars F[X])
  let pol_γ := (MvPolynomial.x Vars.γ : MvPolynomial Vars F[X])
  let pol_aβ := (MvPolynomial.c (Polynomial.c A_β) : MvPolynomial Vars F[X])
  let pol_aγ := (MvPolynomial.c (Polynomial.c A_γ) : MvPolynomial Vars F[X])
  let pol_aδ := (MvPolynomial.c (Polynomial.c A_δ) : MvPolynomial Vars F[X])
  let pol_δ := (MvPolynomial.x Vars.δ : MvPolynomial Vars F[X])
  let sum_ax := (∑ i in (finRange n_var), ((Polynomial.c (A_x i)) * (Polynomial.x ^ (i : ℕ))) : F[X])
  let sum₁ := (MvPolynomial.c sum_ax : MvPolynomial Vars F[X])
  let sum₂ := (∑ i in (finRange n_stmt), 
    let pol₁ := (@crs'_l F field n_stmt u_stmt v_stmt w_stmt i : MvPolynomial Vars F[X])
    let pol₂ := (MvPolynomial.c (Polynomial.c (A_l i)) : MvPolynomial Vars F[X])
    pol₁ * pol₂ : MvPolynomial Vars F[X])
  let sum₃ := (∑ i in (finRange n_wit),
    let pol_am := (MvPolynomial.c (Polynomial.c (A_m i)) : MvPolynomial Vars F[X])
    let pol₁ := @crs'_m F field n_wit u_wit v_wit w_wit i
    pol₁ * pol_am : MvPolynomial Vars F[X])
  let sum₄ := ∑ i in (finRange (n_var - 1)),
    let pol₁ := (@crs'_t F field n_wit n_var r i : MvPolynomial Vars F[X])
    let pol_ah := (MvPolynomial.c (Polynomial.c (A_h i)) : MvPolynomial Vars F[X])
    pol₁ * pol_ah
  (pol₁ * pol₂)
  + -- TODO
  (@crs'_β F field) * pol_aβ
  + 
  (@crs'_γ F field) * pol_aγ
  +
  (@crs'_δ F field) * pol_aδ
  +
  (pol_γ * pol_δ) * sum₁
  +
  sum₂
  +
  sum₃
  +
  sum₄

/- Polynomial form of B in the adversary's proof representation -/
def B'  : MvPolynomial Vars F[X] :=
  let pol₁ := (MvPolynomial.c (Polynomial.c B_α) : MvPolynomial Vars F[X])
  let pol_γ := (MvPolynomial.x Vars.γ : MvPolynomial Vars F[X])
  let pol_δ := (MvPolynomial.x Vars.δ : MvPolynomial Vars F[X])
  let sum_bx := (∑ i in (finRange n_var), ((Polynomial.c (B_x i)) * (Polynomial.x ^ (i : ℕ))) : F[X])
  let sum₁ := (MvPolynomial.c sum_bx : MvPolynomial Vars F[X])
  let sum₂ := (∑ i in (finRange n_stmt),
    let pol_bl := (MvPolynomial.c (Polynomial.c (B_l i)) : MvPolynomial Vars F[X])
    let pol₁ := @crs'_l F field n_stmt u_stmt v_stmt w_stmt i
    pol₁ * pol_bl : MvPolynomial Vars F[X])
  let sum₃ := (∑ i in (finRange n_wit),
    let pol_bm := (MvPolynomial.c (Polynomial.c (B_m i)) : MvPolynomial Vars F[X])
    (@crs'_m F field n_wit u_wit v_wit w_wit i) * pol_bm : MvPolynomial Vars F[X])
  let sum₄ := (∑ i in (finRange (n_var - 1)),
    let pol_bh := (MvPolynomial.c (Polynomial.c (B_h i)) : MvPolynomial Vars F[X])
    (@crs'_t F field n_wit n_var r i) * pol_bh : MvPolynomial Vars F[X])
  (@crs'_α F field) * pol₁
  +
  (@crs'_β F field) * (MvPolynomial.c (Polynomial.c B_β) : MvPolynomial Vars F[X])
  + 
  (@crs'_γ F field) * (MvPolynomial.c (Polynomial.c B_γ) : MvPolynomial Vars F[X])
  +
  (@crs'_δ F field) * (MvPolynomial.c (Polynomial.c B_δ) : MvPolynomial Vars F[X])
  +
  (pol_γ * pol_δ) * sum₁
  +
  sum₂
  +
  sum₃
  +
  sum₄

/- Polynomial form of C in the adversary's proof representation -/
def C'  : MvPolynomial Vars F[X] :=
  let pol_α := (MvPolynomial.c (Polynomial.c C_α) : MvPolynomial Vars F[X])
  let pol_β := (MvPolynomial.c (Polynomial.c C_β) : MvPolynomial Vars F[X])
  let pol_γ := (MvPolynomial.c (Polynomial.c C_γ) : MvPolynomial Vars F[X])
  let pol_δ := (MvPolynomial.c (Polynomial.c C_δ) : MvPolynomial Vars F[X])
  let pol₁ := (MvPolynomial.x Vars.γ : MvPolynomial Vars F[X])
  let pol₂ := (MvPolynomial.x Vars.δ : MvPolynomial Vars F[X])
  let sum_cx := (∑ i in (finRange n_var), ((Polynomial.c (C_x i)) * Polynomial.x ^ (i : ℕ)) : F[X])
  let sum₁ := (MvPolynomial.c sum_cx : MvPolynomial Vars F[X])
  let sum₂ :=
    (∑ i in (finRange n_stmt),
    let pol_cl := (MvPolynomial.c (Polynomial.c (C_l i)) : MvPolynomial Vars F[X])
    (@crs'_l F field n_stmt u_stmt v_stmt w_stmt i) * pol_cl : MvPolynomial Vars F[X])
  let sum₃ := (∑ i in (finRange n_wit),
    let pol_cm := (MvPolynomial.c (Polynomial.c (C_m i)) : MvPolynomial Vars F[X])
    let pol₁ := @crs'_m F field n_wit u_wit v_wit w_wit i
    pol₁ * pol_cm : MvPolynomial Vars F[X])
  let sum₄ := (∑ i in (finRange (n_var - 1)),
    let pol_ch := (MvPolynomial.c (Polynomial.c (C_h i)) : MvPolynomial Vars F[X])
    (@crs'_t F field n_wit n_var r i) * pol_ch : MvPolynomial Vars F[X])
  (@crs'_α F field) * pol_α
  + -- TODO
  (@crs'_β F field) * pol_β
  + 
  (@crs'_γ F field) * pol_γ
  +
  (@crs'_δ F field) * pol_δ
  +
  (pol₁ * pol₂) * sum₁
  +
  sum₂
  +
  sum₃
  +
  sum₄

def verified (f : Vars → F) (x : F) (a_stmt : Finₓ n_stmt → F ) : Prop :=
  let A_inst := 
    @A F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ A_x A_l A_m A_h f x
  let B_inst :=
    @B F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r B_α B_β B_γ B_δ B_x B_l B_m B_h f x
  let C_inst :=
    @C F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r C_α C_β C_γ C_δ C_x C_l C_m C_h f x
  let crs_α_inst := @crs_α F f
  let crs_β_inst := @crs_β F f
  A_inst * B_inst = 
    (crs_α_inst * crs_β_inst) + 
    ((∑ i in finRange n_stmt, (a_stmt i) * 
      @crs_l F field n_stmt u_stmt v_stmt w_stmt i f x) * (crs_γ F f) + C_inst * (crs_δ F f))

def verified' (a_stmt : Finₓ n_stmt → F) : Prop :=
  let A'_inst :=
    @A' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ A_x A_l A_m A_h
  let B'_inst :=
    @B' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r B_α B_β B_γ B_δ B_x B_l B_m B_h
  let C'_inst :=
    @C' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r C_α C_β C_γ C_δ C_x C_l C_m C_h
  let crs'_α_inst := (@crs'_α F field : MvPolynomial Vars F[X])
  let crs'_β_inst := (@crs'_β F field : MvPolynomial Vars F[X])
  A'_inst * B'_inst = (crs'_α_inst * crs'_β_inst) + 
    ((∑ i in finRange n_stmt, 
    let pol_astmt := (MvPolynomial.c (Polynomial.c (a_stmt i)) : MvPolynomial Vars F[X])
    pol_astmt * (@crs'_l F field n_stmt u_stmt v_stmt w_stmt i) ) * (@crs'_γ F field) + C'_inst * (@crs'_δ F field))

lemma modification_equivalence (f : Vars → F) (x : F) (a_stmt : Finₓ n_stmt → F) :
  let verified_inst :=
    @verified F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h f x a_stmt
  let verified'_inst :=
    @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt
  verified_inst → verified'_inst := by sorry

open Finsupp

lemma coeff0023 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
        Polynomial.c B_γ + (Polynomial.c A_γ) *
        (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * x ^ (i : Nat)) =
    0 := by sorry

lemma coeff0013 (a_stmt : Finₓ n_stmt → F)
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * (Polynomial.c (A_m i))) * (Polynomial.c B_γ) +
          (∑ (i : Finₓ (n_var - 1)) in
               finRange (n_var - 1),
               ((Polynomial.x)^(i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
            Polynomial.c B_γ + (Polynomial.c A_γ) * (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * (Polynomial.c (B_m i))) +
      (Polynomial.c A_γ) * (∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i))) = 
    0 := by sorry

lemma coeff0012 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * (Polynomial.c (A_m i))) *
            (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * (Polynomial.x ^ (i : ℕ))) +
          (∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
            ∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * (Polynomial.x ^ (i : ℕ)) +
        (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * (Polynomial.x ^ (i : ℕ))) *
          (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * (Polynomial.c (B_m i))) +
      (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
        ∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i))) =
    0 := by sorry

lemma coeff0002 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (A_m i)) *
          ∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i) +
        (∑ (i : Finₓ (n_var - 1)) in
             finRange (n_var - 1),
             (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
          ∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i) +
      ((∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (A_m i)) *
           ∑ (i : Finₓ (n_var - 1)) in
             finRange (n_var - 1),
             (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i)) +
         (∑ (i : Finₓ (n_var - 1)) in
              finRange (n_var - 1),
              (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
           ∑ (i : Finₓ (n_var - 1)) in
             finRange (n_var - 1),
             (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i)))) = 0 := by sorry

lemma coeff0011 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * (Polynomial.c (A_m i))) *
            ∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i) +
          (∑ (i : Finₓ (n_var - 1)) in
               finRange (n_var - 1),
               (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
            ∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i) +
        (∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)) *
          ∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i) +
      (∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)) *
        ∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i))) =
    0 := by sorry

lemma coeff0020 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)) = 0) ∨
    ((∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i)) = 0) :=
  by sorry

lemma coeff0021 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)) *
        ∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * Polynomial.x ^ (i : ℕ) +
      (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
        ∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i)) = 0 := by sorry

lemma coeff0022 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)) * Polynomial.c B_γ +
              ((∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (A_m i)) *
                   Polynomial.c B_δ +
                 (∑ (i : Finₓ (n_var - 1)) in
                      finRange (n_var - 1),
                      (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
                   Polynomial.c B_δ) +
            (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
              (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * Polynomial.x ^ (i : ℕ)) +
          (Polynomial.c A_γ) * (∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i)) +
        (Polynomial.c A_δ) * (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i)) +
      (Polynomial.c A_δ) * (∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i))) =
    ∑ (i : Finₓ n_stmt) in finRange n_stmt, (Polynomial.c (a_stmt i)) * (w_stmt i) +
      (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (C_m i) +
         ∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (C_h i))) := by sorry

lemma coeff0024 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
 Polynomial.c A_γ = 0 ∨ Polynomial.c B_γ = 0 := by sorry

lemma coeff0111 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (A_m i)) *
              ∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (B_l i) +
            (∑ (i : Finₓ (n_var - 1)) in
                 finRange (n_var - 1),
                 (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
              ∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (B_l i) +
          (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)) *
            ∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i) +
        ((∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)) *
             ∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i) +
           (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (A_l i)) *
             ∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i)) +
      (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (A_l i)) *
        ∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i))) =
    0 := by sorry

lemma coeff0033 (a_stmt :  Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (Polynomial.c A_δ) * Polynomial.c B_γ + (Polynomial.c A_γ) * Polynomial.c B_δ = Polynomial.c C_γ := by sorry

lemma coeff0102 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * (Polynomial.c (A_m i))) *
            ∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i) +
          (∑ (i : Finₓ (n_var - 1)) in
               finRange (n_var - 1),
               (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
            ∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i) +
        (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)) *
          ∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i) +
      (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)) *
        ∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i))) =
    0 := by sorry

lemma coeff0042 (a_stmt : Finₓ n_stmt → F)
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
 (Polynomial.c A_δ) * Polynomial.c B_δ = Polynomial.c C_δ := by sorry

lemma coeff0112 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (A_m i)) * Polynomial.c B_β +
            (∑ (i : Finₓ (n_var - 1)) in
                 finRange (n_var - 1),
                 (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
              Polynomial.c B_β +
          (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)) *
            (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * Polynomial.x ^ (i : ℕ)) +
        ((∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
             ∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i) +
           (Polynomial.c A_β) * (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i))) +
      (Polynomial.c A_β) *
        (∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i))) =
    0 := by sorry

lemma coeff0031 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)) * Polynomial.c B_δ +
      (Polynomial.c A_δ) * (∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i)) =
    ∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (C_l i) := by sorry


lemma coeff0032 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
        Polynomial.c B_δ +
      (Polynomial.c A_δ) *
        (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * Polynomial.x ^ (i : ℕ)) =
    ∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (C_x i)) * Polynomial.x ^ (i : ℕ) := by sorry

lemma coeff0113 (a_stmt : Finₓ n_stmt → F)
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)) * Polynomial.c B_γ +
      (Polynomial.c A_γ) * (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i)) =
    0 := by sorry

lemma coeff0120 (a_stmt :  Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)) *
        ∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (B_l i) +
      (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (A_l i)) *
        ∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i)) =
    0 := by sorry

lemma coeff0123 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (Polynomial.c A_γ) * Polynomial.c B_β + (Polynomial.c A_β) * Polynomial.c B_γ = 0 := by sorry

lemma coeff0121 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)) * Polynomial.c B_β +
        (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (A_l i)) *
          (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * Polynomial.x ^ (i : ℕ)) +
      ((∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
           ∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (B_l i) +
         (Polynomial.c A_β) * (∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i))) =
    0 := by sorry

lemma coeff0132 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (Polynomial.c A_δ) * Polynomial.c B_β + (Polynomial.c A_β) * Polynomial.c B_δ = Polynomial.c C_β := by sorry

lemma coeff0131 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (A_l i)) * Polynomial.c B_δ +
      (Polynomial.c A_δ) * (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (B_l i)) =
    ∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (C_l i) := by sorry

lemma coeff0122 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
                Polynomial.c B_β +
              (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (A_l i)) *
                Polynomial.c B_γ +
            (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)) * Polynomial.c B_δ +
          (Polynomial.c A_β) *
            (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * (Polynomial.x ^ (i : ℕ))) +
        (Polynomial.c A_γ) * (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (B_l i)) +
      (Polynomial.c A_δ) * (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i)) =
    (∑ (i : Finₓ n_stmt) in finRange n_stmt, (Polynomial.c (a_stmt i)) * (u_stmt i)) +
      (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (C_m i)) := by sorry

lemma coeff0202 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)) = 0) ∨
    ((∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i)) = 0) := by sorry

lemma coeff0212 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)) * Polynomial.c B_β +
      (Polynomial.c A_β) * (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i)) =
    0 := by sorry

lemma coeff0211 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)) *
        ∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (B_l i) +
      (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (A_l i)) *
        ∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i)) =
    0 := by sorry

lemma coeff0220 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (A_l i)) = 0 ∨
    (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (B_l i)) = 0 := by sorry

lemma coeff0221 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (A_l i)) * Polynomial.c B_β) +
      (Polynomial.c A_β) * (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (B_l i)) =
    0 := by sorry

lemma coeff0222 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (Polynomial.c A_β = 0) ∨ (Polynomial.c B_β) = 0 := by sorry

lemma coeff1002 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (A_m i)) *
            ∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i) +
          (∑ (i : Finₓ (n_var - 1)) in
               finRange (n_var - 1),
               (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
            ∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i) +
        (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)) *
          ∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i) +
      (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)) *
        ∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i))) =
    0 := by sorry

lemma coeff1011 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (A_m i)) *
              (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (B_l i)) +
            (∑ (i : Finₓ (n_var - 1)) in
                 finRange (n_var - 1),
                 (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
              ∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (B_l i) +
          (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)) *
            ∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i) +
        ((∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)) *
             ∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i) +
           (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (A_l i)) *
             ∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i)) +
      (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (A_l i)) *
        ∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i))) =
    0 := by sorry

lemma coeff1012 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (A_m i)) * Polynomial.c B_α +
            (∑ (i : Finₓ (n_var - 1)) in
                 finRange (n_var - 1),
                 (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
              Polynomial.c B_α +
          (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)) *
            (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * Polynomial.x ^ (i : ℕ)) +
        ((∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
             ∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i) +
           (Polynomial.c A_α) * (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i))) +
      (Polynomial.c A_α) *
        (∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i))) = 0 := by sorry

lemma coeff1013 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)) * Polynomial.c B_γ +
      (Polynomial.c A_γ) * (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i)) =
    0 := by sorry

lemma coeff1020 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)) *
        (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (B_l i)) +
      (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (A_l i)) *
        ∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i)) =
    0 := by sorry

lemma coeff1021 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)) * Polynomial.c B_α +
        (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (A_l i)) *
          (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * Polynomial.x ^ (i : ℕ)) +
      ((∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
           (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (B_l i)) +
         (Polynomial.c A_α) * (∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i))) =
    0 := by sorry

lemma coeff1023 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (Polynomial.c A_γ) * Polynomial.c B_α + (Polynomial.c A_α) * Polynomial.c B_γ = 0 := by sorry

lemma coeff1022 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
                Polynomial.c B_α +
              (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (A_l i)) *
                Polynomial.c B_γ +
            (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)) * Polynomial.c B_δ +
          (Polynomial.c A_α) *
            (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * Polynomial.x ^ (i : ℕ)) +
        (Polynomial.c A_γ) * (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (B_l i)) +
      (Polynomial.c A_δ) * (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i)) =
    (∑ (i : Finₓ n_stmt) in finRange n_stmt, (Polynomial.c (a_stmt i)) * (v_stmt i)) +
      (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (C_m i)) := by sorry

lemma coeff1031 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (A_l i)) * Polynomial.c B_δ +
      (Polynomial.c A_δ) * (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (B_l i)) =
    ∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (C_l i) := by sorry

lemma coeff1111 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)) *
          ∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (B_l i) +
        (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)) *
          ∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (B_l i) +
      ((∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (A_l i)) *
           ∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i) +
         (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (A_l i)) *
           ∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i))) =
    0 := by sorry

lemma coeff1102 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)) *
        ∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i) +
      (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)) *
        ∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i)) =
    0 := by sorry

lemma coeff1112 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)) * Polynomial.c B_α +
        (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)) * Polynomial.c B_β +
      ((Polynomial.c A_α) * (∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i)) +
         (Polynomial.c A_β) * (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i))) =
    0 := by sorry

lemma coeff1032 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (Polynomial.c A_δ) * Polynomial.c B_α + (Polynomial.c A_α) * Polynomial.c B_δ = Polynomial.c C_α := by sorry

lemma coeff1122 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (Polynomial.c A_β) * Polynomial.c B_α + (Polynomial.c A_α) * Polynomial.c B_β = 1 := by sorry

lemma coeff1120 (a_stmt : Finₓ n_stmt → F)
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (A_l i)) *
        ∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (B_l i) +
      (∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (A_l i)) *
        ∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (B_l i)) =
    0 := by sorry
  
lemma coeff2011 (a_stmt : Finₓ n_stmt → F)
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)) *
        ∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (B_l i) +
      (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (A_l i)) *
        ∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i)) =
    0 := by sorry

lemma coeff2002 (a_stmt : Finₓ n_stmt → F)
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)) = 0 ∨
    (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i)) = 0 := by sorry

lemma coeff2012 (a_stmt : Finₓ n_stmt → F)
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)) * Polynomial.c B_α +
      (Polynomial.c A_α) * (∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i)) =
    0 := by sorry

lemma coeff2020 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (A_l i)) = 0 ∨
    (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (B_l i)) = 0 := by sorry

lemma coeff2021 (a_stmt : Finₓ n_stmt → F)
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (A_l i)) * Polynomial.c B_α +
      (Polynomial.c A_α) * (∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (B_l i)) =
    0 := by sorry

lemma coeff2022 (a_stmt : Finₓ n_stmt → F) 
      (eqn : @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h a_stmt) :
  Polynomial.c A_α = 0 ∨ Polynomial.c B_α = 0 := by sorry


lemma coeff0022reformat (a_stmt : Finₓ n_stmt → F) :   
  ((∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (A_m i)) * Polynomial.c B_δ +
            (∑ (i : Finₓ (n_var - 1)) in
                 finRange (n_var - 1),
                 (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))) *
              Polynomial.c B_δ +
          (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
            ∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * Polynomial.x ^ (i : ℕ) +
        (Polynomial.c A_δ) * (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i)) +
      (Polynomial.c A_δ) *
        (∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i)))) =
    (∑ (i : Finₓ n_stmt) in finRange n_stmt, (Polynomial.c (a_stmt i)) * w_stmt i) +
      (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (C_m i) +
         ∑ (i : Finₓ (n_var - 1)) in
           finRange (n_var - 1),
           (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (C_h i)))
  ↔
  (((∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (A_m i)) +
            (∑ (i : Finₓ (n_var - 1)) in
                 finRange (n_var - 1),
                 (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))))  *
              Polynomial.c B_δ +
          (∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ)) *
            ∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.c (B_x i)) * Polynomial.x ^ (i : ℕ) +
        (Polynomial.c A_δ) * (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i) +
      ∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i)))) =
    ∑ (i : Finₓ n_stmt) in finRange n_stmt, (Polynomial.c (a_stmt i)) * w_stmt i +
      (∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (C_m i) +
         ∑ (i : Finₓ (n_var - 1)) in
           finRange (n_var - 1),
           (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (C_h i))) := by sorry

register_simp_attr atom "Attribute for defintions of atoms in the proof"

-- @[atom] 
def p_A_α := Polynomial.c A_α
-- @[atom]
def p_A_β := Polynomial.c A_β
-- @[atom]
def p_A_γ := Polynomial.c A_γ
-- @[atom]
def p_A_δ := Polynomial.c A_δ
-- @[atom]
def p_B_α := Polynomial.c B_α
-- @[atom]
def p_B_β := Polynomial.c B_β
-- @[atom]
def p_B_γ := Polynomial.c B_γ
-- @[atom]
def p_B_δ := Polynomial.c B_δ
-- @[atom]
def p_C_α := Polynomial.c C_α
-- @[atom]
def p_C_β := Polynomial.c C_β
-- @[atom]
def p_C_γ := Polynomial.c C_γ
-- @[atom]
def p_C_δ := Polynomial.c C_δ

-- @[atom]
def p_u_stmt_A_l := ∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (A_l i)
-- @[atom]
def p_v_stmt_A_l := ∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (A_l i)
-- @[atom]
def p_w_stmt_A_l := ∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (A_l i)
-- @[atom]
def p_u_stmt_B_l := ∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (B_l i)
-- @[atom]
def p_v_stmt_B_l := ∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (B_l i)
-- @[atom]
def p_w_stmt_B_l := ∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (B_l i)
-- @[atom]
def p_u_stmt_C_l := ∑ (i : Finₓ n_stmt) in finRange n_stmt, (u_stmt i) * Polynomial.c (C_l i)
-- @[atom]
def p_v_stmt_C_l := ∑ (i : Finₓ n_stmt) in finRange n_stmt, (v_stmt i) * Polynomial.c (C_l i)
-- @[atom]
def p_w_stmt_C_l := ∑ (i : Finₓ n_stmt) in finRange n_stmt, (w_stmt i) * Polynomial.c (C_l i)

-- @[atom]
def p_u_wit_A_m := ∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (A_m i)
-- @[atom]
def p_v_wit_A_m := ∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (A_m i)
-- @[atom]
def p_w_wit_A_m := ∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (A_m i)
-- @[atom]
def p_u_wit_B_m := ∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (B_m i)
-- @[atom]
def p_v_wit_B_m := ∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (B_m i)
-- @[atom]
def p_w_wit_B_m := ∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (B_m i)
-- @[atom]
def p_u_wit_C_m := ∑ (i : Finₓ n_wit) in finRange n_wit, (u_wit i) * Polynomial.c (C_m i)
-- @[atom]
def p_v_wit_C_m := ∑ (i : Finₓ n_wit) in finRange n_wit, (v_wit i) * Polynomial.c (C_m i)
-- @[atom]
def p_w_wit_C_m := ∑ (i : Finₓ n_wit) in finRange n_wit, (w_wit i) * Polynomial.c (C_m i)

-- @[atom]
def p_t_A_h := ∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (A_h i))
-- @[atom]
def p_t_B_h := ∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (B_h i))
-- @[atom]
def p_t_C_h := ∑ (i : Finₓ (n_var - 1)) in finRange (n_var - 1), (Polynomial.x ^ (i : ℕ)) * ((t r) * Polynomial.c (C_h i))

-- @[atom]
def p_A_x := ∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.x ^ (i : ℕ)) * Polynomial.c (A_x i)
-- @[atom]
def p_B_x := ∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.x ^ (i : ℕ)) * Polynomial.c (B_x i)
-- @[atom]
def p_C_x := ∑ (i : Finₓ n_var) in finRange n_var, (Polynomial.x ^ (i : ℕ)) * Polynomial.c (C_x i)

@[simp] lemma Polynomial.c_eq_one (a : F) : Polynomial.c a = 1 ↔ a = 1 := by sorry
-- calc polynomial.C a = 1 ↔ polynomial.C a = polynomial.C 1 : by rw polynomial.C_1
--         ... ↔ a = 1 : polynomial.C_inj

lemma simplifier1 (i : Finₓ n_stmt) (a_stmt : Finₓ n_stmt → F ) 
  : (Polynomial.c (a_stmt i)) * (u_stmt i) = (u_stmt i) * (Polynomial.c (a_stmt i))
  := sorry

lemma simplifier2 (i : Finₓ n_stmt) (a_stmt : Finₓ n_stmt → F ) 
  : (Polynomial.c (a_stmt i)) * v_stmt i = (v_stmt i) * Polynomial.c (a_stmt i)
  := sorry

lemma polynomial.mul_mod_by_monic (t p : F[X]) (mt : Polynomial.Monic t) : 
  let prod := (t * p : F[X])
  prod %ₘ t = 0 := by sorry
-- rw [Polynomial.dvd_iff_mod_by_monic_eq_zero]
--  apply dvd_mul_right
--  exact mt

theorem soundness (a_stmt : Finₓ n_stmt → F) (f : Vars → F) (x : F) :
  let verified_inst := @verified F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ A_x B_x C_x A_l B_l C_l A_m B_m C_m A_h B_h C_h f x
  let satisfying_inst := @satisfying F field n_stmt n_wit u_stmt u_wit v_stmt v_wit w_stmt w_wit r
  verified_inst a_stmt
  → (satisfying_inst a_stmt C_m) := by sorry
end Groth16