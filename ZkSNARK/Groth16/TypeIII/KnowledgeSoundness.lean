import Mathbin

import ZkSNARK.Groth16.Vars

noncomputable section

/-!
# Knowledge Soundness
This file proves the knowledge-soundness property of the Groth16 system for type III pairings, as 
presented in "Another Look at Extraction and Randomization of Groth's zk-SNARK" by 
[Baghery et al.](https://eprint.iacr.org/2020/811.pdf).
-/

namespace TypeIII

open MvPolynomial Finset

variable {F : Type u} [field : Field F]

variable {n_stmt n_wit n_var : ℕ}

/- u_stmt and u_wit are fin-indexed collections of polynomials from the square span program -/
variable {u_stmt : Finₓ n_stmt → F[X]}
variable {u_wit : Finₓ n_wit → F[X]}
variable {v_stmt : Finₓ n_stmt → F[X]}
variable {v_wit : Finₓ n_wit → F[X]}
variable {w_stmt : Finₓ n_stmt → F[X]}
variable {w_wit : Finₓ n_wit → F[X]}

/- The roots of the polynomial t -/
variable (r : Finₓ n_wit → F)

/- t is the polynomial divisibility by which is used to verify satisfaction of the SSP -/
def t : F[X] := ∏ i in finRange n_wit, (Polynomial.x : F[X]) - Polynomial.c (r i)

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

variable (F)
def crs_α  (f : Vars → F) : F[X] := Polynomial.c (f Vars.α)

def crs_β (f : Vars → F) : F[X] := Polynomial.c (f Vars.β)

def crs_γ (f : Vars → F) : F[X] := Polynomial.c (f Vars.γ)

def crs_δ (f : Vars → F) : F[X] := Polynomial.c (f Vars.δ)

def crs_powers_of_x (i : Finₓ n_var) : F[X] := ((Polynomial.x)^(i : ℕ))

def crs_l (i : Finₓ n_stmt) (f : Vars → F) : F[X] := 
  ((Polynomial.c (1 / f Vars.γ)) * (Polynomial.c ((f Vars.β) / (f Vars.γ)))) * (u_stmt i)
  +
  (Polynomial.c  (f Vars.α / f Vars.γ)) * (v_stmt i)
  +
  (w_stmt i) 

def crs_m (i : Finₓ n_wit) (f : Vars → F) : F[X] := 
  ((Polynomial.c (1 / (f Vars.δ))) * (Polynomial.c ((f Vars.β) / (f Vars.δ)))) * (u_wit i)
  +
  (Polynomial.c  ((f Vars.α) / (f Vars.δ))) * (v_wit i)
  +
  (w_wit i) 

def crs_n (i : Finₓ (n_var - 1)) (f : Vars → F) : F[X] := 
  (((Polynomial.x)^(i : ℕ)) * (t r)) * Polynomial.c (1 / f Vars.δ)

/- The coefficients of the CRS elements in the algebraic adversary's representation -/
variable {A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ : F}
variable {A_x B_x C_x : Finₓ n_var → F}
variable {A_l B_l C_l : Finₓ n_stmt → F}
variable {A_m B_m C_m : Finₓ n_wit → F}
variable {A_h B_h C_h : Finₓ (n_var - 1) → F}

/- Polynomial forms of the adversary's proof representation -/
def A (f : Vars → F) : F[X] := 
  (Polynomial.c A_α) * crs_α F f
  +
  (Polynomial.c A_β) * crs_β F f
  +
  (Polynomial.c A_δ) * crs_δ F f
  +
  ∑ i in (finRange n_var), (Polynomial.c (A_x i)) * (crs_powers_of_x F i)
  +
  ∑ i in (finRange n_stmt), (Polynomial.c (A_l i)) * (@crs_l F field n_stmt u_stmt v_stmt w_stmt i f)
  +
  ∑ i in (finRange n_wit), (Polynomial.c (A_m i)) * (@crs_m F field n_wit u_wit v_wit w_wit i f)
  +
  ∑ i in (finRange (n_var-1)), (Polynomial.c (A_h i)) * (crs_n F r i f)

def B (f : Vars → F) : F[X] := 
  (Polynomial.c B_β) * (crs_β F f)
  + 
  (Polynomial.c B_γ) * (crs_γ F f)
  +
  (Polynomial.c B_δ) * (crs_δ F f)
  +
  ∑ i in (finRange n_var), (Polynomial.c (B_x i)) * (crs_powers_of_x F i)

def C (f : Vars → F) : F[X]  := 
  (Polynomial.c C_α) * crs_α F f
  +
  (Polynomial.c C_β) * crs_β F f
  +
  (Polynomial.c C_δ) * crs_δ F f
  +
  ∑ i in (finRange n_var), (Polynomial.c (C_x i)) * (crs_powers_of_x F i)
  +
  ∑ i in (finRange n_stmt), (Polynomial.c (C_l i)) * (@crs_l F field n_stmt u_stmt v_stmt w_stmt i f)
  +
  ∑ i in (finRange n_wit), (Polynomial.c (C_m i)) * (@crs_m F field n_wit u_wit v_wit w_wit i f)
  +
  ∑ i in (finRange (n_var - 1)), (Polynomial.c (C_h i)) * (crs_n F r i f)

/- The modified CRS elements 
these are multivariate (non-Laurent!) polynomials of the toxic waste samples, 
obtained by multiplying the Laurent polynomial forms of the CRS through by γ * δ. 
We will later prove that the laurent polynomial equation is equivalent to a similar equation 
of the modified crs elements, allowing us to construct a proof in terms of polynomials -/
def crs'_α  : MvPolynomial Vars F[X] :=
  let pol_alpha := (x Vars.α : MvPolynomial Vars F[X])
  let pol_gamma := (x Vars.γ : MvPolynomial Vars F[X])
  let pol_delta := (x Vars.δ : MvPolynomial Vars F[X])
  (pol_alpha * pol_gamma) * pol_delta

def crs'_β : MvPolynomial Vars F[X] :=
  let pol_beta := (x Vars.β : MvPolynomial Vars F[X])
  let pol_gamma := (x Vars.γ : MvPolynomial Vars F[X])
  let pol_delta := (x Vars.δ : MvPolynomial Vars F[X])
  (pol_beta * pol_gamma) * pol_delta

def crs'_γ : MvPolynomial Vars F[X] :=
  let pol_gamma := (x Vars.γ : MvPolynomial Vars F[X])
  let pol_delta := (x Vars.δ : MvPolynomial Vars F[X])
  (pol_gamma * pol_gamma) * pol_delta

def crs'_δ : MvPolynomial Vars F[X] :=
  let pol_gamma := (x Vars.γ : MvPolynomial Vars F[X])
  let pol_delta := (x Vars.δ : MvPolynomial Vars F[X])
  (pol_delta * pol_gamma) * pol_delta

def crs'_powers_of_x (i : Finₓ n_var) : MvPolynomial Vars F[X] :=
  let pol_gamma := (x Vars.γ : MvPolynomial Vars F[X])
  let pol_delta := (x Vars.δ : MvPolynomial Vars F[X])
  let pow := (MvPolynomial.c (Polynomial.x ^ (i : ℕ)) : MvPolynomial Vars F[X])
  (pow * pol_gamma) * pol_delta

def crs'_l (i : Finₓ n_stmt) : MvPolynomial Vars F[X] :=
  let pol_alpha := (x Vars.α : MvPolynomial Vars F[X])
  let pol_beta := (x Vars.β : MvPolynomial Vars F[X])
  let pol_delta := (x Vars.δ : MvPolynomial Vars F[X])
  let pol_u := (MvPolynomial.c (u_stmt i) : MvPolynomial Vars F[X])
  let pol_v := (MvPolynomial.c (v_stmt i) : MvPolynomial Vars F[X])
  let pol_w := (MvPolynomial.c (w_stmt i) : MvPolynomial Vars F[X])
  (pol_beta * pol_delta) * pol_u
  +
  (pol_alpha * pol_delta) * pol_v
  +
  pol_delta * pol_w

def crs'_m (i : Finₓ n_wit) : MvPolynomial Vars F[X] :=
  let pol_alpha := (x Vars.α : MvPolynomial Vars F[X])
  let pol_beta := (x Vars.β : MvPolynomial Vars F[X])
  let pol_gamma := (x Vars.γ : MvPolynomial Vars F[X])
  let pol_u := (MvPolynomial.c (u_wit i) : MvPolynomial Vars F[X])
  let pol_v := (MvPolynomial.c (v_wit i) : MvPolynomial Vars F[X])
  let pol_w := (MvPolynomial.c (w_wit i) : MvPolynomial Vars F[X])
  (pol_beta * pol_gamma) * pol_u
  +
  (pol_alpha * pol_gamma) * pol_v
  +
  pol_gamma * pol_w

def crs'_t (i : Finₓ (n_var - 1)) : MvPolynomial Vars F[X] :=
  let pol_gamma := (x Vars.γ : MvPolynomial Vars F[X])
  let pow :=  (MvPolynomial.c (((Polynomial.x)^(i : ℕ)) * (t r)) : MvPolynomial Vars (F[X]))
  pol_gamma * pow

/- Polynomial form of A in the adversary's proof representation -/
def A'  : MvPolynomial Vars F[X] :=
  let pol_aα := (MvPolynomial.c (Polynomial.c A_α) : MvPolynomial Vars F[X])
  let pol_aβ := (MvPolynomial.c (Polynomial.c A_β) : MvPolynomial Vars F[X])
  let pol_aδ := (MvPolynomial.c (Polynomial.c A_δ) : MvPolynomial Vars F[X])
  let crs'_α_inst := @crs'_α F field
  let crs'_β_inst := @crs'_β F field
  let crs'_δ_inst := @crs'_δ F field
  let pol_gamma := (x Vars.γ : MvPolynomial Vars F[X])
  let pol_delta := (x Vars.δ : MvPolynomial Vars F[X])
  let sum₁ := (MvPolynomial.c (∑ i in (finRange n_var), ((Polynomial.c (A_x i)) * Polynomial.x ^ (i : ℕ))) : MvPolynomial Vars F[X])
  let sum₂ := ∑ i in (finRange n_stmt),
    let pol_al := (MvPolynomial.c (Polynomial.c (A_l i)) : MvPolynomial Vars F[X])
    (@crs'_l F field n_stmt u_stmt v_stmt w_stmt i) * pol_al
  let sum₃ := ∑ i in (finRange n_wit),
    let pol_am := (MvPolynomial.c (Polynomial.c (A_m i)) : MvPolynomial Vars F[X])
    (@crs'_m F field n_wit u_wit v_wit w_wit i) * pol_am
  let sum₄ := ∑ i in (finRange (n_var - 1)),
    let pol_ah :=  (MvPolynomial.c (Polynomial.c (A_h i)) : MvPolynomial Vars F[X])
    (@crs'_t F field n_wit n_var r i) * pol_ah
  crs'_α_inst * pol_aα
  +
  crs'_β_inst * pol_aβ
  + 
  crs'_δ_inst * pol_aδ
  +
  (pol_gamma * pol_delta) * sum₁
  +
  sum₂
  +
  sum₃
  +
  sum₄

/- Polynomial form of B in the adversary's proof representation -/
def B'  : MvPolynomial Vars F[X] :=
  let pol_bβ := (MvPolynomial.c (Polynomial.c B_β) : MvPolynomial Vars F[X])
  let pol_bγ := (MvPolynomial.c (Polynomial.c B_γ) : MvPolynomial Vars F[X])
  let pol_bδ := (MvPolynomial.c (Polynomial.c B_γ) : MvPolynomial Vars F[X])
  let pol_gamma := (x Vars.γ : MvPolynomial Vars F[X])
  let pol_delta := (x Vars.δ : MvPolynomial Vars F[X])
  let sum := ∑ i in (finRange n_var), ((Polynomial.c (B_x i)) * Polynomial.x ^ (i : ℕ))
  let sum_c := (MvPolynomial.c sum : MvPolynomial Vars F[X])
  (@crs'_β F field) * pol_bβ
  + 
  (@crs'_γ F field) * pol_bγ
  +
  (@crs'_δ F field) * pol_bδ
  +
  (pol_gamma * pol_delta) * sum_c

#check @crs'_t

/- Polynomial form of C in the adversary's proof representation -/
def C'  : MvPolynomial Vars F[X] :=
  let pol_cα := (MvPolynomial.c (Polynomial.c C_α) : MvPolynomial Vars F[X])
  let pol_cβ := (MvPolynomial.c (Polynomial.c C_β) : MvPolynomial Vars F[X])
  let pol_cγ := (MvPolynomial.c (Polynomial.c C_γ) : MvPolynomial Vars F[X])
  let pol_gamma := (x Vars.γ : MvPolynomial Vars F[X])
  let pol_delta := (x Vars.δ : MvPolynomial Vars F[X])
  let sum₁ := ∑ i in (finRange n_var), ((Polynomial.c (C_x i)) * Polynomial.x ^ (i : ℕ))
  let sum_cx := (MvPolynomial.c sum₁ : MvPolynomial Vars F[X])
  let sum₂ := (∑ i in (finRange n_stmt), 
    let pol_cl := (MvPolynomial.c (Polynomial.c (C_l i)) : MvPolynomial Vars F[X])
    (@crs'_l F field n_stmt u_stmt v_stmt w_stmt i) * pol_cl : MvPolynomial Vars F[X])
  let sum₃ := ∑ i in (finRange n_wit),
    let pol_cm := (MvPolynomial.c (Polynomial.c (C_m i)) : MvPolynomial Vars F[X])
    (@crs'_m F field n_wit u_wit v_wit w_wit i) * pol_cm
  let sum₄ :=
    ∑ i in (finRange (n_var - 1)),
    let pol_ch := (MvPolynomial.c (Polynomial.c (C_h i)) : MvPolynomial Vars F[X])
    (@crs'_t F field n_wit n_var r i) * pol_ch
  (@crs'_α F field) * pol_cα
  +
  (@crs'_β F field) * pol_cβ
  + 
  (@crs'_δ F field) * pol_cγ
  +
  (pol_gamma * pol_delta) * sum_cx
  +
  sum₂
  +
  sum₃
  +
  sum₄

def verified (a_stmt : Finₓ n_stmt → F) (f : Vars → F) : Prop :=
  let A_inst := 
    @A F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_δ A_x A_l A_m A_h f
  let B_inst := @B F field n_var B_β B_γ B_δ B_x f
  let C_inst := 
    @C F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r C_α C_β C_δ C_x C_l C_m C_h f
  A_inst * B_inst = (crs_α F f) * (crs_β F f) + 
    (∑ i in finRange n_stmt, a_stmt i • @crs_l F field n_stmt u_stmt v_stmt w_stmt i f) * (crs_γ F f) + C_inst * (crs_δ F f)

def verified' (a_stmt : Finₓ n_stmt → F ) : Prop :=
  let A'_inst :=
    @A' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_δ A_x A_l A_m A_h
  let B'_inst := @B' F field n_var B_β B_γ B_x
  let C'_inst := 
    @C' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r C_α C_β C_δ C_x C_l C_m C_h
  (A'_inst * B'_inst) = 
    (@crs'_α F field) * (@crs'_β F field) + 
    (∑ i in finRange n_stmt, 
      let pol_astmt := (MvPolynomial.c (Polynomial.c (a_stmt i)) : MvPolynomial Vars F[X])
      pol_astmt * (@crs'_l F field n_stmt u_stmt v_stmt w_stmt i) ) * 
    (crs'_γ F) + C'_inst * (crs'_δ F)

lemma modification_implication (a_stmt : Finₓ n_stmt → F) (f : Vars → F) :
  let verified_inst :=
    @verified F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_δ B_β B_γ B_δ C_α C_β C_δ A_x B_x C_x A_l C_l A_m C_m A_h C_h a_stmt f
  let verified'_inst :=
    @verified' F field n_stmt n_wit n_var u_stmt u_wit v_stmt v_wit w_stmt w_wit r A_α A_β A_δ B_β B_γ B_δ C_α C_β C_δ A_x B_x C_x A_l C_l A_m C_m A_h C_h a_stmt
  verified_inst → verified'_inst := by sorry

end TypeIII