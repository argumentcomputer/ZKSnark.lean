import Mathbin

-- import ZkSNARK.BabyZkSNARK.GeneralLemmas.PolynomialDegree

noncomputable section

namespace KnowledgeSoundness
open Finset Polynomial

/- The finite field parameter of our SNARK -/

variable {F : Type u} [Field F]
/- The naturals representing:
  m - the number of gates in the circuit,
  n_stmt - the statement size,
  n_wit - the witness size -/


/-- An inductive type from which to index the variables of the 3-variable polynomials the proof manages -/
inductive Vars : Type
  | X : Vars
  | Y : Vars
  | Z : Vars

variable {m n_stmt n_wit : ℕ}
def n := n_stmt + n_wit

/- u_stmt and u_wit are fin-indexed collections of polynomials from the square span program -/
variable (u_stmt : Finₓ n_stmt → F[X]) 
variable (u_wit : Finₓ n_wit → F[X])

/- The roots of the polynomial t -/
variable (r : Finₓ m → F)
/-- t is the polynomial divisibility by which is used to verify satisfaction of the SSP -/
def t : Polynomial F := 
  ∏ i in finRange m, (x : F[X]) - c (r i)

lemma t_def : (t r) = ∏ i in finRange m, (x : F[X]) - c (r i) := rfl

/- t has degree m -/
lemma nat_degree_t : (t r).natDegree = m := by
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

lemma degree_t_pos : 0 < m → 0 < (t r).degree := by
  sorry
  -- intro hm
  -- suffices h : t.degree = some m
  --   rw h
  --   apply with_bot.some_lt_some.2
  --   exact hm

  -- have h := nat_degree_t
  -- rw Polynomial.nat_degree at h

  -- induction h1 : t.degree

  -- rw h1 at h
  -- rw option.get_or_else at h
  -- rw h at hm
  -- have h2 := has_lt.lt.false hm
  -- exfalso
  -- exact h2

  -- rw h1 at h,
  -- rw option.get_or_else at h
  -- rw h

-- Single variable form of V_wit
def V_wit_sv (a_wit : Finₓ n_wit → F) : Polynomial F := 
∑ i in finRange n_wit, a_wit i • u_wit i

/- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
def V_stmt_sv (a_stmt : Finₓ n_stmt → F) : Polynomial F 
:= ∑ i in finRange n_stmt, a_stmt i • u_stmt i

/- Checks whether a statement witness pair satisfies the SSP -/
def satisfying (a_stmt : Finₓ n_stmt → F) (a_wit : Finₓ n_wit → F) := 
(∑ i in finRange n_stmt, a_stmt i • u_stmt i
  + ∑ i in finRange n_wit, a_wit i • u_wit i) ^ 2 %ₘ (t r) = 1



/- Multivariable polynomial definititons and ultilities -/


/- Helper for converting MvPolynomial to single -/
def singlify : Vars → Polynomial F
| Vars.X => Polynomial.x 
| Vars.Y => 1
| Vars.Z => 1

variable (F)
/- Helpers for representing X, Y, Z as 3-variable polynomials -/
def X_poly : MvPolynomial Vars F := MvPolynomial.x Vars.X
def Y_poly : MvPolynomial Vars F := MvPolynomial.x Vars.Y
def Z_poly : MvPolynomial Vars F := MvPolynomial.x Vars.Z

variable {F}
/- Multivariable version of t -/
def t_mv : MvPolynomial Vars F := (t r).eval₂ MvPolynomial.c (X_poly F)

/- V_stmt as a multivariable polynomial of Vars.X -/
def V_stmt_mv (a_stmt : Finₓ n_stmt → F) : MvPolynomial Vars F 
:= (V_stmt_sv u_stmt a_stmt).eval₂ MvPolynomial.c (X_poly F)

/-- Converting a single variable polynomial to a multivariable polynomial and back yields the same polynomial -/
lemma my_multivariable_to_single_variable 
  (p : Polynomial F) : ((p.eval₂ MvPolynomial.c (X_poly F)).eval₂ Polynomial.c singlify) = p := by
  sorry
  -- apply multivariable_to_single_variable
  -- simp

/-- The crs elements as multivariate polynomials of the toxic waste samples -/
def crs_powers_of_τ (i : Fin m) : (MvPolynomial Vars F) := X_poly F ^ (i : ℕ)
def crs_γ : MvPolynomial Vars F := Z_poly F
def crs_γβ : MvPolynomial Vars F := (Z_poly F) * Y_poly F
def crs_β_ssps (i : Finₓ n_wit) : (MvPolynomial Vars F) := (Y_poly F) * (u_wit i).eval₂ MvPolynomial.c (X_poly F)

/- The coefficients of the CRS elements in the algebraic adversary's representation -/
variable (b v h : Fin m → F)
variable (b_γ v_γ h_γ b_γβ v_γβ h_γβ : F)
variable (b' v' h' : Fin n_wit → F)

/-- Polynomial forms of the adversary's proof representation -/
def B_wit : MvPolynomial Vars F := 
  ∑ i in finRange m, b i • crs_powers_of_τ i + 
  b_γ • crs_γ + b_γβ • crs_γβ +
  ∑ i in finRange n_wit,  b' i • crs_β_ssps i

def V_wit : MvPolynomial Vars F := 
  ∑ i in (Finset.range m), (v i) • (crs_powers_of_τ i)
  +
  v_γ • crs_γ
  +
  v_γβ • crs_γβ
  +
  ∑ i in (Finset.range n_wit), (v' i) • (crs_β_ssps i)

def H : MvPolynomial Vars F := 
  ∑ i in (Finset.range m), (h i) • (crs_powers_of_τ i)
  +
  h_γ • crs_γ
  +
  h_γβ • crs_γβ
  +
  ∑ i in (Finset.range n_wit), (h' i) • (crs_β_ssps i)


/-- V as a multivariable polynomial -/
def V (a_stmt : Fin n_stmt → F) : MvPolynomial Vars F := V_stmt_mv a_stmt + V_wit

/- Lemmas for proof -/

lemma eq_helper (x j : ℕ) : x = j ∨ (x = 0 ∧ j = 0) ↔ x = j :=
begin
  split,
  intro h, 
  cases h,
  exact h,
  rw [h.left, h.right],
  intro h,
  left,
  exact h,
end

lemma h2_1 : (∀ (i : Fin m), B_wit.coeff (finsupp.single Vars.X i) = b i) :=
begin
  intro j,
  rw B_wit,
  simp [crs_powers_of_τ, crs_γ, crs_γβ, crs_β_ssps],
  simp [X_poly, Y_poly, Z_poly],
  simp with coeff_simp,
  unfold_coes,
  --TODO is this best?
  -- TODO improve ite_finsupp_simplify with this
  -- simp [],
  -- ite_finsupp_simplify,
  -- simp only [single_injective_iff],
  -- simp [finsupp.single_eq_single_iff, ←fin.eq_iff_veq],
  simp [finsupp.single_eq_single_iff],
  simp only [eq_helper],
  unfold_coes,
  simp [←fin.eq_iff_veq],
end


lemma h3_1 : B_wit.coeff (Finsupp.single Vars.Z 1) = b_γ
:=
begin
  rw B_wit,
  simp [crs_powers_of_τ, crs_γ, crs_γβ, crs_β_ssps],
  simp [X_poly, Y_poly, Z_poly],
  simp with coeff_simp,
  simp [finsupp.single_eq_single_iff],
  -- -- simp? [-finsupp.single_nat_sub],
  -- simp?,
  -- ite_finsupp_simplify,
  -- simp only with coeff_simp,
  -- ite_finsupp_simplify,


end

lemma h4_1 : (∀ i, b i = 0) → (λ (i : Fin m), b i • crs_powers_of_τ i) = (λ (i : Fin m), 0) := by
  intro tmp
  apply funext
  intro x
  rw tmp x
  simp

lemma h5_1 : b_γβ • (Z_poly * Y_poly) = Y_poly * b_γβ • Z_poly := by
  rw MvPolynomial.smul_eq_C_mul
  rw MvPolynomial.smul_eq_C_mul
  ring

lemma h6_2 : (H * t_mv + MvPolynomial.C 1).coeff (finsupp.single Vars.Z 2) = 0 := by
  rw MvPolynomial.coeff_add
  rw MvPolynomial.coeff_C
  rw if_neg
  rw MvPolynomial.coeff_mul
  rw single_2_antidiagonal
  rw Finset.sum_insert
  rw Finset.sum_insert
  rw Finset.sum_singleton
  simp [H, t_mv, crs_powers_of_τ, crs_γ, crs_γβ, crs_β_ssps, X_poly, Y_poly, Z_poly]
  simp only with coeff_simp polynomial_nf
  -- unfold_coes,

  -- ite_finsupp_simplify,
  -- simp only with coeff_simp,

  simp [-finsupp.single_zero, finsupp.single_eq_single_iff]
  rw finset.mem_singleton
  simp
  simp [finset.mem_insert, finset.mem_singleton]
  simp
  -- -- dec_trivial,

  -- rw finsupp.eq_single_iff,
  -- dec_trivial,

end

-- TODO check all lemmas are used

lemma h6_3 (a_stmt : Fin n_stmt → F) : (
    (b_γβ • Z_poly 
      + ∑ (i : Fin n_stmt) in Finset.range n_stmt, a_stmt i • Polynomial.eval₂ MvPolynomial.C X_poly (u_stmt i) 
      + ∑ (i : Fin n_wit) in Finset.range n_wit, b' i • Polynomial.eval₂ MvPolynomial.C X_poly (u_wit i)
    ) ^ 2).coeff (finsupp.single Vars.Z 2) = b_γβ ^ 2 := by
  rw pow_succ
  rw pow_one
  rw MvPolynomial.coeff_mul
  rw single_2_antidiagonal

  rw Finset.sum_insert
  rw Finset.sum_insert
  rw Finset.sum_singleton

  -- NOTE The simp only with coeff_simp and ite_finsupp_simplify tactic work here
  --      But I used to get deterministic timeout - i fixed this by making simp only with coeff_simp do simp only instead
  --
  simp [X_poly, Y_poly, Z_poly]
  simp only with coeff_simp polynomial_nf
  -- simp only with coeff_simp,
  -- ite_finsupp_simplify,
  rw pow_succ
  rw pow_one

  simp
  simp [-finsupp.single_zero, finsupp.single_eq_single_iff]
  simp [finset.mem_insert, finset.mem_singleton]
  simp


/-- This function represents the exctractor in the AGM. -/
def extractor : Fin n_wit → F := b'

/-- Show that if the adversary polynomials obey the equations, 
then the coefficients give a satisfying witness. 
This theorem appears in the Baby SNARK paper as Theorem 1 case 1. -/
theorem case_1 (a_stmt : Fin n_stmt → F ) : 
  (0 < m)
  → (B_wit = V_wit * Y_poly)
  → (H * t_mv + MvPolynomial.C 1 = (V a_stmt)^2) 
  → (satisfying a_stmt extractor) := by
  rw extractor
  intros hm eqnI eqnII
  -- TODO eqnI should have a Z term on both sides
  -- "B_wit only has terms with a Y component"
  have h1 : (∀ m : Vars →₀ ℕ, m Vars.Y = 0 → B_wit.coeff m = 0)
    rw eqnI
    apply mul_var_no_constant V_wit Vars.Y
  -- "b_0 b_1, ..., b_m, ... are all zero"
  have h2 : ∀ i : Fin m, b i = 0
    intro i
    rw ← (h2_1 i)
    rw eqnI
    apply mul_var_no_constant
    rw finsupp.single_apply
    simp
  -- b_γ = 0
  have h3 : b_γ = 0
    rw ← h3_1
    rw eqnI
    apply mul_var_no_constant
    rw finsupp.single_apply
    simp
  -- "We can write B_wit as ..."
  have h4 : B_wit = b_γβ • crs_γβ + ∑ i in (Finset.range n_wit), (b' i) • (crs_β_ssps i)
    rw B_wit
    rw h4_1 h2
    rw h3
    simp
  -- "... we also see that V_wit must not have any Y terms at all"
  have h5 : V_wit = b_γβ • Z_poly + ∑ i in (Finset.range n_wit), (b' i) • ((u_wit i).eval₂ MvPolynomial.C X_poly)
    apply left_cancel_X_mul Vars.Y
    rw ←Y_poly
    rw mul_comm
    rw ←eqnI
    rw h4
    simp only [crs_γβ, crs_β_ssps]
    rw mul_add
    rw h5_1
    rw finset.mul_sum
    simp
  -- "... write V(.) as follows ..."
  have h6 : V a_stmt = b_γβ • Z_poly 
      + ∑ i in (Finset.range n_stmt), (a_stmt i) • ((u_stmt i).eval₂ MvPolynomial.C X_poly)
      + ∑ i in (Finset.range n_wit), (b' i) • ((u_wit i).eval₂ MvPolynomial.C X_poly)
    rw V
    rw V_stmt_mv
    rw h5
    rw V_stmt_sv
    rw polynomial.eval₂_finset_sum
    simp only [Polynomial.eval₂_smul]
    simp only [←MvPolynomial.smul_eq_C_mul]
    ring
  -- ... we can conclude that b_γβ = 0.
  have h7 : b_γβ = 0
    let eqnII' := eqnII
    rw h6 at eqnII'
    have h6_1 := congr_arg (MvPolynomial.coeff (finsupp.single Vars.Z 2)) eqnII'
    rw h6_2 at h6_1
    rw h6_3 at h6_1
    exact pow_eq_zero (eq.symm h6_1)
  -- Finally, we arrive at the conclusion that the coefficients define a satisfying witness such that ...
  have h8 : V a_stmt = 
      ∑ i in (Finset.range n_stmt), (a_stmt i) • ((u_stmt i).eval₂ MvPolynomial.C X_poly)
      + ∑ i in (Finset.range n_wit), (b' i) • ((u_wit i).eval₂ MvPolynomial.C X_poly)
    rw h6
    rw h7
    simp
  -- Treat both sides of this a single variable polynomial
  have h9 := congr_arg (MvPolynomial.eval₂ (@polynomial.C F _) singlify) h8
  rw MvPolynomial.eval₂_add at h9
  rw MvPolynomial.eval₂_sum at h9
  simp [MvPolynomial.smul_eq_C_mul] at h9
  simp [my_multivariable_to_single_variable] at h9
  simp [←Polynomial.smul_eq_C_mul] at h9
  -- Now we solve the main goal. First, we expand the definition of "satisfying"
  rw satisfying
  rw ←h9
  clear h8 h9

  -- TODO is there a more efficient way to simply say (evaluate f on both sides of this hypothesis)? Yes the congr tactic does this
  have h10 : ((H * t_mv + MvPolynomial.C 1).eval₂ Polynomial.C singlify) %ₘ t = (((V a_stmt)^2).eval₂ Polynomial.C singlify) %ₘ t
    rw eqnII
  -- h10 done
  rw MvPolynomial.eval₂_add at h10
  rw MvPolynomial.eval₂_mul at h10

  rw ←MvPolynomial.eval₂_pow

  rw ←h10
  rw t_mv
  rw my_multivariable_to_single_variable t
  have h12: MvPolynomial.C 1 = (Polynomial.C 1 : Polynomial F).eval₂ MvPolynomial.C X_poly
    rw Polynomial.eval₂_C
  -- h12 done
  rw h12
  rw my_multivariable_to_single_variable
  have h13 : (MvPolynomial.eval₂ Polynomial.C singlify H * t + Polynomial.C 1 : Polynomial F) /ₘ t = (MvPolynomial.eval₂ Polynomial.C singlify H : Polynomial F) ∧ (MvPolynomial.eval₂ Polynomial.C singlify H * t + Polynomial.C 1 : Polynomial F) %ₘ t = (Polynomial.C 1 : Polynomial F)
    apply Polynomial.div_mod_by_monic_unique
    exact monic_t
    split
    rw [add_comm, mul_comm]
    rw Polynomial.degree_C
    exact degree_t_pos hm
    exact one_ne_zero
  -- h13 done
  rw h13.2
  simp
end


end KnowledgeSoundness