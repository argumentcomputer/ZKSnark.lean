import Mathbin.Data.Finsupp.Antidiagonal
import Mathbin.Data.Finsupp.Basic
import Mathbin.Data.Finset.Basic

namespace SingleAntidiagonal

variable {S : Type}
variable [DecidableEq S]

/-- A general lemma about the anitdiagonal of a finsupp.single. -/
lemma single_antidiagonal (s : S) (n : ℕ) : 
  (Finsupp.single s n).antidiagonal 
  = (Finset.range (n+1)).image (λ i => (Finsupp.single s (n-i), Finsupp.single s (i))) 
:= by sorry
/-  
  rw [Finset.ext_iff]
  intro a
  rw [Finsupp.mem_antidiagonal]
  rw [Finset.mem_image]
  apply Iff.intro
  intro h
  use a.snd s
  apply Exists.intro
  rw [Finsupp.ext_iff] at h
  have h1 := h s
  simp at h1
  rw [Finset.mem_range]
  rw [←h1]
  apply @nat.lt_of_lt_of_le (a.snd s) (a.snd s + 1) _
  exact lt_add_one ((a.snd) s)
  rw [add_assoc]
  exact ((a.snd) s + 1).le_add_left ((a.fst) s)
  rw [prod.ext_iff]
  simp
  split
  rw [Finsupp.ext_iff]
  intro a_1
  rw [Finsupp.nat_sub_apply]
  rw [Finsupp.single_apply]
  rw [Finsupp.single_apply]
  by_cases h2 : a_1 = s
   rw h2
   simp
   have h3 : (a.fst + a.snd) s = (finsupp.single s n) s
   rw [h]
   rw [Finsupp.add_apply] at h3
   rw [Finsupp.single_apply] at h3
   simp at h3
   rw ←h3
   simp
   rw if_neg
   rw if_neg
   have h3 : (a.fst + a.snd) a_1 = (finsupp.single s n) a_1
   rw [h]
   rw [Finsupp.add_apply] at h3
   rw [Finsupp.single_apply] at h3
   simp at h3
   rw [if_neg] at h3
   simp at h3
  --  rw nat.sub_zero,
  --  rw add_eq_zero_iff at h3,
   rw [h3.left]
   finish
   finish
   finish
  rw [Finsupp.ext_iff]
  intro a_1
  rw [Finsupp.single_apply]
  by_cases h2 : a_1 = s
    rw h2
    simp
    rw if_neg
    have h3 : (a.fst + a.snd) a_1 = (finsupp.single s n) a_1
    rw h
    rw [Finsupp.add_apply] at h3
    rw [Finsupp.single_apply] at h3
    simp at h3
    rw if_neg at h3
    -- rw add_eq_zero_iff at h3,
    simp at h3

    rw [h3.right]
    finish
    finish
  intro h
  cases h
  cases h_h
  let h1 := prod.ext_iff.1 h_h_h
  rw [←h1.left, ←h1.right]
  simp
  rw [←Finsupp.single_nat_sub, ←Finsupp.single_add]
  rw [Finset.mem_range] at h_h_w
  have h4 : n - h_w + h_w = n
    rw nat.lt_succ_iff at h_h_w
    exact nat.sub_add_cancel h_h_w
  rw h4
-/


lemma Finsupp.sub_le_right_of_le_add (a b c : S →₀ ℕ) (h : a ≤ b + c) : a - c ≤ b := by sorry
/-
  intro
  have z := h s
  rw [Nat.nat_sub_apply]
  rw [Nat.add_apply] at z
  -- rw z,
  exact Nat.sub_le_right_of_le_add z
-/

-- TODO generalize and add to mathlib
lemma Nat.add_inf (a b c : ℕ) : a + (b ⊓ c) = (a + b) ⊓ (a + c) := by sorry
  -- by_cases b ≤ c
  -- rw [inf_eq_left.2 h]
  --apply h
  -- have h' : c ≤ b
  --  exact le_of_not_ge h
  -- simp [inf_eq_right.2 h']
  -- exact h'

lemma Finsupp.nat_add_inf (a b c : S →₀ ℕ) : a + (b ⊓ c) = (a + b) ⊓ (a + c) := by sorry
--  ext
--  simp only [Nat.add_apply, Finsupp.inf_apply]
--  apply Nat.add_inf

-- -- TODO generalize and add to mathlib
-- lemma nat.add_lemma (a b c : ℕ) (h : b ≤ a) : a - b + c = a + c - b := 
-- begin
--   exact nat.sub_add_eq_add_sub h,
-- end

-- TODO generalize and add to mathlib
lemma Nat.add_lemma2 (a b c : ℕ) : c = a + b -> c - a = b := by sorry
  -- rw [Nat.sub_eq_of_eq_add]

lemma helper (a b c d : ℕ) (h : b + d = a + c) : a - b ⊓ a + (c - (b - b ⊓ a)) = d := by
  sorry
/- 
  by_cases h1 : b ≤ a
  simp [inf_eq_left.2 h1]
  rw [Nat.sub_add_eq_add_sub]
  rw [<-h],
  exact norm_num.sub_nat_pos (b + d) b d rfl
  exact h1
  have h' : a ≤ b
    exact le_of_not_ge h1
  simp [inf_eq_right.2 h']
  apply Nat.sub_eq_of_eq_add
  rw [Nat.sub_add_eq_add_sub]
  rw [h]
  simp only [Nat.add_sub_cancel_left]
  exact h'
-/

-- TODO: Put in mathlib
lemma add_antidiagonal (f g : S →₀ ℕ) : 
  (f + g).antidiagonal = (Finset.product (f.antidiagonal) (g.antidiagonal)).image (λ x => ((x.fst.fst + x.snd.fst), (x.fst.snd + x.snd.snd))) := by
  sorry
 /- 
  rw [Finset.ext_iff]
  intro a
  rw [Finsupp.mem_antidiagonal]
  rw [Finset.mem_image]
  split
  { 
    intro h
    use ((a.fst ⊓ f, f - (a.fst ⊓ f)), (a.fst - (a.fst ⊓ f), g - (a.fst - (a.fst ⊓ f))))
    split
    -- TODO abstract lemma about a+b, a+c, b+d, c+d
    rw [Fin.finset.mem_product]
    split
    simp only [Finsupp.mem_antidiagonal]
    apply Finsupp.nat_add_sub_of_le
    exact inf_le_right
    simp only [Finsupp.mem_antidiagonal]
    apply Finsupp.nat_add_sub_of_le
    apply Finsupp.sub_le_right_of_le_add
    rw [Finsupp.nat_add_inf]
    simp
    rw [add_comm]
    rw [←h]
    simp
    -- simp only,
    have tmp : a = (a.fst, a.snd)
    simp
    rw [tmp]
    simp only
    apply congr_arg2
    apply Finsupp.nat_add_sub_of_le
    exact inf_le_left

    -- TODO probably the best way to finish is
    ext
    simp only [add_apply, nat_sub_apply, finsupp.inf_apply]
    apply helper
    have h1 := finsupp.ext_iff.1 h
    exact h1 a_1

    -- then by_cases on the ⊓ which is greater.
  }
  { intro h
    cases h with a1 h2
    cases h2 with H h3
    rw [Finset.mem_product] at H
    rw [Finsupp.mem_antidiagonal] at H
    rw [Finsupp.mem_antidiagonal] at H
    rw [←H.left, ←H.right]
    rw [prod.ext_iff] at h3
    rw [←h3.left, ←h3.right]
    finish
    }
  -- hint,
  -- ext,
  -- simp only,
  -- use 
-/

/- A copy of the square_antidiagonal lemma, which relies on the more general single_antidiagonal rather than being self contained. -/
/-
lemma single_2_antidiagonal (s : S) : (Finsupp.single s 2).Antidiagonal = 
{
  (Finsupp.single s 0, Finsupp.single s 2), 
  (Finsupp.single s 1, Finsupp.single s 1), 
  (Finsupp.single s 2, Finsupp.single s 0), 
}
:= by
  rw [single_antidiagonal s 2]
  rw [Finset.ext_iff]
  intro a
  rw [Finset.range]
  rw [Finset.image]
  simp [-Finsupp.single_nat_sub]
-/

end SingleAntidiagonal