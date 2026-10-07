import Mathlib

/-!
# The Gauss sum of `⟨10/17⟩`: `∑_{x mod 17} e^{πi·10x²/17} = -√17` (so `Br⟨10/17⟩ = 4`)

Used in Proposition `prop:forms` (the paper: "the Gauss sum of `⟨10/17⟩` is `(5/17)√17 = -√17`").
Proof, with `ψ` the standard additive character of `ℤ/17` (Mathlib's `ZMod.stdAddChar`):
* `S = ∑ ψ(5x²)`;
* `S² = ∑_{x,w} ψ(5x² + 5w²) = ∑_{x,w} ψ(5x² - 5w²)` (`w ↦ 4w`, `4² = -1`)
  `= ∑_u ψ(-5u²) ∑_x ψ(10ux) = 17` (`w = x - u`, orthogonality `AddChar.sum_mulShift`), so `S = ±√17`;
* `Re S = ∑ cos(2π·(5x² mod 17)/17) ≤ 3 < √17` (cosine bounds), so `S = -√17`.
-/

namespace Srg154

open Complex
open scoped Real

noncomputable def q17 (x : ZMod 17) : ℝ := 10 * (x.val : ℝ) ^ 2 / 17

/-- The quadratic Gauss sum of `⟨10/17⟩`. -/
def Gauss17 : Prop := ∑ x : ZMod 17, exp (π * (q17 x : ℂ) * I) = -(Real.sqrt 17 : ℂ)

/-- `ψ = ZMod.stdAddChar`, `ψ(j) = e^{2πij/17}`. -/
noncomputable abbrev ψ17 : AddChar (ZMod 17) ℂ := ZMod.stdAddChar

theorem term17 (x : ZMod 17) : exp (π * (q17 x : ℂ) * I) = ψ17 (5 * x ^ 2) := by
  have h : (5 * x ^ 2 : ZMod 17) = ((5 * x.val ^ 2 : ℕ) : ZMod 17) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [h, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold q17
  congr 1
  push_cast; ring

theorem psi17_apply (j : ZMod 17) : ψ17 j = exp (2 * π * I * j.val / 17) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]; norm_num

theorem psi17_re (j : ZMod 17) : (ψ17 j).re = Real.cos (2 * π * j.val / 17) := by
  rw [psi17_apply]
  rw [show (2 * π * I * j.val / 17 : ℂ) = ((2 * π * j.val / 17 : ℝ) : ℂ) * I by push_cast; ring,
    exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero, add_zero]

/-- `S² = 17`. -/
theorem gauss17_sq : (∑ x : ZMod 17, ψ17 (5 * x ^ 2)) ^ 2 = 17 := by
  have hψ := ZMod.isPrimitive_stdAddChar 17
  rw [sq, Finset.sum_mul_sum]
  -- w ↦ 4w
  have h4 : Function.Bijective (fun w : ZMod 17 => 4 * w) := by
    have e1 : (13 : ZMod 17) * 4 = 1 := by decide
    have e2 : (4 : ZMod 17) * 13 = 1 := by decide
    refine Function.bijective_iff_has_inverse.2 ⟨fun w => 13 * w, fun w => ?_, fun w => ?_⟩
    · simp only; rw [← mul_assoc, e1, one_mul]
    · simp only; rw [← mul_assoc, e2, one_mul]
  have step1 : ∀ x : ZMod 17, ∑ w : ZMod 17, ψ17 (5 * x ^ 2) * ψ17 (5 * w ^ 2) =
      ∑ u : ZMod 17, ψ17 (x * (10 * u)) * ψ17 (-5 * u ^ 2) := by
    intro x
    rw [← Fintype.sum_bijective _ h4 (fun w => ψ17 (5 * x ^ 2) * ψ17 (5 * (4 * w) ^ 2))
      (fun w => ψ17 (5 * x ^ 2) * ψ17 (5 * w ^ 2)) (fun _ => rfl)]
    rw [← (Equiv.subLeft x).sum_comp]
    refine Fintype.sum_congr _ _ fun u => ?_
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    have h80 : (80 : ZMod 17) = -5 := by decide
    simp only [Equiv.subLeft_apply]
    linear_combination (x - u) ^ 2 * h80
  simp only [step1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  have hs : ∀ u : ZMod 17, ∑ x : ZMod 17, ψ17 (x * (10 * u)) =
      if 10 * u = 0 then (Fintype.card (ZMod 17) : ℂ) else 0 := fun u => by
    rw [AddChar.sum_mulShift _ hψ]; split_ifs <;> simp
  simp only [hs]
  have h10 : ∀ u : ZMod 17, (10 * u = 0 ↔ u = 0) := by decide
  simp only [h10, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp

/-- Bound function: `2·cos(2πk/17) ≤ B(k)`. -/
def B17 (k : ℕ) : ℕ :=
  if k = 0 then 2 else if k = 3 ∨ k = 14 then 1 else if 5 ≤ k ∧ k ≤ 12 then 0 else 2

theorem cos_le_B17 (k : ℕ) : 2 * Real.cos (2 * π * k / 17) ≤ B17 k := by
  have hpi := Real.pi_pos
  unfold B17
  split_ifs with h0 h3 h5
  · subst h0; simp
  · have h6 : Real.cos (6 * π / 17) ≤ 1 / 2 := by
      rw [← Real.cos_pi_div_three]
      apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith) (by nlinarith)
    rcases h3 with rfl | rfl
    · push_cast
      rw [show 2 * π * 3 / 17 = 6 * π / 17 by ring]; linarith
    · push_cast
      rw [show 2 * π * 14 / 17 = 2 * π - 6 * π / 17 by ring, Real.cos_two_pi_sub]; linarith
  · have hk5 : (5 : ℝ) ≤ k := by exact_mod_cast h5.1
    have hk12 : (k : ℝ) ≤ 12 := by exact_mod_cast h5.2
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := 2 * π * k / 17) (by nlinarith) (by nlinarith)
    push_cast; linarith
  · push_cast; linarith [Real.cos_le_one (2 * π * k / 17)]

theorem sum_B17 : ∑ x : ZMod 17, B17 (5 * x ^ 2).val = 6 := by decide +kernel

/-- `Re S ≤ 3`. -/
theorem gauss17_re_le : (∑ x : ZMod 17, ψ17 (5 * x ^ 2)).re ≤ 3 := by
  rw [Complex.re_sum]
  simp only [psi17_re]
  have : ∑ x : ZMod 17, 2 * Real.cos (2 * π * ((5 * x ^ 2 : ZMod 17).val : ℝ) / 17) ≤
      ∑ x : ZMod 17, (B17 (5 * x ^ 2).val : ℝ) := Finset.sum_le_sum fun x _ => cos_le_B17 _
  rw [← Finset.mul_sum] at this
  have h6 : ∑ x : ZMod 17, (B17 (5 * x ^ 2).val : ℝ) = 6 := by exact_mod_cast sum_B17
  linarith

/-- **The Gauss sum of `⟨10/17⟩` is `-√17`.** -/
theorem gauss17 : Gauss17 := by
  unfold Gauss17
  simp only [term17]
  set S := ∑ x : ZMod 17, ψ17 (5 * x ^ 2) with hS
  have hsq := gauss17_sq
  rw [← hS] at hsq
  have hre := gauss17_re_le
  rw [← hS] at hre
  have h17 : ((Real.sqrt 17 : ℝ) : ℂ) ^ 2 = 17 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hfac : (S - Real.sqrt 17) * (S + Real.sqrt 17) = 0 := by
    linear_combination hsq - h17
  rcases mul_eq_zero.1 hfac with h | h
  · exfalso
    have : S = Real.sqrt 17 := sub_eq_zero.1 h
    rw [this, ofReal_re] at hre
    have : (4 : ℝ) < Real.sqrt 17 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  · exact eq_neg_of_add_eq_zero_left h

end Srg154
