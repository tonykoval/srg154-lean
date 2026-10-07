import Srg154.Gauss17

/-!
# Proposition `prop:forms`: the finite classification via Milgram's formula

`DiscForm.lean` proves, from the graph, that `D(N) = D₂ ⊕ D₃ ⊕ D₁₇` with
* `D₁₇ = ⟨ȳ⟩ ≅ ⟨10/17⟩`,
* `D₂` elementary of rank `≤ 2` with `q ≡ 1` on `D₂ \ {0}`,
* `D₃` elementary of rank `≤ 2` with `q = (2/3)·Q`, `Q` an anisotropic quadratic form over `𝔽₃`.

Here we model every such candidate as finite data and decide which candidates satisfy Milgram's formula
`∑_{x ∈ D} e^{πi q(x)} = √|D| · e^{2πi·sign/8}` with `sign = rank N = 22`.

* `Cand`: `(r₂, r₃, a₀, a₁, b)`: `D₂ = 𝔽₂^{r₂}`, `D₃ = 𝔽₃^{r₃}` with `Q(c) = a₀c₀² + a₁c₁² + b c₀c₁`
  (`Valid`: the unused coefficients are `0` and `Q` is anisotropic).
* `gaussTotal c`: the Gauss sum of `D₂ ⊕ D₃ ⊕ ⟨10/17⟩`, a sum over the finite group in `ℂ`.
* `Milgram c`: Milgram's formula for `c` (a HYPOTHESIS: Milgram's theorem is not in Mathlib).
* `Gauss17`: the value `∑_{x mod 17} e^{πi·10x²/17} = -√17`, i.e. `Br⟨10/17⟩ = 4`. Proved in `gauss17`
  (sign of a quadratic Gauss sum, by `|S|² = 17` and explicit cosine bounds), so it is NOT a hypothesis.
* `forms_classification`: `Valid c ∧ Milgram c ⇒ c = formI ∨ c = formII`, where
  `formI = ⟨2/3⟩ ⊕ ⟨10/17⟩` (`|D| = 51`) and `formII = V₂ ⊕ ⟨4/3⟩ ⊕ ⟨10/17⟩` (`|D| = 204`);
  `formI_milgram`, `formII_milgram`: both forms do satisfy Milgram's formula (so "exactly two").
* `det_cases`: `|D| ∈ {51, 204}`.
-/

namespace Srg154

open Complex
open scoped Real

/-- Candidate data `(r₂, r₃, (a₀, a₁, b))`. -/
abbrev Cand := Fin 3 × Fin 3 × (ZMod 3 × ZMod 3 × ZMod 3)

def Cand.r2 (c : Cand) : ℕ := c.1.val
def Cand.r3 (c : Cand) : ℕ := c.2.1.val

/-- `D₂ = 𝔽₂^{r₂}` inside `𝔽₂²`. -/
def S2 (r : ℕ) : Finset (Fin 2 → ZMod 2) := Finset.univ.filter fun c => ∀ i : Fin 2, r ≤ i.val → c i = 0

/-- `D₃ = 𝔽₃^{r₃}` inside `𝔽₃²`. -/
def S3 (r : ℕ) : Finset (Fin 2 → ZMod 3) := Finset.univ.filter fun c => ∀ i : Fin 2, r ≤ i.val → c i = 0

/-- `Q(c) = a₀c₀² + a₁c₁² + b c₀c₁`. -/
def Q3 (c : Cand) (x : Fin 2 → ZMod 3) : ZMod 3 :=
  c.2.2.1 * x 0 ^ 2 + c.2.2.2.1 * x 1 ^ 2 + c.2.2.2.2 * x 0 * x 1

/-- Normalisation and anisotropy of `Q` (the vector-level facts of `DiscForm.lean`). -/
def Valid (c : Cand) : Prop :=
  (c.r3 ≤ 1 → c.2.2.2.1 = 0 ∧ c.2.2.2.2 = 0) ∧ (c.r3 = 0 → c.2.2.1 = 0) ∧
  ∀ x ∈ S3 c.r3, Q3 c x = 0 → x = 0

instance (c : Cand) : Decidable (Valid c) := by unfold Valid; infer_instance

/-- The quadratic form on each component, as a real number mod 2. -/
noncomputable def q2 (x : Fin 2 → ZMod 2) : ℝ := if x = 0 then 0 else 1
noncomputable def q3 (c : Cand) (x : Fin 2 → ZMod 3) : ℝ := 2 * ((Q3 c x).val : ℝ) / 3

/-- The Gauss sum of `D₂ ⊕ D₃ ⊕ ⟨10/17⟩`. -/
noncomputable def gaussTotal (c : Cand) : ℂ :=
  ∑ x₂ ∈ S2 c.r2, ∑ x₃ ∈ S3 c.r3, ∑ x : ZMod 17,
    exp (π * ((q2 x₂ + q3 c x₃ + q17 x : ℝ) : ℂ) * I)

/-- `|D| = 2^{r₂} 3^{r₃} 17`. -/
def Cand.card (c : Cand) : ℕ := 2 ^ c.r2 * 3 ^ c.r3 * 17

/-- **Milgram's formula** for the candidate (rank 22): Gauss sum `= √|D| · e^{2πi·22/8}`. -/
def Milgram (c : Cand) : Prop :=
  gaussTotal c = (Real.sqrt c.card : ℂ) * exp (2 * π * I * (22 / 8))


/-- `⟨2/3⟩ ⊕ ⟨10/17⟩`, `det 51`. -/
def formI : Cand := (0, 1, (1, 0, 0))
/-- `V₂ ⊕ ⟨4/3⟩ ⊕ ⟨10/17⟩`, `det 204`. -/
def formII : Cand := (2, 1, (2, 0, 0))

/-! ## Integer data of the Gauss sums -/

/-- `g₂ = ∑_{D₂} (-1)^{q}`. -/
def g2Z (c : Cand) : ℤ := ∑ x ∈ S2 c.r2, if x = 0 then 1 else -1
/-- `2·Re g₃ = ∑ (2 if Q = 0 else -1)`. -/
def g3A (c : Cand) : ℤ := ∑ x ∈ S3 c.r3, if Q3 c x = 0 then 2 else -1
/-- `Im g₃ = (√3/2)·∑ (0, 1, -1 for Q = 0, 1, 2)`. -/
def g3B (c : Cand) : ℤ := ∑ x ∈ S3 c.r3, if Q3 c x = 0 then 0 else if Q3 c x = 1 then 1 else -1

/-- The integer form of Milgram's formula (given `Gauss17`). -/
def IntCond (c : Cand) : Prop :=
  g2Z c * g3A c = 0 ∧ 51 * (g2Z c * g3B c) ^ 2 = 4 * c.card ∧ 0 ≤ g2Z c * g3B c

instance (c : Cand) : Decidable (IntCond c) := by unfold IntCond; infer_instance

/-- **The finite classification** (kernel-checked exhaustion over all 243 candidates). -/
theorem classification_finite : ∀ c : Cand, Valid c → IntCond c → c = formI ∨ c = formII := by
  decide +kernel

theorem formI_valid : Valid formI ∧ IntCond formI := by decide +kernel
theorem formII_valid : Valid formII ∧ IntCond formII := by decide +kernel

/-! ## From the complex Gauss sum to the integer data -/

theorem exp_q2 (x : Fin 2 → ZMod 2) :
    exp (π * (q2 x : ℂ) * I) = ((if x = 0 then 1 else -1 : ℤ) : ℂ) := by
  unfold q2
  split_ifs <;> simp [exp_pi_mul_I]

/-- `ω`-values: `e^{πi·2k/3}` for `k = 0, 1, 2`. -/
theorem exp_q3 (k : ZMod 3) :
    exp (π * ((2 * (k.val : ℝ) / 3 : ℝ) : ℂ) * I) =
      ((if k = 0 then 2 else -1 : ℤ) : ℂ) / 2 +
        ((Real.sqrt 3 / 2 : ℝ) : ℂ) * ((if k = 0 then 0 else if k = 1 then 1 else -1 : ℤ) : ℂ) * I := by
  have hc : Real.cos (2 * π / 3) = -1 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; ring
  have hs : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have hc4 : Real.cos (4 * π / 3) = -1 / 2 := by
    rw [show 4 * π / 3 = π / 3 + π by ring, Real.cos_add_pi, Real.cos_pi_div_three]; ring
  have hs4 : Real.sin (4 * π / 3) = -(Real.sqrt 3 / 2) := by
    rw [show 4 * π / 3 = π / 3 + π by ring, Real.sin_add_pi, Real.sin_pi_div_three]
  have key : ∀ t : ℝ, exp (π * (t : ℂ) * I) = (Real.cos (π * t) : ℂ) + (Real.sin (π * t) : ℂ) * I := by
    intro t
    rw [show (π : ℂ) * (t : ℂ) * I = ((π * t : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I]
    rw [← ofReal_cos, ← ofReal_sin]
  rw [key]
  rcases (show ∀ k : ZMod 3, k = 0 ∨ k = 1 ∨ k = 2 by decide) k with rfl | rfl | rfl
  · simp
  · have h1 : (1 : ZMod 3).val = 1 := rfl
    have h10 : (1 : ZMod 3) ≠ 0 := by decide
    rw [h1]; simp only [h10, ↓reduceIte]
    rw [show π * (2 * ((1 : ℕ) : ℝ) / 3) = 2 * π / 3 by push_cast; ring, hc, hs]
    push_cast; ring
  · have h2 : (2 : ZMod 3).val = 2 := rfl
    have h20 : (2 : ZMod 3) ≠ 0 := by decide
    have h21 : (2 : ZMod 3) ≠ 1 := by decide
    rw [h2]; simp only [h20, h21, ↓reduceIte]
    rw [show π * (2 * ((2 : ℕ) : ℝ) / 3) = 4 * π / 3 by push_cast; ring, hc4, hs4]
    push_cast; ring

theorem gauss_factor (c : Cand) :
    gaussTotal c = (∑ x₂ ∈ S2 c.r2, exp (π * (q2 x₂ : ℂ) * I)) *
      (∑ x₃ ∈ S3 c.r3, exp (π * (q3 c x₃ : ℂ) * I)) * ∑ x : ZMod 17, exp (π * (q17 x : ℂ) * I) := by
  unfold gaussTotal
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x₂ _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x₃ _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← exp_add, ← exp_add]
  congr 1
  push_cast; ring

theorem g2_eq (c : Cand) : ∑ x₂ ∈ S2 c.r2, exp (π * (q2 x₂ : ℂ) * I) = (g2Z c : ℂ) := by
  simp only [exp_q2, g2Z]; push_cast; rfl

theorem g3_eq (c : Cand) : ∑ x₃ ∈ S3 c.r3, exp (π * (q3 c x₃ : ℂ) * I) =
    (g3A c : ℂ) / 2 + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * (g3B c : ℂ) * I := by
  have : ∀ x₃, exp (π * (q3 c x₃ : ℂ) * I) = _ := fun x₃ => exp_q3 (Q3 c x₃)
  simp only [q3] at this
  simp only [q3, this, Finset.sum_add_distrib, g3A, g3B, ← Finset.sum_div, ← Finset.mul_sum,
    ← Finset.sum_mul]
  push_cast; ring

theorem exp_milgram : exp (2 * π * I * (22 / 8)) = -I := by
  have : (2 * π * I * (22 / 8) : ℂ) = (11 : ℕ) * (π / 2 * I) := by push_cast; ring
  rw [this, exp_nat_mul, exp_pi_div_two_mul_I]
  rw [show (11 : ℕ) = 4 * 2 + 3 by norm_num, pow_add, pow_mul, I_pow_four]; simp [pow_succ]

/-- **Milgram ⇒ the integer condition** (given the 17-part Gauss sum). -/
theorem milgram_int (c : Cand) (hM : Milgram c) : IntCond c := by
  have h17 := gauss17
  unfold Milgram at hM
  rw [gauss_factor, g2_eq, g3_eq, h17, exp_milgram] at hM
  have hD : Real.sqrt (c.card : ℝ) = Real.sqrt 17 * Real.sqrt (2 ^ c.r2 * 3 ^ c.r3) := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; unfold Cand.card; push_cast; ring
  rw [hD] at hM
  have sD : Real.sqrt (2 ^ c.r2 * 3 ^ c.r3) * Real.sqrt (2 ^ c.r2 * 3 ^ c.r3) = 2 ^ c.r2 * 3 ^ c.r3 :=
    Real.mul_self_sqrt (by positivity)
  have hR0 : 0 ≤ Real.sqrt (2 ^ c.r2 * 3 ^ c.r3) := Real.sqrt_nonneg _
  generalize Real.sqrt (2 ^ c.r2 * 3 ^ c.r3) = R at hM sD hR0
  have hre := congrArg re hM
  have him := congrArg im hM
  simp [mul_re, mul_im, ofReal_re, ofReal_im] at hre him
  have s17 : 0 < Real.sqrt 17 := by positivity
  have s3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hA : g2Z c * g3A c = 0 := by rcases hre with h | h <;> simp [h]
  have hB : (g2Z c : ℝ) * g3B c * Real.sqrt 3 = 2 * R := by
    have : Real.sqrt 17 * ((g2Z c : ℝ) * g3B c * Real.sqrt 3 - 2 * R) = 0 := by
      linear_combination 2 * him
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h s17.ne'
    · linarith
  refine ⟨hA, ?_, ?_⟩
  · have h2 : ((g2Z c : ℝ) * g3B c) ^ 2 * 3 = 4 * (2 ^ c.r2 * 3 ^ c.r3) := by
      have := congrArg (fun t => t ^ 2) hB
      simp only [mul_pow] at this
      rw [sq (Real.sqrt 3), s3, sq R, sD] at this
      linarith
    have : (51 : ℝ) * ((g2Z c : ℝ) * g3B c) ^ 2 = 4 * (c.card : ℝ) := by
      unfold Cand.card; push_cast; linarith
    exact_mod_cast this
  · have hpos : 0 ≤ (g2Z c : ℝ) * g3B c * Real.sqrt 3 := by rw [hB]; positivity
    have s3p : 0 < Real.sqrt 3 := by positivity
    have : (0 : ℝ) ≤ (g2Z c : ℝ) * g3B c := by
      by_contra hneg; push Not at hneg; nlinarith
    exact_mod_cast this

/-- **Proposition `prop:forms`, classification** (Milgram's formula as hypothesis): a valid candidate that
satisfies Milgram's formula is form (I) or form (II). -/
theorem forms_classification (c : Cand) (hc : Valid c) (hM : Milgram c) :
    c = formI ∨ c = formII :=
  classification_finite c hc (milgram_int c hM)

/-- `det N = |D(N)| ∈ {51, 204}`. -/
theorem det_cases (c : Cand) (hc : Valid c) (hM : Milgram c) :
    c.card = 51 ∨ c.card = 204 := by
  rcases forms_classification c hc hM with rfl | rfl
  · left; decide
  · right; decide

/-- Both forms satisfy Milgram's formula (so the classification has exactly two members). -/
theorem milgram_of_int (c : Cand) (hI : IntCond c)
    (hsign : 0 < g2Z c * g3B c) : Milgram c := by
  obtain ⟨hA, hB, -⟩ := hI
  unfold Milgram
  rw [gauss_factor, g2_eq, g3_eq, gauss17, exp_milgram]
  have hD : Real.sqrt (c.card : ℝ) = Real.sqrt 17 * Real.sqrt (2 ^ c.r2 * 3 ^ c.r3) := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; unfold Cand.card; push_cast; ring
  rw [hD]
  have hA' : (g2Z c : ℝ) * g3A c = 0 := by exact_mod_cast hA
  have hB' : (51 : ℝ) * ((g2Z c : ℝ) * g3B c) ^ 2 = 4 * (2 ^ c.r2 * 3 ^ c.r3 * 17) := by
    have : ((51 * (g2Z c * g3B c) ^ 2 : ℤ) : ℝ) = ((4 * c.card : ℕ) : ℝ) := by exact_mod_cast hB
    unfold Cand.card at this; push_cast at this; linarith
  have hpos : (0 : ℝ) < (g2Z c : ℝ) * g3B c := by exact_mod_cast hsign
  have s3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have s3p : 0 < Real.sqrt 3 := by positivity
  have key : Real.sqrt (2 ^ c.r2 * 3 ^ c.r3) = (g2Z c : ℝ) * g3B c * Real.sqrt 3 / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    linear_combination (((g2Z c : ℝ) * g3B c) ^ 2 / 4) * s3 + (1 / 68 : ℝ) * hB'
  rw [key]
  apply Complex.ext
  · simp [mul_re, mul_im]
    exact mul_eq_zero.1 hA
  · simp [mul_re, mul_im]
    ring

theorem formI_milgram : Milgram formI :=
  milgram_of_int _ formI_valid.2 (by decide +kernel)

theorem formII_milgram : Milgram formII :=
  milgram_of_int _ formII_valid.2 (by decide +kernel)

end Srg154
