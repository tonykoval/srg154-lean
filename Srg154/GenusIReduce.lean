import Srg154.GenusI

/-!
# Genus I: the reduction to `A₁²⁴` coordinates (Lemma `lem:A1`, first lines of Theorem `thm:genusI`)

`GenusI.lean` proves Theorem `thm:genusI` in normalised coordinates (`r = √2 e₀`, so `x₀ = 1`).  Here:

* `lemA1_geom`: **Lemma `lem:A1` in any real inner product space**: if `r² = 2`, `⟨r,f⟩ = 1`, `f² = 26`,
  `ρ` is a root with integral `α = ⟨ρ,r⟩`, `β = ⟨ρ,f⟩`, `π(ρ) ≠ 0`, and `(eq:adm)` holds for `π(ρ)`,
  then `α = 0` (so `r` spans an `A₁` component) and `β ∈ {0, ±1, ±3}`.
* `A1_24_roots`: the roots of `A₁²⁴ = {v/√2 : v ≡ codeword (mod 2)}` are exactly `±√2 eᵢ`, from the Golay
  weights `0, 8, 12, 16, 24` alone (a word of weight `≤ 4` would be needed otherwise).
* `genusI_impossible_general`: Theorem `thm:genusI` for an ARBITRARY root `r = ρ/√2` of the model and any
  `f = x/√2` with `⟨r,f⟩ = 1`, `f² = 26`: the coordinate change (a transposition and a global sign, under
  which the code is replaced by its image, with the same weights) is carried out in Lean and reduces to
  `genusI_impossible`.  This removes the normalisation `r = √2 e₀` from the hypotheses; E2 itself
  (`X ≅ A₁²⁴`, the Golay code weights) remains a hypothesis.
-/

namespace Srg154

open RealInnerProductSpace

/-- **Lemma `lem:A1`, geometric form.** -/
theorem lemA1_geom {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (r f ρ : E)
    (hr : ⟪r, r⟫ = 2) (hrf : ⟪r, f⟫ = 1) (hf : ⟪f, f⟫ = 26) (hρ : ⟪ρ, ρ⟫ = 2) (α β : ℤ)
    (hα : ⟪ρ, r⟫ = α) (hβ : ⟪ρ, f⟫ = β) (hπ : projI r f ρ ≠ 0)
    (adm : ∀ m : ℤ, (m : ℝ) = 51 * ⟪projI r f ρ, projI r f ρ⟫ → ∃ ℓ, HasWitness m ℓ) :
    α = 0 ∧ (β = 0 ∨ β = 1 ∨ β = -1 ∨ β = 3 ∨ β = -3) := by
  obtain ⟨-, -, h51⟩ := projI_spec r f ρ hr hrf hf
  rw [hρ, hα, hβ] at h51
  have hpos : 0 < ⟪projI r f ρ, projI r f ρ⟫ := real_inner_self_pos.2 hπ
  have hm : (0 : ℝ) < ((102 - (26 * α ^ 2 - 2 * α * β + 2 * β ^ 2) : ℤ) : ℝ) := by
    push_cast; linarith
  refine lemmaA1_arith α β (by exact_mod_cast hm) (adm _ ?_)
  push_cast; linarith

/-- **The roots of `A₁²⁴`** are `±√2 eᵢ` (doubled coordinates: `±2 eᵢ`), from the code weights. -/
theorem A1_24_roots (𝒢 : Set (Fin 24 → ZMod 2))
    (hwt : ∀ c ∈ 𝒢, c ≠ 0 → wt c ∈ ({8, 12, 16, 24} : Finset ℕ))
    (ρ : Fin 24 → ℤ) (hρG : mod2 ρ ∈ 𝒢) (hρ : dot ρ ρ = 4) :
    ∃ i : Fin 24, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ j, ρ j = if j = i then 2 * ε else 0 := by
  have hsum : ∑ j, ρ j ^ 2 = 4 := by rw [← hρ]; simp [dot, sq]
  -- all entries are even
  have hev : mod2 ρ = 0 := by
    by_contra hne
    have hw := hwt _ hρG hne
    have hle : wt (mod2 ρ) ≤ 4 := by
      have : ∀ j, (if mod2 ρ j ≠ 0 then 1 else 0 : ℤ) ≤ ρ j ^ 2 := by
        intro j
        split_ifs with h
        · have : ρ j ≠ 0 := by intro h0; apply h; simp [mod2, h0]
          have := sq_pos_of_ne_zero this
          omega
        · positivity
      have hs := Finset.sum_le_sum (s := Finset.univ) fun j _ => this j
      rw [hsum, Finset.sum_boole] at hs
      unfold wt
      exact_mod_cast hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    omega
  have heven : ∀ j, ∃ t, ρ j = 2 * t := by
    intro j
    have h := congrFun hev j
    simp only [mod2, Pi.zero_apply] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h
  -- some entry is nonzero
  obtain ⟨i, hi⟩ : ∃ i, ρ i ≠ 0 := by
    by_contra h; push Not at h; simp [h] at hsum
  obtain ⟨t, ht⟩ := heven i
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => ρ j ^ 2) (Finset.mem_univ i)
  rw [hsum] at hsplit
  have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i, ρ j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht; exact hi ht
  have hti : ρ i ^ 2 = 4 := by
    have : 1 ≤ t ^ 2 := by have := sq_pos_of_ne_zero ht0; omega
    have h4 : ρ i ^ 2 = 4 * t ^ 2 := by rw [ht]; ring
    omega
  have hzero : ∑ j ∈ Finset.univ.erase i, ρ j ^ 2 = 0 := by omega
  have hz : ∀ j ∈ Finset.univ.erase i, ρ j ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 hzero
  have htt : t = 1 ∨ t = -1 := by
    have : t ^ 2 = 1 := by rw [ht] at hti; nlinarith
    have hb : -1 ≤ t ∧ t ≤ 1 := by constructor <;> nlinarith
    omega
  refine ⟨i, t, htt, fun j => ?_⟩
  split_ifs with hj
  · subst hj; exact ht
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (hz j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩))

/-- `51 π(v)²` for a general root `r = ρ/√2` and `f = x/√2` (doubled coordinates). -/
noncomputable def mIgen (ρ x v : Fin 24 → ℤ) : ℚ :=
  51 * ((dot v v : ℚ) / 2) -
    (26 * ((dot v ρ : ℚ) / 2) ^ 2 - 2 * ((dot v ρ : ℚ) / 2) * ((dot v x : ℚ) / 2) +
      2 * ((dot v x : ℚ) / 2) ^ 2)

/-- **Theorem `thm:genusI` for an arbitrary root `r` of `A₁²⁴`** (E2 as hypothesis: the model and the code
weights). -/
theorem genusI_impossible_general (𝒢 : Set (Fin 24 → ZMod 2)) (h0 : (0 : Fin 24 → ZMod 2) ∈ 𝒢)
    (hwt : ∀ c ∈ 𝒢, c ≠ 0 → wt c ∈ ({8, 12, 16, 24} : Finset ℕ))
    (ρ x : Fin 24 → ℤ) (hρG : mod2 ρ ∈ 𝒢) (hρ : dot ρ ρ = 4)
    (hxG : mod2 x ∈ 𝒢) (hρx : dot ρ x = 2) (hxn : dot x x = 52)
    (adm : ∀ v : Fin 24 → ℤ, mod2 v ∈ 𝒢 → ∀ m : ℤ, (m : ℚ) = mIgen ρ x v → m ≠ 0 → ∃ ℓ, HasWitness m ℓ) :
    False := by
  obtain ⟨i, ε, hε, hρi⟩ := A1_24_roots 𝒢 hwt ρ hρG hρ
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε2 : (ε : ZMod 2) = 1 := by rcases hε with rfl | rfl <;> decide
  set σ : Equiv.Perm (Fin 24) := Equiv.swap 0 i with hσ
  have hσσ : ∀ j, σ (σ j) = j := fun j => Equiv.swap_apply_self _ _ _
  let T : (Fin 24 → ℤ) → (Fin 24 → ℤ) := fun v j => ε * v (σ j)
  have hTT : ∀ v, T (T v) = v := by
    intro v; funext j; simp only [T, hσσ, ← mul_assoc, hεε, one_mul]
  have hdotT : ∀ v w, dot (T v) (T w) = dot v w := by
    intro v w
    simp only [dot, T]
    rw [← Equiv.sum_comp σ (fun j => v j * w j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination (v (σ j) * w (σ j)) * hεε
  have hdotT' : ∀ v w, dot (T v) w = dot v (T w) := by
    intro v w
    conv_lhs => rw [← hTT w]
    rw [hdotT]
  have hmodT : ∀ v, mod2 (T v) = fun j => mod2 v (σ j) := by
    intro v; funext j; simp [mod2, T, hε2]
  let 𝒢' : Set (Fin 24 → ZMod 2) := {c | (fun j => c (σ j)) ∈ 𝒢}
  have hwtσ : ∀ c : Fin 24 → ZMod 2, wt (fun j => c (σ j)) = wt c := by
    intro c
    unfold wt
    apply Finset.card_bij (fun j _ => σ j)
    · intro j hj; simpa using hj
    · intro a _ b _ h; exact σ.injective h
    · intro b hb; exact ⟨σ b, by simpa [hσσ] using hb, hσσ b⟩
  have h0' : (0 : Fin 24 → ZMod 2) ∈ 𝒢' := by
    show (fun j => (0 : Fin 24 → ZMod 2) (σ j)) ∈ 𝒢; exact h0
  have hwt' : ∀ c ∈ 𝒢', c ≠ 0 → wt c ∈ ({8, 12, 16, 24} : Finset ℕ) := by
    intro c hc hne
    rw [← hwtσ c]
    refine hwt _ hc fun h => hne ?_
    funext j; have := congrFun h (σ j); simpa [hσσ] using this
  have hTρ : T ρ = fun j => if j = 0 then 2 else 0 := by
    funext j
    simp only [T, hρi]
    by_cases hj : j = 0
    · subst hj
      have : σ 0 = i := Equiv.swap_apply_left _ _
      simp only [this, ite_true]; linear_combination 2 * hεε
    · have : σ j ≠ i := by
        intro h; apply hj; have := congrArg σ h; rwa [hσσ, Equiv.swap_apply_right] at this
      simp [this, hj]
  set x' := T x with hx'
  have hx'G : mod2 x' ∈ 𝒢' := by
    show (fun j => mod2 x' (σ j)) ∈ 𝒢
    rw [hx', hmodT]; simpa [hσσ] using hxG
  have hx'0 : x' 0 = 1 := by
    have h1 : dot (T ρ) x' = 2 := by rw [hx', hdotT, hρx]
    rw [hTρ] at h1
    simp [dot] at h1
    omega
  have hx'n : dot x' x' = 52 := by rw [hx', hdotT, hxn]
  refine genusI_impossible 𝒢' h0' hwt' x' hx'G hx'0 hx'n ?_
  intro v' hv' m hm hm0
  refine adm (T v') ?_ m ?_ hm0
  · rw [hmodT]; exact hv'
  · rw [hm]
    have e1 : dot (T v') (T v') = dot v' v' := hdotT _ _
    have e2 : dot (T v') x = dot v' x' := by rw [hdotT', hx']
    have e3 : dot (T v') ρ = 2 * v' 0 := by
      rw [hdotT', hTρ]; simp [dot]; ring
    unfold mI mIgen
    rw [e1, e2, e3]
    push_cast; ring

end Srg154
