import Srg154.Certificates

/-!
# Items 3 and 4. Genus II: pins, Theorem A (frame identity) and Theorem B (7-design)

Setting (Proposition `prop:dict`): a real inner product space `E`, an additive subgroup `U` (the odd
unimodular lattice; only integrality and closure are used), vectors `w, u ∈ U` with
`w² = 51`, `u² = 7`, `⟨u,w⟩ = 15`.

The graph enters ONLY through two hypotheses (`adm_proj`, `adm_char`), which are the paper's
equation `(eq:adm)` composed with `(eq:projII)` and `Lemma test (b)`: for `v ∈ U` with
`n = v²`, `α = ⟨v,w⟩`, `β = ⟨v,u⟩` and `51n - α² ≠ 0` (i.e. `π(v) ≠ 0`), the pair
`(51n - α², 17β - 5α)` has a witness; for characteristic `η` the pair of `π(η)/2`,
`((51n - α²)/4, (17β - 5α)/2)`, has a witness.  (`HasWitness` is weaker than `Admissible`, so these
hypotheses are weaker than what the paper derives, and the theorems are correspondingly stronger.)

From these and the 521 kernel-checked certificates, Lean derives the pins (a)-(d) of Lemma `lem:pins`
(the Gram-determinant bounds are proved, not assumed).  Then:
* `theoremA`: the frame identity (Theorem `thm:frameid`, external input E3, taken as a HYPOTHESIS that
  is only required to hold when `U` is unit-free) forces `U` to have no roots;
* `theoremB`: the 7-design moments (external input E4 / Lemma `lem:design`, HYPOTHESIS, required only
  when `U` has no units and no roots) force `U` to have roots;
* `genusII_impossible`: hence no such configuration exists.
-/

namespace Srg154

open RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Gram determinant bound -/

/-- `det Gram(v,w,u) ≥ 0`, i.e. `7α² - 30αβ + 51β² ≤ 132 v²`. -/
theorem gram_bound (v w u : E) (hw : ⟪w, w⟫ = 51) (hu : ⟪u, u⟫ = 7) (huw : ⟪u, w⟫ = 15) :
    7 * ⟪v, w⟫ ^ 2 - 30 * ⟪v, w⟫ * ⟪v, u⟫ + 51 * ⟪v, u⟫ ^ 2 ≤ 132 * ⟪v, v⟫ := by
  set α := ⟪v, w⟫ with hα
  set β := ⟪v, u⟫ with hβ
  have hwu : ⟪w, u⟫ = 15 := by rw [real_inner_comm]; exact huw
  have hwv : ⟪w, v⟫ = α := by rw [real_inner_comm]
  have huv : ⟪u, v⟫ = β := by rw [real_inner_comm]
  have h := real_inner_self_nonneg (x := (132 : ℝ) • v - (7 * α - 15 * β) • w - (51 * β - 15 * α) • u)
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hw, hu,
    huw, hwu, hwv, huv, ← hα, ← hβ] at h
  nlinarith [h]

/-! ## The genus-II configuration -/

/-- `η` is characteristic in `U`. -/
def IsChar (U : AddSubgroup E) (η : E) : Prop :=
  η ∈ U ∧ ∀ v ∈ U, ∃ k : ℤ, ⟪η, v⟫ - ⟪v, v⟫ = 2 * k

/-- The data of Proposition `prop:dict` together with the graph hypothesis `(eq:adm)`. -/
structure Config (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  U : AddSubgroup E
  w : E
  u : E
  w_mem : w ∈ U
  u_mem : u ∈ U
  hw : ⟪w, w⟫ = 51
  hu : ⟪u, u⟫ = 7
  huw : ⟪u, w⟫ = 15
  integral : ∀ v ∈ U, ∀ v' ∈ U, ∃ k : ℤ, ⟪v, v'⟫ = k
  /-- `(eq:adm)` for `π(v)`, `v ∈ U` (via `(eq:projII)`). -/
  adm_proj : ∀ v ∈ U, ∀ n α β : ℤ, ⟪v, v⟫ = n → ⟪v, w⟫ = α → ⟪v, u⟫ = β →
    51 * n - α ^ 2 ≠ 0 → HasWitness (51 * n - α ^ 2) (17 * β - 5 * α)
  /-- `(eq:adm)` for `π(η)/2`, `η` characteristic (Lemma `test`(b), `(eq:projII)`). -/
  adm_char : ∀ η, IsChar U η → ∀ n α β : ℤ, ⟪η, η⟫ = n → ⟪η, w⟫ = α → ⟪η, u⟫ = β →
    ∀ m ℓ : ℤ, 4 * m = 51 * n - α ^ 2 → 2 * ℓ = 17 * β - 5 * α → m ≠ 0 → HasWitness m ℓ

namespace Config

variable (K : Config E)

theorem int_of_mem {v v' : E} (hv : v ∈ K.U) (hv' : v' ∈ K.U) : ∃ k : ℤ, ⟪v, v'⟫ = k :=
  K.integral v hv v' hv'

theorem gram (v : E) :
    7 * ⟪v, K.w⟫ ^ 2 - 30 * ⟪v, K.w⟫ * ⟪v, K.u⟫ + 51 * ⟪v, K.u⟫ ^ 2 ≤ 132 * ⟪v, v⟫ :=
  gram_bound v K.w K.u K.hw K.hu K.huw

/-- **Lemma `lem:pins`(a)**: `U` has no units. -/
theorem no_units : ∀ v ∈ K.U, ⟪v, v⟫ ≠ 1 := by
  intro v hv h1
  obtain ⟨α, hα⟩ := K.int_of_mem hv K.w_mem
  obtain ⟨β, hβ⟩ := K.int_of_mem hv K.u_mem
  -- Cauchy–Schwarz: α² ≤ 51
  have cs := real_inner_mul_inner_self_le v K.w
  rw [hα, h1, K.hw] at cs
  have hα2 : α ^ 2 ≤ 51 := by
    have : ((α ^ 2 : ℤ) : ℝ) ≤ 51 := by push_cast; nlinarith
    exact_mod_cast this
  have hb : -7 ≤ α ∧ α ≤ 7 := by constructor <;> nlinarith
  have hne : (51 : ℤ) * 1 - α ^ 2 ≠ 0 := by
    obtain ⟨h1, h2⟩ := hb
    interval_cases α <;> norm_num
  have hw := K.adm_proj v hv 1 α β (by rw [h1]; norm_num) hα hβ hne
  have hm : 51 * 1 - α ^ 2 ∈
      ({4, 16, 30, 36, 52, 60, 64, 70, 72, 76, 94, 2, 15, 26, 35, 42, 47, 50, 51} : Finset ℤ) := by
    obtain ⟨h1, h2⟩ := hb
    interval_cases α <;> decide
  exact forb_a _ hm _ hw

/-- **Lemma `lem:pins`(b)**: every root has `α(α - 3β) ≤ 1`, with equality only for `(α,β) = ±(1,0)`. -/
theorem root_pin (ρ : E) (hρ : ρ ∈ K.U) (h2 : ⟪ρ, ρ⟫ = 2) :
    ⟪ρ, K.w⟫ * (⟪ρ, K.w⟫ - 3 * ⟪ρ, K.u⟫) ≤ 1 ∧
    (⟪ρ, K.w⟫ * (⟪ρ, K.w⟫ - 3 * ⟪ρ, K.u⟫) = 1 → ⟪ρ, K.w⟫ ^ 2 = 1) := by
  obtain ⟨α, hα⟩ := K.int_of_mem hρ K.w_mem
  obtain ⟨β, hβ⟩ := K.int_of_mem hρ K.u_mem
  have hg := K.gram ρ
  rw [hα, hβ, h2] at hg
  rw [hα, hβ]
  have hG : 7 * α ^ 2 - 30 * α * β + 51 * β ^ 2 ≤ 264 := by
    have : ((7 * α ^ 2 - 30 * α * β + 51 * β ^ 2 : ℤ) : ℝ) ≤ 264 := by push_cast; linarith
    exact_mod_cast this
  have hα2 : α ^ 2 < 102 := by
    have : α ^ 2 ≤ 102 := by nlinarith [sq_nonneg (51 * β - 15 * α)]
    rcases this.lt_or_eq with h | h
    · exact h
    · exfalso
      have hb : -11 ≤ α ∧ α ≤ 11 := by constructor <;> nlinarith
      obtain ⟨h1, h2⟩ := hb
      interval_cases α <;> omega
  have hne : 51 * 2 - α ^ 2 ≠ 0 := by omega
  have hw := K.adm_proj ρ hρ 2 α β (by rw [h2]; norm_num) hα hβ hne
  -- the integer statement
  have key : α * (α - 3 * β) ≤ 1 ∧ (α * (α - 3 * β) = 1 → α ^ 2 = 1) := by
    by_contra hcon
    have hcon' : 1 ≤ α * (α - 3 * β) ∧ ¬ (α = 1 ∧ β = 0) ∧ ¬ (α = -1 ∧ β = 0) := by
      rcases not_and_or.1 hcon with h | h
      · refine ⟨by omega, ?_, ?_⟩ <;> rintro ⟨rfl, rfl⟩ <;> omega
      · push Not at h
        obtain ⟨h1, h2⟩ := h
        refine ⟨by omega, ?_, ?_⟩ <;> rintro ⟨rfl, rfl⟩ <;> simp at h2
    obtain ⟨h1, h3, h4⟩ := hcon'
    rcases lt_trichotomy α 0 with hneg | hz | hpos
    · -- flip signs
      have := forb_b (-α) (-β) (by omega) (by nlinarith) (by nlinarith) (by nlinarith)
        (by intro e; simp only [Prod.mk.injEq] at e; exact h4 ⟨by omega, by omega⟩)
      apply this
      have e1 : (102 : ℤ) - (-α) ^ 2 = 51 * 2 - α ^ 2 := by ring
      have e2 : 17 * -β - 5 * -α = -(17 * β - 5 * α) := by ring
      rw [e1, e2]; exact hw.neg
    · subst hz; simp at h1
    · have := forb_b α β (by omega) hG hα2 h1
        (by intro e; simp only [Prod.mk.injEq] at e; exact h3 ⟨e.1, e.2⟩)
      apply this
      have e1 : (102 : ℤ) - α ^ 2 = 51 * 2 - α ^ 2 := by ring
      rw [e1]; exact hw
  obtain ⟨k1, k2⟩ := key
  refine ⟨by exact_mod_cast (show ((α * (α - 3 * β) : ℤ) : ℝ) ≤ 1 by exact_mod_cast k1), ?_⟩
  intro he
  have : α * (α - 3 * β) = 1 := by exact_mod_cast (show ((α * (α - 3 * β) : ℤ) : ℝ) = 1 by
    push_cast; linarith)
  exact_mod_cast k2 this

/-- Characteristic vectors have odd `α`, `β`. -/
theorem char_odd {η : E} (hη : IsChar K.U η) :
    ∃ α β : ℤ, ⟪η, K.w⟫ = α ∧ ⟪η, K.u⟫ = β ∧ Odd α ∧ Odd β := by
  obtain ⟨α, hα⟩ := K.int_of_mem hη.1 K.w_mem
  obtain ⟨β, hβ⟩ := K.int_of_mem hη.1 K.u_mem
  obtain ⟨k1, hk1⟩ := hη.2 K.w K.w_mem
  obtain ⟨k2, hk2⟩ := hη.2 K.u K.u_mem
  rw [hα, K.hw] at hk1
  rw [hβ, K.hu] at hk2
  refine ⟨α, β, hα, hβ, ⟨k1 + 25, ?_⟩, ⟨k2 + 3, ?_⟩⟩
  · have : ((α : ℤ) : ℝ) = ((2 * (k1 + 25) + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : ((β : ℤ) : ℝ) = ((2 * (k2 + 3) + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-- **Lemma `lem:pins`(c)**: a characteristic `η` of norm 7 has `3αβ - α² ≥ 2`, and
`3αβ - α² = 2` forces `α² = 1`. (The case `η = ±u`, where `3αβ - α² = 90`, is included.) -/
theorem char_pin (η : E) (hη : IsChar K.U η) (h7 : ⟪η, η⟫ = 7) :
    2 ≤ 3 * ⟪η, K.w⟫ * ⟪η, K.u⟫ - ⟪η, K.w⟫ ^ 2 ∧
    (3 * ⟪η, K.w⟫ * ⟪η, K.u⟫ - ⟪η, K.w⟫ ^ 2 = 2 → ⟪η, K.w⟫ ^ 2 = 1) := by
  obtain ⟨α, β, hα, hβ, hαo, hβo⟩ := K.char_odd hη
  have hg := K.gram η
  rw [hα, hβ, h7] at hg
  rw [hα, hβ]
  have hG : 7 * α ^ 2 - 30 * α * β + 51 * β ^ 2 ≤ 924 := by
    have : ((7 * α ^ 2 - 30 * α * β + 51 * β ^ 2 : ℤ) : ℝ) ≤ 924 := by push_cast; linarith
    exact_mod_cast this
  have hα2 : α ^ 2 < 357 := by
    have : α ^ 2 ≤ 357 := by nlinarith [sq_nonneg (51 * β - 15 * α)]
    rcases this.lt_or_eq with h | h
    · exact h
    · exfalso
      have hb : -19 ≤ α ∧ α ≤ 19 := by constructor <;> nlinarith
      obtain ⟨h1, h2⟩ := hb
      interval_cases α <;> omega
  obtain ⟨a, ha⟩ := hαo
  obtain ⟨b, hb⟩ := hβo
  -- the integers m, ℓ of π(η)/2
  have hm : 4 * ((357 - α ^ 2) / 4) = 51 * 7 - α ^ 2 := by
    subst ha; ring_nf; omega
  have hl : 2 * ((17 * β - 5 * α) / 2) = 17 * β - 5 * α := by omega
  have hm0 : (357 - α ^ 2) / 4 ≠ 0 := by omega
  have hw := K.adm_char η hη 7 α β (by rw [h7]; norm_num) hα hβ _ _ hm hl hm0
  have key : 2 ≤ 3 * α * β - α ^ 2 ∧ (3 * α * β - α ^ 2 = 2 → α ^ 2 = 1) := by
    -- reduce to α ≥ 1
    have main : ∀ α β : ℤ, 1 ≤ α → Odd α → Odd β → 7 * α ^ 2 - 30 * α * β + 51 * β ^ 2 ≤ 924 →
        α ^ 2 < 357 → HasWitness ((357 - α ^ 2) / 4) ((17 * β - 5 * α) / 2) →
        2 ≤ 3 * α * β - α ^ 2 ∧ (3 * α * β - α ^ 2 = 2 → α ^ 2 = 1) := by
      intro α β h1 hao hbo hG hα2 hw
      by_cases e157 : α = 15 ∧ β = 7
      · obtain ⟨rfl, rfl⟩ := e157; norm_num
      by_cases hgood : (α = 1 ∨ α = 3) ∧ 2 ≤ 3 * α * β - α ^ 2
      · refine ⟨hgood.2, fun he => ?_⟩
        rcases hgood.1 with rfl | rfl
        · norm_num
        · omega
      · exfalso
        obtain ⟨a, ha⟩ := hao
        exact forb_c α β _ _ h1 ⟨a, ha⟩ hbo hG hα2
          (by intro e; simp only [Prod.mk.injEq] at e; exact e157 e) hgood
          (by subst ha; ring_nf; omega) (by obtain ⟨b, hb⟩ := hbo; omega) hw
    rcases lt_or_gt_of_ne (show α ≠ 0 by omega) with hneg | hpos
    · have := main (-α) (-β) (by omega) ⟨-a - 1, by omega⟩ ⟨-b - 1, by omega⟩ (by nlinarith)
        (by nlinarith) (by
          have e1 : (357 - (-α) ^ 2) / 4 = (357 - α ^ 2) / 4 := by ring_nf
          have e2 : (17 * -β - 5 * -α) / 2 = -((17 * β - 5 * α) / 2) := by omega
          rw [e1, e2]; exact hw.neg)
      have e3 : 3 * -α * -β - (-α) ^ 2 = 3 * α * β - α ^ 2 := by ring
      rw [e3] at this
      exact ⟨this.1, fun h => by have := this.2 h; nlinarith⟩
    · exact main α β (by omega) ⟨a, ha⟩ ⟨b, hb⟩ hG hα2 hw
  obtain ⟨k1, k2⟩ := key
  refine ⟨by exact_mod_cast (show (2 : ℝ) ≤ ((3 * α * β - α ^ 2 : ℤ) : ℝ) by exact_mod_cast k1), ?_⟩
  intro he
  have : 3 * α * β - α ^ 2 = 2 := by
    exact_mod_cast (show ((3 * α * β - α ^ 2 : ℤ) : ℝ) = 2 by push_cast; linarith)
  exact_mod_cast k2 this

/-- **Lemma `lem:pins`(d)**: if `U` has no roots, every `v ∈ U` of norm 3 has `|β| ≤ 2` or
`⟨v, 3w - 7u⟩ = 0`. -/
theorem norm3_pin (hroot : ∀ v ∈ K.U, ⟪v, v⟫ ≠ 2) (v : E) (hv : v ∈ K.U) (h3 : ⟪v, v⟫ = 3) :
    ∃ β : ℤ, ⟪v, K.u⟫ = β ∧ (-2 ≤ β ∧ β ≤ 2 ∨ ⟪v, (3 : ℝ) • K.w - (7 : ℝ) • K.u⟫ = 0) := by
  obtain ⟨α, hα⟩ := K.int_of_mem hv K.w_mem
  obtain ⟨β, hβ⟩ := K.int_of_mem hv K.u_mem
  refine ⟨β, hβ, ?_⟩
  have huv : ⟪K.u, v⟫ = β := by rw [real_inner_comm]; exact hβ
  -- Cauchy–Schwarz: β² ≤ 21
  have cs := real_inner_mul_inner_self_le v K.u
  rw [hβ, h3, K.hu] at cs
  have hβ2 : β ^ 2 ≤ 21 := by
    have : ((β ^ 2 : ℤ) : ℝ) ≤ 21 := by push_cast; nlinarith
    exact_mod_cast this
  have hb : -4 ≤ β ∧ β ≤ 4 := by constructor <;> nlinarith
  have hinner : ⟪v, (3 : ℝ) • K.w - (7 : ℝ) • K.u⟫ = 3 * α - 7 * β := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, hα, hβ]
  -- β = ±4 gives a root u ∓ v
  have not4 : β ≠ 4 := by
    intro e
    apply hroot (K.u - v) (K.U.sub_mem K.u_mem hv)
    rw [inner_sub_left, inner_sub_right, inner_sub_right, K.hu, h3, huv, hβ, e]; norm_num
  have notm4 : β ≠ -4 := by
    intro e
    apply hroot (K.u + v) (K.U.add_mem K.u_mem hv)
    rw [inner_add_left, inner_add_right, inner_add_right, K.hu, h3, huv, hβ, e]; norm_num
  have hg := K.gram v
  rw [hα, hβ, h3] at hg
  -- β = ±3
  have three : ∀ α : ℤ, 7 * α ^ 2 - 90 * α + 459 ≤ 396 → HasWitness (51 * 3 - α ^ 2) (17 * 3 - 5 * α) →
      α = 7 := by
    intro α hG hw
    have h1 : 1 ≤ α := by nlinarith
    have h2 : α ≤ 12 := by nlinarith
    by_contra h7
    exact forb_d α h1 h2 h7 (by
      have e1 : (153 : ℤ) - α ^ 2 = 51 * 3 - α ^ 2 := by ring
      have e2 : (51 : ℤ) - 5 * α = 17 * 3 - 5 * α := by ring
      rw [e1, e2]; exact hw)
  have hne : ∀ α : ℤ, 51 * 3 - α ^ 2 ≠ 0 := by
    intro α h
    have hb : -13 ≤ α ∧ α ≤ 13 := by constructor <;> nlinarith
    obtain ⟨h1, h2⟩ := hb
    interval_cases α <;> omega
  have hw := K.adm_proj v hv 3 α β (by rw [h3]; norm_num) hα hβ (hne α)
  rcases (show β = -4 ∨ β = -3 ∨ (-2 ≤ β ∧ β ≤ 2) ∨ β = 3 ∨ β = 4 by omega) with
    e | e | e | e | e
  · exact absurd e notm4
  · right
    rw [hinner]
    subst e
    have hG : 7 * (-α) ^ 2 - 90 * (-α) + 459 ≤ 396 := by
      have : ((7 * (-α) ^ 2 - 90 * (-α) + 459 : ℤ) : ℝ) ≤ 396 := by push_cast at hg ⊢; nlinarith
      exact_mod_cast this
    have := three (-α) hG (by
      have e1 : (51 : ℤ) * 3 - (-α) ^ 2 = 51 * 3 - α ^ 2 := by ring
      have e2 : (17 : ℤ) * 3 - 5 * -α = -(17 * -3 - 5 * α) := by ring
      rw [e1, e2]; exact hw.neg)
    have : α = -7 := by omega
    subst this; norm_num
  · left; exact e
  · right
    rw [hinner]
    subst e
    have hG : 7 * α ^ 2 - 90 * α + 459 ≤ 396 := by
      have : ((7 * α ^ 2 - 90 * α + 459 : ℤ) : ℝ) ≤ 396 := by push_cast at hg ⊢; nlinarith
      exact_mod_cast this
    have := three α hG hw
    subst this; norm_num
  · exact absurd e not4

end Config

/-! ## Theorem A: the frame identity excludes roots -/

/-- The frame identity data of Theorem `thm:frameid` (external input E3), for a set `R` of roots containing
one of each pair `±ρ` and a set `C` of characteristic vectors of norm 7. -/
def FrameIdentity (U : AddSubgroup E) (R C : Finset E) : Prop :=
  (∀ ρ ∈ R, ρ ∈ U ∧ ⟪ρ, ρ⟫ = 2) ∧
  (∀ v ∈ U, ⟪v, v⟫ = 2 → v ∈ R ∨ -v ∈ R) ∧
  (∀ η ∈ C, IsChar U η ∧ ⟪η, η⟫ = 7) ∧
  R.card = 2 * C.card ∧
  ∀ x x' : E, ∑ η ∈ C, ⟪η, x⟫ * ⟪η, x'⟫ + 4 * ∑ ρ ∈ R, ⟪ρ, x⟫ * ⟪ρ, x'⟫ =
    (C.card : ℝ) * ⟪x, x'⟫

/-- **Theorem `thm:A`.** If the frame identity holds for unit-free `U` (hypothesis E3), then `U` has no
roots. Only the evaluations at `(w,w)` and `(u,w)` and the pins (b), (c) are used. -/
theorem theoremA (K : Config E)
    (frame : (∀ v ∈ K.U, ⟪v, v⟫ ≠ 1) → ∃ R C : Finset E, FrameIdentity K.U R C) :
    ∀ v ∈ K.U, ⟪v, v⟫ ≠ 2 := by
  obtain ⟨R, C, hR, hRall, hC, hcard, hid⟩ := frame K.no_units
  set c := (C.card : ℝ) with hc
  have hww := hid K.w K.w
  have huw := hid K.u K.w
  rw [K.hw] at hww
  rw [K.huw] at huw
  -- abbreviations
  set αR : E → ℝ := fun ρ => ⟪ρ, K.w⟫
  set βR : E → ℝ := fun ρ => ⟪ρ, K.u⟫
  have hRc : (R.card : ℝ) = 2 * c := by rw [hcard]; push_cast; ring
  -- combined identity (eq:combined)
  have comb : 4 * ∑ ρ ∈ R, αR ρ * (αR ρ - 3 * βR ρ) =
      6 * c + ∑ η ∈ C, (3 * αR η * βR η - αR η ^ 2) := by
    have e1 : ∑ ρ ∈ R, αR ρ * (αR ρ - 3 * βR ρ) =
        ∑ ρ ∈ R, ⟪ρ, K.w⟫ * ⟪ρ, K.w⟫ - 3 * ∑ ρ ∈ R, ⟪ρ, K.u⟫ * ⟪ρ, K.w⟫ := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp only [αR, βR]; ring
    have e2 : ∑ η ∈ C, (3 * αR η * βR η - αR η ^ 2) =
        3 * ∑ η ∈ C, ⟪η, K.u⟫ * ⟪η, K.w⟫ - ∑ η ∈ C, ⟪η, K.w⟫ * ⟪η, K.w⟫ := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun η _ => ?_
      simp only [αR, βR]; ring
    rw [e1, e2]; linarith
  -- pins
  have rp : ∀ ρ ∈ R, αR ρ * (αR ρ - 3 * βR ρ) ≤ 1 := fun ρ hρ =>
    (K.root_pin ρ (hR ρ hρ).1 (hR ρ hρ).2).1
  have cp : ∀ η ∈ C, 2 ≤ 3 * αR η * βR η - αR η ^ 2 := fun η hη =>
    (K.char_pin η (hC η hη).1 (hC η hη).2).1
  have sR : ∑ ρ ∈ R, αR ρ * (αR ρ - 3 * βR ρ) ≤ ∑ ρ ∈ R, (1 : ℝ) := Finset.sum_le_sum rp
  have sC : ∑ η ∈ C, (2 : ℝ) ≤ ∑ η ∈ C, (3 * αR η * βR η - αR η ^ 2) := Finset.sum_le_sum cp
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at sR sC
  rw [hRc] at sR
  -- equality throughout
  have eqR : ∑ ρ ∈ R, αR ρ * (αR ρ - 3 * βR ρ) = ∑ ρ ∈ R, (1 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hRc]; linarith
  have eqC : ∑ η ∈ C, (2 : ℝ) = ∑ η ∈ C, (3 * αR η * βR η - αR η ^ 2) := by
    simp only [Finset.sum_const, nsmul_eq_mul]; rw [← hc]; linarith
  have eachR := (Finset.sum_eq_sum_iff_of_le rp).1 eqR
  have eachC := (Finset.sum_eq_sum_iff_of_le cp).1 eqC
  have aR : ∀ ρ ∈ R, ⟪ρ, K.w⟫ * ⟪ρ, K.w⟫ = 1 := fun ρ hρ => by
    have := (K.root_pin ρ (hR ρ hρ).1 (hR ρ hρ).2).2 (eachR ρ hρ); nlinarith
  have aC : ∀ η ∈ C, ⟪η, K.w⟫ * ⟪η, K.w⟫ = 1 := fun η hη => by
    have := (K.char_pin η (hC η hη).1 (hC η hη).2).2 (eachC η hη).symm; nlinarith
  rw [Finset.sum_congr rfl aR, Finset.sum_congr rfl aC] at hww
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hww
  rw [hRc, ← hc] at hww
  have hc0 : c = 0 := by linarith
  have hR0 : R.card = 0 := by
    have : (R.card : ℝ) = 0 := by rw [hRc, hc0]; ring
    exact_mod_cast this
  intro v hv h2
  rcases hRall v hv h2 with h | h <;> simp [Finset.card_eq_zero.1 hR0] at h

/-! ## Theorem B: the 7-design excludes the rootless case -/

/-- The moment identities of Lemma `lem:design` for a finite set `Ψ` (external input E4). -/
def DesignMoments (Ψ : Finset E) : Prop :=
  (∀ x x' : E, ∑ v ∈ Ψ, ⟪v, x⟫ * ⟪v, x'⟫ = 600 * ⟪x, x'⟫) ∧
  (∀ x x' : E, ∑ v ∈ Ψ, ⟪v, x⟫ ^ 3 * ⟪v, x'⟫ = 216 * ⟪x, x⟫ * ⟪x, x'⟫) ∧
  (∀ x x' : E, ∑ v ∈ Ψ, ⟪v, x⟫ ^ 5 * ⟪v, x'⟫ = 120 * ⟪x, x⟫ ^ 2 * ⟪x, x'⟫)

/-- **Theorem `thm:B`.** If, for unit-free rootless `U`, the norm-3 vectors carry the 7-design moments
(hypothesis E4), then `U` has roots. -/
theorem theoremB (K : Config E)
    (design : (∀ v ∈ K.U, ⟪v, v⟫ ≠ 1) → (∀ v ∈ K.U, ⟪v, v⟫ ≠ 2) →
      ∃ Ψ : Finset E, (∀ v ∈ Ψ, v ∈ K.U ∧ ⟪v, v⟫ = 3) ∧ DesignMoments Ψ) :
    ∃ v ∈ K.U, ⟪v, v⟫ = 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨Ψ, hΨ, m1, m3, m5⟩ := design K.no_units hcon
  set h : E := (3 : ℝ) • K.w - (7 : ℝ) • K.u
  have huh : ⟪K.u, h⟫ = -4 := by
    simp only [h, inner_sub_right, real_inner_smul_right, K.hu, K.huw]; norm_num
  -- F vanishes on Ψ
  have hF : ∀ v ∈ Ψ, (⟪v, K.u⟫ ^ 5 - 5 * ⟪v, K.u⟫ ^ 3 + 4 * ⟪v, K.u⟫) * ⟪v, h⟫ = 0 := by
    intro v hv
    obtain ⟨β, hβ, hpin⟩ := K.norm3_pin hcon v (hΨ v hv).1 (hΨ v hv).2
    rcases hpin with ⟨b1, b2⟩ | h0
    · rw [hβ]
      have : (β : ℝ) ^ 5 - 5 * (β : ℝ) ^ 3 + 4 * β = 0 := by
        interval_cases β <;> norm_num
      rw [this, zero_mul]
    · rw [h0, mul_zero]
  have hsum0 : ∑ v ∈ Ψ, (⟪v, K.u⟫ ^ 5 - 5 * ⟪v, K.u⟫ ^ 3 + 4 * ⟪v, K.u⟫) * ⟪v, h⟫ = 0 :=
    Finset.sum_eq_zero hF
  have hsplit : ∑ v ∈ Ψ, (⟪v, K.u⟫ ^ 5 - 5 * ⟪v, K.u⟫ ^ 3 + 4 * ⟪v, K.u⟫) * ⟪v, h⟫ =
      ∑ v ∈ Ψ, ⟪v, K.u⟫ ^ 5 * ⟪v, h⟫ - 5 * ∑ v ∈ Ψ, ⟪v, K.u⟫ ^ 3 * ⟪v, h⟫ +
        4 * ∑ v ∈ Ψ, ⟪v, K.u⟫ * ⟪v, h⟫ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hsplit, m5, m3, m1, K.hu, huh] at hsum0
  norm_num at hsum0

/-- **Genus II is impossible** (Theorems A and B together). -/
theorem genusII_impossible (K : Config E)
    (frame : (∀ v ∈ K.U, ⟪v, v⟫ ≠ 1) → ∃ R C : Finset E, FrameIdentity K.U R C)
    (design : (∀ v ∈ K.U, ⟪v, v⟫ ≠ 1) → (∀ v ∈ K.U, ⟪v, v⟫ ≠ 2) →
      ∃ Ψ : Finset E, (∀ v ∈ Ψ, v ∈ K.U ∧ ⟪v, v⟫ = 3) ∧ DesignMoments Ψ) : False := by
  obtain ⟨v, hv, h2⟩ := theoremB K design
  exact theoremA K frame v hv h2

end Srg154
