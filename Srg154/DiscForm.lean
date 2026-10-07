import Srg154.VertexLattice

/-!
# Proposition `prop:forms`: the structure of `D(N) = N^#/N`, at the level of vectors

For a maximal even overlattice `N` (`MaxEven`) of the vertex lattice of an srg(154,72,26,40) we prove, from the
graph alone, every step of the proof of Proposition `prop:forms` that precedes Milgram's formula, phrased for
representatives `x ∈ N^#` (so no quotient group has to be built):

* `MaxEven.primary_decomp`: `x = 51x + 34x - 84x` with `2·51x, 3·34x, 17·(-84x) ∈ N`, i.e.
  `D(N) = D₂ ⊕ D₃ ⊕ D₁₇`; `MaxEven.coprime_orth`: the components are orthogonal (`⟨x,x'⟩ ∈ ℤ`).
* `MaxEven.d17_cyclic`: `D₁₇ = ⟨ȳ⟩`: `17x ∈ N ⇒ x + 5ℓy ∈ N`; `y_sq_mod`: `q(ȳ) = 44/17 ≡ 10/17 (mod 2)`.
* `MaxEven.d2_odd`: `q ≡ 1` on `D₂ \ {0}`; `MaxEven.d2_rank`: `dim D₂ ≤ 2` (three independent elements
  would have isotropic sum).
* `MaxEven.d3_norm`: `q(x̄) ∈ (2/3)ℤ` on `D₃`, nonzero mod 2 off `0`; `MaxEven.d3_rank`: `dim D₃ ≤ 2`
  (every ternary quadratic form over `𝔽₃` is isotropic: Chevalley–Warning, checked by `decide`).

The remaining step, the choice between the candidate forms, is Milgram's formula: see `FiniteForms.lean`.
-/

namespace Srg154

open RealInnerProductSpace

variable {G : SimpleGraph (Fin 154)} [DecidableRel G.Adj]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {v : Fin 154 → F}
  {N : AddSubgroup F}

theorem dual_add {x x' : F} (hx : x ∈ Dual v N) (hx' : x' ∈ Dual v N) : x + x' ∈ Dual v N :=
  ⟨Submodule.add_mem _ hx.1 hx'.1, fun n hn => by rw [inner_add_left]; exact (hx.2 n hn).add (hx'.2 n hn)⟩

theorem smul_mem_of_int {x : F} (k : ℤ) (c : ℝ) (hc : c = k) (hx : x ∈ N) : c • x ∈ N := by
  subst hc; exact zsmul_mem' k hx

/-- `D(N) = D₂ ⊕ D₃ ⊕ D₁₇`: `x = 51x + 34x + (-84)x` with the three parts killed by `2`, `3`, `17`. -/
theorem MaxEven.primary_decomp (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {x : F} (hx : x ∈ Dual v N) :
    x = (51 : ℝ) • x + (34 : ℝ) • x + (-84 : ℝ) • x ∧ (2 : ℝ) • ((51 : ℝ) • x) ∈ N ∧
      (3 : ℝ) • ((34 : ℝ) • x) ∈ N ∧ (17 : ℝ) • ((-84 : ℝ) • x) ∈ N := by
  have h := hN.mul102_mem hG hv hx
  refine ⟨by module, ?_, ?_, ?_⟩
  · rw [smul_smul]; norm_num; exact h
  · rw [smul_smul]; norm_num; exact h
  · rw [smul_smul, show (17 : ℝ) * -84 = ((-14 : ℤ) : ℝ) * 102 by norm_num, ← smul_smul]
    exact zsmul_mem' _ h

/-- Components of coprime orders are orthogonal: if `p x, q x' ∈ N` with `ap + bq = 1`, then `⟨x,x'⟩ ∈ ℤ`. -/
theorem MaxEven.coprime_orth {x x' : F} (hx : x ∈ Dual v N) (hx' : x' ∈ Dual v N) (p q a b : ℤ)
    (hab : a * p + b * q = 1) (hp : (p : ℝ) • x ∈ N) (hq : (q : ℝ) • x' ∈ N) : IsInt ⟪x, x'⟫ := by
  obtain ⟨s, hs⟩ := hx'.2 _ hp
  obtain ⟨t, ht⟩ := hx.2 _ hq
  rw [real_inner_smul_right, real_inner_comm] at hs
  rw [real_inner_smul_right] at ht
  refine ⟨a * s + b * t, ?_⟩
  have hab' : (a : ℝ) * p + b * q = 1 := by exact_mod_cast hab
  push_cast
  rw [← hs, ← ht]
  linear_combination (-⟪x, x'⟫) * hab'

/-- `q(ȳ) = 44/17 = 10/17 + 2`. -/
theorem y_sq_mod (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) : ⟪yv v, yv v⟫ = 10 / 17 + 2 := by
  rw [y_sq hG hv]; norm_num

/-- **`D₁₇ = ⟨ȳ⟩`**: if `17x ∈ N` then `x ≡ -5ℓ y (mod N)`, `ℓ = 17⟨y,x⟩`. -/
theorem MaxEven.d17_cyclic (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {x : F} (hx : x ∈ Dual v N) (h17 : (17 : ℝ) • x ∈ N) :
    x + (5 * (17 * ⟪yv v, x⟫)) • yv v ∈ N := by
  have e : x + (5 * (17 * ⟪yv v, x⟫)) • yv v =
      ((18 : ℝ) • x + (5 * (17 * ⟪yv v, x⟫)) • yv v) - (17 : ℝ) • x := by module
  rw [e]; exact N.sub_mem (hN.lemMax_b hG hv hx) h17

/-- **`q ≡ 1` on `D₂ \ {0}`**: `2x ∈ N`, `x ∉ N` ⇒ `x²` is an odd integer. -/
theorem MaxEven.d2_odd (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {x : F} (hx : x ∈ Dual v N) (h2 : (2 : ℝ) • x ∈ N) (hxN : x ∉ N) :
    ∃ k : ℤ, ⟪x, x⟫ = 2 * k + 1 := by
  obtain ⟨a, ha⟩ := hN.d2_int hG hv hx h2
  rcases Int.even_or_odd' a with ⟨k, rfl | rfl⟩
  · exact absurd (hN.mem_of_dual_even hx ⟨k, by rw [ha]; push_cast; ring⟩) hxN
  · exact ⟨k, by rw [ha]; push_cast; ring⟩

/-- **`dim D₂ ≤ 2`**: if `x₁, x₂, x₃ ∈ D₂` and none of `x₁, x₂, x₃, x₁+x₂, x₁+x₃, x₂+x₃` is `0` in `D(N)`,
then `x₁+x₂+x₃ = 0` in `D(N)` (otherwise it would be an isotropic vector: norm `3 + 3 ≡ 0`). -/
theorem MaxEven.d2_rank (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {x₁ x₂ x₃ : F} (h1 : x₁ ∈ Dual v N) (h2 : x₂ ∈ Dual v N) (h3 : x₃ ∈ Dual v N)
    (t1 : (2 : ℝ) • x₁ ∈ N) (t2 : (2 : ℝ) • x₂ ∈ N) (t3 : (2 : ℝ) • x₃ ∈ N)
    (n1 : x₁ ∉ N) (n2 : x₂ ∉ N) (n3 : x₃ ∉ N)
    (n12 : x₁ + x₂ ∉ N) (n13 : x₁ + x₃ ∉ N) (n23 : x₂ + x₃ ∉ N) : x₁ + x₂ + x₃ ∈ N := by
  have t : ∀ {a b : F}, (2 : ℝ) • a ∈ N → (2 : ℝ) • b ∈ N → (2 : ℝ) • (a + b) ∈ N := fun ha hb => by
    rw [smul_add]; exact N.add_mem ha hb
  obtain ⟨k1, e1⟩ := hN.d2_odd hG hv h1 t1 n1
  obtain ⟨k2, e2⟩ := hN.d2_odd hG hv h2 t2 n2
  obtain ⟨k3, e3⟩ := hN.d2_odd hG hv h3 t3 n3
  obtain ⟨k12, e12⟩ := hN.d2_odd hG hv (dual_add h1 h2) (t t1 t2) n12
  obtain ⟨k13, e13⟩ := hN.d2_odd hG hv (dual_add h1 h3) (t t1 t3) n13
  obtain ⟨k23, e23⟩ := hN.d2_odd hG hv (dual_add h2 h3) (t t2 t3) n23
  rw [real_inner_add_add_self] at e12 e13 e23
  refine hN.mem_of_dual_even (dual_add (dual_add h1 h2) h3) ⟨k12 + k13 + k23 - k1 - k2 - k3, ?_⟩
  rw [real_inner_add_add_self, real_inner_add_add_self, inner_add_left]
  push_cast
  linarith

/-- **`D₃` norms**: if `3x ∈ N` then `x² = 2a/3` with `a ∈ ℤ`, and `3 ∤ a` unless `x ∈ N`. -/
theorem MaxEven.d3_norm (hN : MaxEven v N) {x : F} (hx : x ∈ Dual v N) (h3 : (3 : ℝ) • x ∈ N) :
    ∃ a : ℤ, ⟪x, x⟫ = 2 * a / 3 ∧ (x ∉ N → ¬ (3 : ℤ) ∣ a) := by
  obtain ⟨t, ht⟩ := hx.2 _ h3
  obtain ⟨j, hj⟩ := hN.even _ h3
  rw [real_inner_smul_right] at ht
  rw [real_inner_smul_left, real_inner_smul_right] at hj
  have h3t : (3 * t : ℤ) = 2 * j := by
    have : (3 : ℝ) * t = 2 * j := by rw [← ht]; linarith
    exact_mod_cast this
  obtain ⟨a, rfl⟩ : (2 : ℤ) ∣ t := ⟨j - t, by omega⟩
  refine ⟨a, by push_cast at ht; linarith, fun hxN ⟨c, hc⟩ => hxN ?_⟩
  refine hN.mem_of_dual_even hx ⟨c, ?_⟩
  subst hc; push_cast at ht; linarith

/-- Every ternary quadratic form over `𝔽₃` is isotropic (Chevalley–Warning), by exhaustion. -/
theorem ternary_isotropic_F3 : ∀ a₁ a₂ a₃ b₁₂ b₁₃ b₂₃ : ZMod 3, ∃ c₁ c₂ c₃ : ZMod 3,
    (c₁ ≠ 0 ∨ c₂ ≠ 0 ∨ c₃ ≠ 0) ∧
    a₁ * c₁ ^ 2 + a₂ * c₂ ^ 2 + a₃ * c₃ ^ 2 + b₁₂ * c₁ * c₂ + b₁₃ * c₁ * c₃ + b₂₃ * c₂ * c₃ = 0 := by
  decide +kernel

/-- **`dim D₃ ≤ 2`**: any three elements of `D₃` are dependent over `𝔽₃`. -/
theorem MaxEven.d3_rank (hN : MaxEven v N) {x₁ x₂ x₃ : F} (h1 : x₁ ∈ Dual v N) (h2 : x₂ ∈ Dual v N)
    (h3 : x₃ ∈ Dual v N) (t1 : (3 : ℝ) • x₁ ∈ N) (t2 : (3 : ℝ) • x₂ ∈ N) (t3 : (3 : ℝ) • x₃ ∈ N) :
    ∃ c₁ c₂ c₃ : ℕ, c₁ < 3 ∧ c₂ < 3 ∧ c₃ < 3 ∧ (c₁ ≠ 0 ∨ c₂ ≠ 0 ∨ c₃ ≠ 0) ∧
      (c₁ : ℝ) • x₁ + (c₂ : ℝ) • x₂ + (c₃ : ℝ) • x₃ ∈ N := by
  obtain ⟨a₁, ea₁, -⟩ := hN.d3_norm h1 t1
  obtain ⟨a₂, ea₂, -⟩ := hN.d3_norm h2 t2
  obtain ⟨a₃, ea₃, -⟩ := hN.d3_norm h3 t3
  obtain ⟨b₁₂, eb₁₂⟩ := h2.2 _ t1
  obtain ⟨b₁₃, eb₁₃⟩ := h3.2 _ t1
  obtain ⟨b₂₃, eb₂₃⟩ := h3.2 _ t2
  rw [real_inner_smul_right, real_inner_comm] at eb₁₂ eb₁₃ eb₂₃
  obtain ⟨c₁, c₂, c₃, hne, hQ⟩ := ternary_isotropic_F3 a₁ a₂ a₃ b₁₂ b₁₃ b₂₃
  refine ⟨c₁.val, c₂.val, c₃.val, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ?_, ?_⟩
  · rcases hne with h | h | h
    · exact Or.inl ((ZMod.val_ne_zero c₁).2 h)
    · exact Or.inr (Or.inl ((ZMod.val_ne_zero c₂).2 h))
    · exact Or.inr (Or.inr ((ZMod.val_ne_zero c₃).2 h))
  · set u₁ : ℤ := ((c₁.val : ℕ) : ℤ); set u₂ : ℤ := ((c₂.val : ℕ) : ℤ); set u₃ : ℤ := ((c₃.val : ℕ) : ℤ)
    have hQZ : (3 : ℤ) ∣ a₁ * u₁ ^ 2 + a₂ * u₂ ^ 2 + a₃ * u₃ ^ 2 + b₁₂ * u₁ * u₂ +
        b₁₃ * u₁ * u₃ + b₂₃ * u₂ * u₃ := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1
      simp only [u₁, u₂, u₃]
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id]
      exact hQ
    obtain ⟨w, hw⟩ := hQZ
    have hd : (c₁.val : ℝ) • x₁ + (c₂.val : ℝ) • x₂ + (c₃.val : ℝ) • x₃ ∈ Dual v N := by
      have e : ∀ (c : ℕ) (x : F), x ∈ Dual v N → (c : ℝ) • x ∈ Dual v N := fun c x hx => by
        have := dual_zsmul hx (c : ℤ); exact_mod_cast this
      exact dual_add (dual_add (e _ _ h1) (e _ _ h2)) (e _ _ h3)
    refine hN.mem_of_dual_even hd ⟨w, ?_⟩
    have hw' : (a₁ : ℝ) * u₁ ^ 2 + a₂ * u₂ ^ 2 + a₃ * u₃ ^ 2 + b₁₂ * u₁ * u₂ +
        b₁₃ * u₁ * u₃ + b₂₃ * u₂ * u₃ = 3 * w := by exact_mod_cast hw
    simp only [u₁, u₂, u₃] at hw'
    push_cast at hw'
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    have s21 : ⟪x₂, x₁⟫ = ⟪x₁, x₂⟫ := real_inner_comm _ _
    have s31 : ⟪x₃, x₁⟫ = ⟪x₁, x₃⟫ := real_inner_comm _ _
    have s32 : ⟪x₃, x₂⟫ = ⟪x₂, x₃⟫ := real_inner_comm _ _
    rw [s21, s31, s32, ea₁, ea₂, ea₃]
    have q12 : ⟪x₁, x₂⟫ = b₁₂ / 3 := by rw [eq_div_iff (by norm_num)]; linarith
    have q13 : ⟪x₁, x₃⟫ = b₁₃ / 3 := by rw [eq_div_iff (by norm_num)]; linarith
    have q23 : ⟪x₂, x₃⟫ = b₂₃ / 3 := by rw [eq_div_iff (by norm_num)]; linarith
    rw [q12, q13, q23]
    linear_combination (2 / 3 : ℝ) * hw'

end Srg154
