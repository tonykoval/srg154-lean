import Srg154.DualVector

/-!
# The vertex lattice, `y = s/119` and the maximal even overlattice (§`sec:vertex`, Lemmas `lem:M`, `lem:y`,
`lem:max`, `lem:V`, and the norm statement of Proposition `prop:forms`)

Everything here is proved from `G.IsSRGWith 154 72 26 40`; there are no lattice-theoretic hypotheses.

* `exists_rep`: **vertex vectors exist**: there are `vᵢ` in a Euclidean space with `⟨vᵢ,vⱼ⟩ = 𝒢ᵢⱼ`,
  `𝒢 = -A + 2I + 2J` (the PSD statement, by the explicit decomposition `𝒢 = 𝒢'ᵀ𝒢'/18 + (17/11)J`,
  `𝒢' = 𝒢 - (17/11)J`, `𝒢'² = 18𝒢'`).
* For ANY family `v` in ANY real inner product space with Gram matrix `𝒢` (`IsRep`), with `W` its real span
  (the ambient space `ℝ²²` of the paper), `s = ∑ vᵢ`:
  - `lemM`: `∑ᵢ ⟨vᵢ,x⟩ vᵢ = 18x + (5/833)⟨s,x⟩ s` for `x ∈ W` (Lemma `lem:M`), `s_sq`: `s² = 36652`;
  - `lemY`: for every integral `N ⊇ L` inside `W`, `119 ∣ ⟨s,x⟩` (Lemma `lem:y`); `y² = 44/17`, `⟨vᵢ,y⟩ = 2`;
  - `exists_maxEven`: a maximal even `N ⊇ L` inside `W` exists (Zorn; no discreteness is needed);
  - `MaxEven.seventeen_y_mem`, `MaxEven.y_not_mem`, `MaxEven.lemMax_b`, `MaxEven.mem_of_dual_even`:
    Lemma `lem:max` (a), (b), (c);
  - `MaxEven.mul102_mem`, `MaxEven.norm51`: the exponent of `D(N)` divides `102 = 2·3·17` and
    `51x² ∈ ℤ` for every `x ∈ N^#` (the last sentence of Proposition `prop:forms`). This part of the
    proposition does NOT need Milgram's formula: it uses only the parity fact, `D₂` integral and `D₃` elementary;
  - `eq_adm`: **equation `(eq:adm)` from the graph**: for every `x ∈ N^#`, with `m = 51x²`, `ℓ = 17⟨y,x⟩`
    (both proved integral), `(m, ℓ)` has a witness with `Γᵢ = Γ(i)`. Hence also `m ≡ 2ℓ² (mod 17)`.
-/

namespace Srg154

open Matrix RealInnerProductSpace

variable {G : SimpleGraph (Fin 154)} [DecidableRel G.Adj]

/-! ## Part A: the vertex vectors exist -/

theorem gramM_mul_Jm (hG : G.IsSRGWith 154 72 26 40) : gramM G * Jm = (238 : ℝ) • Jm := by
  have h := congrArg Matrix.transpose (Jm_mul_gramM hG)
  rwa [Matrix.transpose_mul, gramM_transpose, Jm_transpose, Matrix.transpose_smul, Jm_transpose] at h

variable (G) in
/-- `𝒢' = 𝒢 - (17/11) J`. -/
noncomputable def gramP : Matrix (Fin 154) (Fin 154) ℝ := gramM G - (17 / 11 : ℝ) • Jm

theorem gramP_sq (hG : G.IsSRGWith 154 72 26 40) : gramP G * gramP G = (18 : ℝ) • gramP G := by
  simp only [gramP, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, gramM_sq hG,
    gramM_mul_Jm hG, Jm_mul_gramM hG, Jm_mul_Jm]
  module

theorem gramP_transpose : (gramP G)ᵀ = gramP G := by
  simp only [gramP, Matrix.transpose_sub, Matrix.transpose_smul, gramM_transpose, Jm_transpose]

variable (G) in
/-- The explicit vertex vectors in `ℝ^{1+154}`. -/
noncomputable def repVec (i : Fin 154) : EuclideanSpace ℝ (Option (Fin 154)) :=
  WithLp.toLp 2 (fun k => match k with
    | none => Real.sqrt (17 / 11)
    | some k => gramP G k i / Real.sqrt 18)

theorem repVec_inner (hG : G.IsSRGWith 154 72 26 40) (i j : Fin 154) :
    ⟪repVec G i, repVec G j⟫ = gramM G i j := by
  rw [PiLp.inner_apply, Fintype.sum_option]
  simp only [repVec, RCLike.inner_apply, conj_trivial]
  have h17 : Real.sqrt (17 / 11) * Real.sqrt (17 / 11) = 17 / 11 :=
    Real.mul_self_sqrt (by norm_num)
  have h18 : Real.sqrt 18 * Real.sqrt 18 = 18 := Real.mul_self_sqrt (by norm_num)
  have hs : (Real.sqrt 18) ≠ 0 := by positivity
  have hP : ∑ k : Fin 154, gramP G k j * gramP G k i = 18 * gramP G i j := by
    have := congrFun (congrFun (gramP_sq hG) i) j
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.transpose_apply (gramP G) k i, gramP_transpose, mul_comm]
  have e : ∑ k : Fin 154, gramP G k j / Real.sqrt 18 * (gramP G k i / Real.sqrt 18) =
      (∑ k : Fin 154, gramP G k j * gramP G k i) / 18 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 18)]
    ring
  rw [e, hP, h17]
  simp only [gramP, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Jm, Matrix.of_apply]
  ring

/-- **The vertex vectors exist** (Lemma `lem:V`'s setting; PSD of `-A+2I+2J`). -/
theorem exists_rep (hG : G.IsSRGWith 154 72 26 40) :
    ∃ v : Fin 154 → EuclideanSpace ℝ (Option (Fin 154)), ∀ i j, ⟪v i, v j⟫ = gramM G i j :=
  ⟨repVec G, repVec_inner hG⟩


/-! ## Part B: the arithmetic of Lemmas `lem:M`, `lem:y`, `lem:max`, `lem:V` and Prop. `prop:forms` -/

/-- `r` is an integer. -/
def IsInt (r : ℝ) : Prop := ∃ k : ℤ, r = k

/-- `r` is an even integer. -/
def IsEven2 (r : ℝ) : Prop := ∃ k : ℤ, r = 2 * k

theorem IsInt.add {a b : ℝ} (ha : IsInt a) (hb : IsInt b) : IsInt (a + b) := by
  obtain ⟨k, rfl⟩ := ha; obtain ⟨j, rfl⟩ := hb; exact ⟨k + j, by push_cast; ring⟩

theorem IsInt.neg {a : ℝ} (ha : IsInt a) : IsInt (-a) := by
  obtain ⟨k, rfl⟩ := ha; exact ⟨-k, by push_cast; ring⟩

theorem IsInt.zmul {a : ℝ} (c : ℤ) (ha : IsInt a) : IsInt (c * a) := by
  obtain ⟨k, rfl⟩ := ha; exact ⟨c * k, by push_cast; ring⟩

theorem IsInt.zero : IsInt 0 := ⟨0, by simp⟩

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable (G) in
/-- `v` is a family of vertex vectors: Gram matrix `-A + 2I + 2J`. -/
def IsRep (v : Fin 154 → F) : Prop := ∀ i j, ⟪v i, v j⟫ = gramM G i j

/-- The real span `W` of the vertex vectors (the space `ℝ²²` of the paper). -/
noncomputable abbrev Wsp (v : Fin 154 → F) : Submodule ℝ F := Submodule.span ℝ (Set.range v)

/-- `s = ∑ vᵢ`. -/
noncomputable def sv (v : Fin 154 → F) : F := ∑ i, v i

/-- `y = s / 119`. -/
noncomputable def yv (v : Fin 154 → F) : F := (1 / 119 : ℝ) • sv v

variable {v : Fin 154 → F}

theorem inner_v_comb (hv : IsRep G v) (i : Fin 154) (w : Fin 154 → ℝ) :
    ⟪v i, ∑ j, w j • v j⟫ = (gramM G *ᵥ w) i := by
  simp only [inner_sum, real_inner_smul_right, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by rw [hv, mul_comm]

theorem inner_comb_comb (hv : IsRep G v) (a b : Fin 154 → ℝ) :
    ⟪∑ i, a i • v i, ∑ j, b j • v j⟫ = a ⬝ᵥ (gramM G *ᵥ b) := by
  rw [sum_inner]
  simp only [real_inner_smul_left, inner_v_comb hv]
  rfl

theorem gramM_mulVec_one (hG : G.IsSRGWith 154 72 26 40) :
    gramM G *ᵥ (fun _ => (1 : ℝ)) = fun _ => 238 := by
  funext i
  have := congrFun (congrFun (gramM_mul_Jm hG) i) 0
  simpa [Matrix.mul_apply, Jm, Matrix.mulVec, dotProduct] using this

theorem sv_eq : sv v = ∑ i, (fun _ => (1 : ℝ)) i • v i := by simp [sv]

theorem inner_v_sv (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (i : Fin 154) :
    ⟪v i, sv v⟫ = 238 := by
  rw [sv_eq, inner_v_comb hv, gramM_mulVec_one hG]

/-- `s² = 36652 = 154 · 238` (Lemma `lem:M`). -/
theorem s_sq (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) : ⟪sv v, sv v⟫ = 36652 := by
  rw [sv_eq, inner_comb_comb hv, gramM_mulVec_one hG]
  simp [dotProduct]
  norm_num

theorem sv_mem : sv v ∈ Wsp v :=
  Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, rfl⟩

/-- **Lemma `lem:M`**: `M x = ∑ ⟨vᵢ,x⟩ vᵢ = 18x + (5/833)⟨s,x⟩ s` on the span `W`. -/
theorem lemM (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) {x : F} (hx : x ∈ Wsp v) :
    ∑ i, ⟪v i, x⟫ • v i = (18 : ℝ) • x + ((5 / 833 : ℝ) * ⟪sv v, x⟫) • sv v := by
  obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
  have hsx : ⟪sv v, ∑ j, w j • v j⟫ = 238 * ∑ j, w j := by
    rw [sv_eq, inner_comb_comb hv, ← (dual_vector_real hG w).1]
    simp [dotProduct]
  set u : Fin 154 → ℝ := fun i => (gramM G *ᵥ w) i - 18 * w i - (10 / 7 : ℝ) * ∑ j, w j with hu
  have hD : ∑ i, ⟪v i, ∑ j, w j • v j⟫ • v i -
      ((18 : ℝ) • ∑ j, w j • v j + ((5 / 833 : ℝ) * ⟪sv v, ∑ j, w j • v j⟫) • sv v) =
      ∑ i, u i • v i := by
    rw [hsx, sv, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_v_comb hv, hu]
    module
  have hGu : gramM G *ᵥ u = 0 := by
    have hu' : u = gramM G *ᵥ w - (18 : ℝ) • w - ((10 / 7 : ℝ) * ∑ j, w j) • (fun _ => (1 : ℝ)) := by
      funext i; simp [hu]
    rw [hu', Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec, gramM_sq hG,
      Matrix.add_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.smul_mulVec,
      gramM_mulVec_one hG]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Jm_mulVec, Pi.zero_apply]
    ring
  have h0 : ∑ i, u i • v i = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℝ), inner_comb_comb hv, hGu, dotProduct_zero]
  rw [← sub_eq_zero, hD, h0]

/-- `⟨x, M x⟩ = ∑ ⟨vᵢ,x⟩²`, hence `∑ zᵢ² = 18x² + (5/833)⟨s,x⟩²`. -/
theorem sum_sq_inner (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) {x : F} (hx : x ∈ Wsp v) :
    ∑ i, ⟪v i, x⟫ ^ 2 = 18 * ⟪x, x⟫ + (5 / 833 : ℝ) * ⟪sv v, x⟫ ^ 2 := by
  have h := congrArg (fun t => ⟪x, t⟫) (lemM hG hv hx)
  simp only [inner_sum, real_inner_smul_right, inner_add_right] at h
  have e : ∀ i, ⟪x, v i⟫ = ⟪v i, x⟫ := fun i => real_inner_comm _ _
  simp only [e] at h
  rw [show ⟪x, sv v⟫ = ⟪sv v, x⟫ from real_inner_comm _ _] at h
  rw [show ∑ i, ⟪v i, x⟫ ^ 2 = ∑ i, ⟪v i, x⟫ * ⟪v i, x⟫ from by simp [sq], h]
  ring

theorem sum_inner_eq (x : F) : ∑ i, ⟪v i, x⟫ = ⟪sv v, x⟫ := by
  rw [sv, sum_inner]

/-! ### Integral and even subgroups of `W` -/

/-- An even subgroup of `W` (the paper's even lattices `N ⊆ ℝ²²`; discreteness is never needed). -/
structure EvenIn (v : Fin 154 → F) (N : AddSubgroup F) : Prop where
  sub : ∀ x ∈ N, x ∈ Wsp v
  even : ∀ x ∈ N, IsEven2 ⟪x, x⟫

/-- A **maximal even overlattice** of `L = ℤ⟨v₁,…,v₁₅₄⟩` inside `W`. -/
structure MaxEven (v : Fin 154 → F) (N : AddSubgroup F) : Prop extends EvenIn v N where
  vmem : ∀ i, v i ∈ N
  max : ∀ N' : AddSubgroup F, N ≤ N' → EvenIn v N' → N' ≤ N

/-- The dual `N^# = {x ∈ W : ⟨x,n⟩ ∈ ℤ for all n ∈ N}`. -/
def Dual (v : Fin 154 → F) (N : AddSubgroup F) : Set F :=
  {x | x ∈ Wsp v ∧ ∀ n ∈ N, IsInt ⟪x, n⟫}

/-- Even ⇒ integral (polarisation). -/
theorem EvenIn.int {N : AddSubgroup F} (hN : EvenIn v N) {x y : F} (hx : x ∈ N) (hy : y ∈ N) :
    IsInt ⟪x, y⟫ := by
  obtain ⟨a, ha⟩ := hN.even _ (N.add_mem hx hy)
  obtain ⟨b, hb⟩ := hN.even _ hx
  obtain ⟨c, hc⟩ := hN.even _ hy
  refine ⟨a - b - c, ?_⟩
  have := real_inner_add_add_self x y
  push_cast
  linarith

theorem zsmul_mem' {N : AddSubgroup F} (k : ℤ) {x : F} (hx : x ∈ N) : (k : ℝ) • x ∈ N := by
  rw [Int.cast_smul_eq_zsmul]; exact N.zsmul_mem hx k

/-- Inner products inside the closure of a set with integral inner products are integral. -/
theorem int_closure (S : Set F) (hS : ∀ a ∈ S, ∀ b ∈ S, IsInt ⟪a, b⟫) :
    ∀ x ∈ AddSubgroup.closure S, ∀ y ∈ AddSubgroup.closure S, IsInt ⟪x, y⟫ := by
  have h1 : ∀ a ∈ S, ∀ y ∈ AddSubgroup.closure S, IsInt ⟪a, y⟫ := by
    intro a ha y hy
    induction hy using AddSubgroup.closure_induction with
    | mem b hb => exact hS a ha b hb
    | zero => simpa using IsInt.zero
    | add b c _ _ hb hc => rw [inner_add_right]; exact hb.add hc
    | neg b _ hb => rw [inner_neg_right]; exact hb.neg
  intro x hx y hy
  induction hx using AddSubgroup.closure_induction with
  | mem b hb => exact h1 b hb y hy
  | zero => simpa using IsInt.zero
  | add b c _ _ hb hc => rw [inner_add_left]; exact hb.add hc
  | neg b _ hb => rw [inner_neg_left]; exact hb.neg

/-- `L = ℤ⟨vᵢ⟩`. -/
noncomputable def Lv (v : Fin 154 → F) : AddSubgroup F := AddSubgroup.closure (Set.range v)

/-- `L` is even (vᵢ² = 4, ⟨vᵢ,vⱼ⟩ ∈ ℤ) and lies in `W`. -/
theorem Lv_even (hv : IsRep G v) : EvenIn v (Lv v) := by
  have hS : ∀ a ∈ Set.range v, ∀ b ∈ Set.range v, IsInt ⟪a, b⟫ := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rw [hv]
    by_cases hij : i = j
    · subst hij; exact ⟨4, by norm_num [gramM, Jm]⟩
    · by_cases ha : G.Adj i j
      · exact ⟨1, by norm_num [gramM, Jm, hij, ha]⟩
      · exact ⟨2, by norm_num [gramM, Jm, hij, ha]⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have : Lv v ≤ (Wsp v).toAddSubgroup :=
      (AddSubgroup.closure_le _).2 fun _ hy => Submodule.subset_span hy
    exact this hx
  · induction hx using AddSubgroup.closure_induction with
    | mem b hb =>
      obtain ⟨i, rfl⟩ := hb
      exact ⟨2, by rw [hv]; norm_num [gramM, Jm]⟩
    | zero => exact ⟨0, by simp⟩
    | add b c hb hc ihb ihc =>
      obtain ⟨k, hk⟩ := ihb; obtain ⟨j, hj⟩ := ihc
      obtain ⟨t, ht⟩ := int_closure _ hS b hb c hc
      refine ⟨k + j + t, ?_⟩
      rw [real_inner_add_add_self, hk, hj, ht]; push_cast; ring
    | neg b _ ihb => simpa using ihb

/-- **A maximal even overlattice exists** (Zorn's lemma on even subgroups of `W` containing `L`). -/
theorem exists_maxEven (hv : IsRep G v) : ∃ N : AddSubgroup F, MaxEven v N := by
  let S : Set (AddSubgroup F) := {N | Lv v ≤ N ∧ EvenIn v N}
  have hL : Lv v ∈ S := ⟨le_rfl, Lv_even hv⟩
  obtain ⟨N, -, hmax⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir := hc.directedOn
    refine ⟨sSup c, ⟨le_trans (hcS hy).1 (le_sSup hy), fun x hx => ?_, fun x hx => ?_⟩,
      fun z hz => le_sSup hz⟩
    · obtain ⟨K, hK, hxK⟩ := (AddSubgroup.mem_sSup_of_directedOn hne hdir).1 hx
      exact (hcS hK).2.sub x hxK
    · obtain ⟨K, hK, hxK⟩ := (AddSubgroup.mem_sSup_of_directedOn hne hdir).1 hx
      exact (hcS hK).2.even x hxK) (Lv v) hL
  refine ⟨N, ⟨hmax.1.2, fun i => hmax.1.1 (AddSubgroup.subset_closure ⟨i, rfl⟩), ?_⟩⟩
  intro N' hNN' hN'
  exact hmax.2 ⟨le_trans hmax.1.1 hNN', hN'⟩ hNN'

/-! ### Lemma `lem:y` -/

/-- **Lemma `lem:y`**: for an integral `N ⊇ L` inside `W`, `119 ∣ ⟨s,x⟩` for every `x ∈ N`. -/
theorem lemY (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) {N : AddSubgroup F}
    (hsub : ∀ x ∈ N, x ∈ Wsp v) (hvN : ∀ i, v i ∈ N) (hint : ∀ x ∈ N, ∀ y ∈ N, IsInt ⟪x, y⟫)
    {x : F} (hx : x ∈ N) : ∃ k : ℤ, ⟪sv v, x⟫ = 119 * k := by
  have hsN : sv v ∈ N := N.sum_mem fun i _ => hvN i
  obtain ⟨t, ht⟩ := hint _ hsN _ hx
  obtain ⟨a, ha⟩ := hint _ hx _ hx
  have hz : ∀ i, IsInt ⟪v i, x⟫ := fun i => hint _ (hvN i) _ hx
  choose z hz using hz
  have h := sum_sq_inner hG hv (hsub x hx)
  simp only [hz, ht, ha] at h
  have hZ : (833 : ℤ) * ∑ i, z i ^ 2 = 833 * 18 * a + 5 * t ^ 2 := by
    have : (833 : ℝ) * ∑ i, (z i : ℝ) ^ 2 = 833 * 18 * a + 5 * (t : ℝ) ^ 2 := by rw [h]; ring
    exact_mod_cast this
  have h119 : (119 : ℤ) ∣ t := by
    have hd : ((5 * t ^ 2 : ℤ) : ZMod 119) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨7 * ∑ i, z i ^ 2 - 7 * 18 * a, by linear_combination -hZ⟩
    have key : ∀ b : ZMod 119, 5 * b ^ 2 = 0 → b = 0 := by decide +kernel
    have := key (t : ZMod 119) (by push_cast at hd; exact hd)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd t 119).1 this
  obtain ⟨k, rfl⟩ := h119
  exact ⟨k, by rw [ht]; push_cast; ring⟩

theorem y_mem : yv v ∈ Wsp v := Submodule.smul_mem _ _ sv_mem

/-- `y² = 44/17`. -/
theorem y_sq (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) : ⟪yv v, yv v⟫ = 44 / 17 := by
  rw [yv, real_inner_smul_left, real_inner_smul_right, s_sq hG hv]; norm_num

/-- `⟨vᵢ, y⟩ = 2`. -/
theorem inner_v_y (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (i : Fin 154) :
    ⟪v i, yv v⟫ = 2 := by
  rw [yv, real_inner_smul_right, inner_v_sv hG hv]; norm_num

/-- `M = 18 I + 85 y yᵀ` on `W`. -/
theorem lemM_y (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) {x : F} (hx : x ∈ Wsp v) :
    ∑ i, ⟪v i, x⟫ • v i = (18 : ℝ) • x + (85 * ⟪yv v, x⟫) • yv v := by
  rw [lemM hG hv hx, yv, real_inner_smul_left, smul_smul]
  congr 2; ring

/-! ### Lemma `lem:max` -/

section MaxEvenSec

variable {N : AddSubgroup F}

theorem MaxEven.int (hN : MaxEven v N) {x y : F} (hx : x ∈ N) (hy : y ∈ N) : IsInt ⟪x, y⟫ :=
  hN.toEvenIn.int hx hy

/-- `⟨y, n⟩ ∈ ℤ` for `n ∈ N` (Lemma `lem:y`). -/
theorem MaxEven.inner_y (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {n : F} (hn : n ∈ N) : IsInt ⟪yv v, n⟫ := by
  obtain ⟨k, hk⟩ := lemY hG hv hN.sub hN.vmem (fun _ hx _ hy => hN.int hx hy) hn
  exact ⟨k, by rw [yv, real_inner_smul_left, hk]; ring⟩

/-- **Lemma `lem:max`(c)** (anisotropy): `x ∈ N^#` with `x²` even lies in `N`. -/
theorem MaxEven.mem_of_dual_even (hN : MaxEven v N) {x : F} (hx : x ∈ Dual v N)
    (he : IsEven2 ⟪x, x⟫) : x ∈ N := by
  have hEv : EvenIn v (N ⊔ AddSubgroup.zmultiples x) := by
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · obtain ⟨n, hn, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hm
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hz
      exact Submodule.add_mem _ (hN.sub n hn) (by
        rw [← Int.cast_smul_eq_zsmul ℝ]; exact Submodule.smul_mem _ _ hx.1)
    · obtain ⟨n, hn, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hm
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hz
      obtain ⟨a, ha⟩ := hN.even n hn
      obtain ⟨b, hb⟩ := hx.2 n hn
      obtain ⟨c, hc⟩ := he
      refine ⟨a + k * b + k ^ 2 * c, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_add_add_self, real_inner_smul_right,
        real_inner_smul_left, real_inner_smul_right]
      have hb' : ⟪n, x⟫ = b := by rw [real_inner_comm]; exact hb
      rw [hb', ha, hc]
      push_cast; ring
  exact hN.max _ le_sup_left hEv (AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples x))

theorem dual_of_mem (hN : MaxEven v N) {x : F} (hx : x ∈ N) : x ∈ Dual v N :=
  ⟨hN.sub x hx, fun _ hn => hN.int hx hn⟩

theorem dual_zsmul {x : F} (hx : x ∈ Dual v N) (k : ℤ) : (k : ℝ) • x ∈ Dual v N :=
  ⟨Submodule.smul_mem _ _ hx.1, fun n hn => by
    rw [real_inner_smul_left]; exact (hx.2 n hn).zmul k⟩

/-- **Lemma `lem:max`(a)**: `17 y ∈ N`. -/
theorem MaxEven.seventeen_y_mem (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N) :
    (17 : ℝ) • yv v ∈ N := by
  refine hN.mem_of_dual_even ⟨Submodule.smul_mem _ _ y_mem, fun n hn => ?_⟩ ⟨374, ?_⟩
  · rw [real_inner_smul_left]; exact_mod_cast (hN.inner_y hG hv hn).zmul 17
  · rw [real_inner_smul_left, real_inner_smul_right, y_sq hG hv]; norm_num

/-- **Lemma `lem:max`(a)**: `y ∉ N` (its norm `44/17` is not an integer). -/
theorem MaxEven.y_not_mem (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N) :
    yv v ∉ N := by
  intro hy
  obtain ⟨k, hk⟩ := hN.even _ hy
  rw [y_sq hG hv] at hk
  have : (44 : ℝ) = 34 * k := by linarith
  have : (44 : ℤ) = 34 * k := by exact_mod_cast this
  omega

/-- `ℓ = 17⟨y,x⟩ ∈ ℤ` for `x ∈ N^#`. -/
theorem MaxEven.ell_int (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {x : F} (hx : x ∈ Dual v N) : IsInt (17 * ⟪yv v, x⟫) := by
  have := hx.2 _ (hN.seventeen_y_mem hG hv)
  rwa [real_inner_comm, real_inner_smul_left] at this

/-- **Lemma `lem:max`(b)**: `18x + 5ℓy = Mx ∈ N` for `x ∈ N^#`. -/
theorem MaxEven.lemMax_b (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {x : F} (hx : x ∈ Dual v N) :
    (18 : ℝ) • x + (5 * (17 * ⟪yv v, x⟫)) • yv v ∈ N := by
  have e : (18 : ℝ) • x + (5 * (17 * ⟪yv v, x⟫)) • yv v = ∑ i, ⟪v i, x⟫ • v i := by
    rw [lemM_y hG hv hx.1]; congr 2; ring
  rw [e]
  refine N.sum_mem fun i _ => ?_
  obtain ⟨z, hz⟩ := hx.2 _ (hN.vmem i)
  rw [real_inner_comm, hz]
  exact zsmul_mem' z (hN.vmem i)

/-- **Lemma `lem:max`(b)**: `306 x ∈ N` for `x ∈ N^#`. -/
theorem MaxEven.mul306_mem (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {x : F} (hx : x ∈ Dual v N) : (306 : ℝ) • x ∈ N := by
  obtain ⟨ℓ, hℓ⟩ := hN.ell_int hG hv hx
  have h1 := zsmul_mem' 17 (hN.lemMax_b hG hv hx)
  have h2 := zsmul_mem' (5 * ℓ) (hN.seventeen_y_mem hG hv)
  have e : (306 : ℝ) • x = ((17 : ℤ) : ℝ) • ((18 : ℝ) • x + (5 * (17 * ⟪yv v, x⟫)) • yv v) -
      ((5 * ℓ : ℤ) : ℝ) • ((17 : ℝ) • yv v) := by
    push_cast; rw [← hℓ]; module
  rw [e]; exact N.sub_mem h1 h2

/-! ### Proposition `prop:forms`: the parts that do not need Milgram's formula -/

/-- Integer coordinates `zᵢ = ⟨vᵢ, x⟩` of `x ∈ N^#`. -/
theorem MaxEven.coords (hN : MaxEven v N) {x : F} (hx : x ∈ Dual v N) :
    ∃ z : Fin 154 → ℤ, ∀ i, ⟪v i, x⟫ = z i := by
  have := fun i => hx.2 _ (hN.vmem i)
  choose z hz using this
  exact ⟨z, fun i => by rw [real_inner_comm]; exact hz i⟩

/-- **The parity fact**: if `x ∈ N^#` and `⟨y,x⟩ ∈ ℤ`, then `9x² ∈ ℤ`
(from `∑ zᵢ² ≡ ∑ zᵢ (mod 2)`, `∑ zᵢ² = 18x² + 85⟨y,x⟩²`, `∑ zᵢ = 119⟨y,x⟩`). -/
theorem MaxEven.parity (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {x : F} (hx : x ∈ Dual v N) (hy : IsInt ⟪yv v, x⟫) : IsInt (9 * ⟪x, x⟫) := by
  obtain ⟨z, hz⟩ := hN.coords hx
  obtain ⟨l, hl⟩ := hy
  have h2 := sum_sq_inner hG hv hx.1
  have h1 := sum_inner_eq (v := v) x
  have hs : ⟪sv v, x⟫ = 119 * ⟪yv v, x⟫ := by rw [yv, real_inner_smul_left]; ring
  simp only [hz, hs, hl] at h1 h2
  have hK : ((∑ i, z i ^ 2 - 85 * l ^ 2 : ℤ) : ℝ) = 18 * ⟪x, x⟫ := by
    push_cast; rw [h2]; ring
  have hsum : ∑ i, z i = 119 * l := by exact_mod_cast h1
  have hev : (2 : ℤ) ∣ ∑ i, z i ^ 2 - 85 * l ^ 2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1
    have sq2 : ∀ b : ZMod 2, b ^ 2 = b := by decide
    have e1 : ((∑ i, z i ^ 2 : ℤ) : ZMod 2) = ((∑ i, z i : ℤ) : ZMod 2) := by
      push_cast; exact Finset.sum_congr rfl fun i _ => sq2 _
    have e2 : ((∑ i, z i ^ 2 - 85 * l ^ 2 : ℤ) : ZMod 2) =
        ((∑ i, z i ^ 2 : ℤ) : ZMod 2) - 85 * (l : ZMod 2) ^ 2 := by push_cast; ring
    rw [e2, e1, hsum]
    push_cast
    rw [sq2]
    have : (119 : ZMod 2) = 85 := by decide
    rw [this]; ring
  obtain ⟨j, hj⟩ := hev
  refine ⟨j, ?_⟩
  rw [hj] at hK; push_cast at hK; linarith

/-- `D₂` is integral: `x ∈ N^#`, `2x ∈ N` ⇒ `x² ∈ ℤ`. -/
theorem MaxEven.d2_int (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {x : F} (hx : x ∈ Dual v N) (h2 : (2 : ℝ) • x ∈ N) : IsInt ⟪x, x⟫ := by
  have hy : IsInt ⟪yv v, x⟫ := by
    obtain ⟨a, ha⟩ := hN.inner_y hG hv h2
    obtain ⟨b, hb⟩ := hN.ell_int hG hv hx
    refine ⟨9 * a - b, ?_⟩
    rw [real_inner_smul_right] at ha
    push_cast; linarith
  obtain ⟨k, hk⟩ := hN.parity hG hv hx hy
  obtain ⟨j, hj⟩ := hN.even _ h2
  rw [real_inner_smul_left, real_inner_smul_right] at hj
  exact ⟨k - 4 * j, by push_cast; linarith⟩

/-- `D₃` is elementary: `x ∈ N^#`, `9x ∈ N` ⇒ `3x ∈ N` (an element of order 9 would make `3x̄` isotropic). -/
theorem MaxEven.d3_elem (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {x : F} (hx : x ∈ Dual v N) (h9 : (9 : ℝ) • x ∈ N) : (3 : ℝ) • x ∈ N := by
  have hy : IsInt ⟪yv v, x⟫ := by
    obtain ⟨a, ha⟩ := hN.inner_y hG hv h9
    obtain ⟨b, hb⟩ := hN.ell_int hG hv hx
    refine ⟨2 * a - b, ?_⟩
    rw [real_inner_smul_right] at ha
    push_cast; linarith
  obtain ⟨k, hk⟩ := hN.parity hG hv hx hy
  obtain ⟨j, hj⟩ := hN.even _ h9
  rw [real_inner_smul_left, real_inner_smul_right] at hj
  have hkj : (9 * k : ℤ) = 2 * j := by
    have : (9 : ℝ) * k = 2 * j := by rw [← hk]; linarith
    exact_mod_cast this
  have h3 : (3 : ℝ) • x = ((3 : ℤ) : ℝ) • x := by norm_num
  refine hN.mem_of_dual_even (h3 ▸ dual_zsmul hx 3) ⟨j - 4 * k, ?_⟩
  rw [real_inner_smul_left, real_inner_smul_right]
  have : (k : ℝ) = 2 * (j - 4 * k) := by
    have : k = 2 * (j - 4 * k) := by omega
    exact_mod_cast this
  push_cast
  linarith

/-- The exponent of `D(N)` divides `102 = 2·3·17`: `102 x ∈ N` for `x ∈ N^#`. -/
theorem MaxEven.mul102_mem (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {x : F} (hx : x ∈ Dual v N) : (102 : ℝ) • x ∈ N := by
  have hx' : ((34 : ℤ) : ℝ) • x ∈ Dual v N := dual_zsmul hx 34
  have h9 : (9 : ℝ) • (((34 : ℤ) : ℝ) • x) ∈ N := by
    rw [smul_smul]; norm_num; exact hN.mul306_mem hG hv hx
  have := hN.d3_elem hG hv hx' h9
  rw [smul_smul] at this; norm_num at this; exact this

/-- **Proposition `prop:forms`, last sentence**: `51 x² ∈ ℤ` for every `x ∈ N^#` (no Milgram needed). -/
theorem MaxEven.norm51 (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) (hN : MaxEven v N)
    {x : F} (hx : x ∈ Dual v N) : IsInt (51 * ⟪x, x⟫) := by
  have h102 := hN.mul102_mem hG hv hx
  obtain ⟨p, hp⟩ := hx.2 _ h102
  rw [real_inner_smul_right] at hp
  have hu : ((51 : ℤ) : ℝ) • x ∈ Dual v N := dual_zsmul hx 51
  have h2 : (2 : ℝ) • (((51 : ℤ) : ℝ) • x) ∈ N := by rw [smul_smul]; norm_num; exact h102
  obtain ⟨q, hq⟩ := hN.d2_int hG hv hu h2
  rw [real_inner_smul_left, real_inner_smul_right] at hq
  exact ⟨26 * p - q, by push_cast at hq ⊢; linarith⟩

end MaxEvenSec

/-! ### Equation `(eq:adm)` from the graph -/

/-- **Equation `(eq:adm)`, formal from the graph.** Let `vᵢ` be ANY vertex vectors of an
srg(154,72,26,40) and `N` ANY maximal even overlattice of `L` (both exist: `exists_rep`, `exists_maxEven`).
For every `x ∈ N^#`, `m = 51x²` and `ℓ = 17⟨y,x⟩` are integers and `(m, ℓ)` has a witness, namely
`zᵢ = ⟨vᵢ,x⟩` with `Γᵢ = Γ(i)`. -/
theorem eq_adm (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) {N : AddSubgroup F} (hN : MaxEven v N)
    {x : F} (hx : x ∈ Dual v N) :
    ∃ m ℓ : ℤ, (m : ℝ) = 51 * ⟪x, x⟫ ∧ (ℓ : ℝ) = 17 * ⟪yv v, x⟫ ∧
      ∃ z : Fin 154 → ℤ, (∀ i, (z i : ℝ) = ⟪v i, x⟫) ∧
        Witness m ℓ z (fun i => G.neighborFinset i) := by
  obtain ⟨m, hm⟩ := hN.norm51 hG hv hx
  obtain ⟨ℓ, hℓ⟩ := hN.ell_int hG hv hx
  obtain ⟨z, hz⟩ := hN.coords hx
  have hx1 := hx.1
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx1
  refine ⟨m, ℓ, hm.symm, hℓ.symm, z, fun i => (hz i).symm, ?_⟩
  refine dual_vector_witness hG w z (fun i => by rw [← hz i, ← hw, inner_v_comb hv]) m ℓ
    (by rw [← hm, ← hw, inner_comb_comb hv]) ?_
  have h1 := sum_inner_eq (v := v) x
  have hs : ⟪sv v, x⟫ = 7 * (17 * ⟪yv v, x⟫) := by
    rw [yv, real_inner_smul_left]; ring
  simp only [hz] at h1
  rw [hs, hℓ] at h1
  exact_mod_cast h1

/-- `(eq:adm)` in the `HasWitness` form used by all forbidden-pair theorems, with test L0
(`m ≡ 2ℓ² mod 17`). -/
theorem eq_adm_hasWitness (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) {N : AddSubgroup F}
    (hN : MaxEven v N) {x : F} (hx : x ∈ Dual v N) :
    ∃ m ℓ : ℤ, (m : ℝ) = 51 * ⟪x, x⟫ ∧ (ℓ : ℝ) = 17 * ⟪yv v, x⟫ ∧ HasWitness m ℓ ∧
      (m - 2 * ℓ ^ 2) % 17 = 0 := by
  obtain ⟨m, ℓ, hm, hℓ, z, -, hw⟩ := eq_adm hG hv hN hx
  refine ⟨m, ℓ, hm, hℓ, ⟨z, _, hw⟩, ?_⟩
  have h0 := hw.L0
  generalize ℓ ^ 2 = q at h0 ⊢
  omega

end Srg154

namespace Srg154

open RealInnerProductSpace

variable {G : SimpleGraph (Fin 154)} [DecidableRel G.Adj]

/-- **Capstone of groups 1–2**: from `G.IsSRGWith 154 72 26 40` alone, vertex vectors exist, a maximal
even overlattice exists, and for EVERY maximal even overlattice `N` and every `x ∈ N^#`,
`(51x², 17⟨y,x⟩)` is a pair of integers with a witness (equation `(eq:adm)`). -/
theorem graph_to_eq_adm (hG : G.IsSRGWith 154 72 26 40) :
    ∃ v : Fin 154 → EuclideanSpace ℝ (Option (Fin 154)), IsRep G v ∧
      (∃ N : AddSubgroup (EuclideanSpace ℝ (Option (Fin 154))), MaxEven v N) ∧
      ∀ N, MaxEven v N → ∀ x ∈ Dual v N, ∃ m ℓ : ℤ, (m : ℝ) = 51 * ⟪x, x⟫ ∧
        (ℓ : ℝ) = 17 * ⟪yv v, x⟫ ∧ HasWitness m ℓ := by
  obtain ⟨v, hv⟩ := exists_rep hG
  refine ⟨v, hv, exists_maxEven hv, fun N hN x hx => ?_⟩
  obtain ⟨m, ℓ, hm, hℓ, hw, -⟩ := eq_adm_hasWitness hG hv hN hx
  exact ⟨m, ℓ, hm, hℓ, hw⟩

end Srg154
