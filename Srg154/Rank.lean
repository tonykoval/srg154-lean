import Srg154.VertexLattice

/-!
# `rank L = 22` (Section `sec:vertex`: "`G` is positive semidefinite of rank 22")

For any family of vertex vectors `v` (`IsRep`), the real span `W` has dimension `22`.
This is the signature `22` used in Milgram's formula (`FiniteForms.lean`).

Proof: `E = 𝒢'/18 + J/154` is idempotent with trace `378/18 + 1 = 22`, `ker 𝒢 = ker E`, and the
map `w ↦ ∑ wᵢ vᵢ` has range `W` and kernel `ker 𝒢` (`‖∑ wᵢvᵢ‖² = wᵀ𝒢w`).
-/

namespace Srg154

open Matrix RealInnerProductSpace

variable {G : SimpleGraph (Fin 154)} [DecidableRel G.Adj]

variable (G) in
/-- `E = 𝒢'/18 + J/154`. -/
noncomputable def idemE : Matrix (Fin 154) (Fin 154) ℝ := (1 / 18 : ℝ) • gramP G + (1 / 154 : ℝ) • Jm

theorem gramP_mul_Jm (hG : G.IsSRGWith 154 72 26 40) : gramP G * Jm = 0 := by
  simp only [gramP, Matrix.sub_mul, Matrix.smul_mul, gramM_mul_Jm hG, Jm_mul_Jm]; module

theorem Jm_mul_gramP (hG : G.IsSRGWith 154 72 26 40) : Jm * gramP G = 0 := by
  simp only [gramP, Matrix.mul_sub, Matrix.mul_smul, Jm_mul_gramM hG, Jm_mul_Jm]; module

theorem idemE_idem (hG : G.IsSRGWith 154 72 26 40) : idemE G * idemE G = idemE G := by
  simp only [idemE, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, gramP_sq hG,
    gramP_mul_Jm hG, Jm_mul_gramP hG, Jm_mul_Jm]
  module

theorem trace_gramM : Matrix.trace (gramM G) = 616 := by
  simp [gramM, Matrix.trace, Jm]; norm_num

theorem trace_idemE : Matrix.trace (idemE G) = 22 := by
  simp only [idemE, gramP, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub, trace_gramM]
  simp [Matrix.trace, Jm]; norm_num

theorem gramM_eq_E :
    gramM G = gramP G + (17 / 11 : ℝ) • Jm := by
  simp only [gramP]; module

/-- `(αP + βJ) w = 0 ↔ P w = 0 ∧ J w = 0` for `α, β ≠ 0` (`P = 𝒢'`, `P² = 18P`, `PJ = JP = 0`). -/
theorem comb_mulVec_eq_zero_iff (hG : G.IsSRGWith 154 72 26 40) (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (w : Fin 154 → ℝ) :
    (α • gramP G + β • Jm) *ᵥ w = 0 ↔ gramP G *ᵥ w = 0 ∧ Jm *ᵥ w = 0 := by
  constructor
  · intro h
    have h1 : gramP G *ᵥ ((α • gramP G + β • Jm) *ᵥ w) = 0 := by rw [h, mulVec_zero]
    have h2 : Jm *ᵥ ((α • gramP G + β • Jm) *ᵥ w) = 0 := by rw [h, mulVec_zero]
    rw [mulVec_mulVec, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, gramP_sq hG, gramP_mul_Jm hG,
      smul_zero, add_zero, smul_smul, smul_mulVec] at h1
    rw [mulVec_mulVec, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Jm_mul_gramP hG, Jm_mul_Jm,
      smul_zero, zero_add, smul_smul, smul_mulVec] at h2
    exact ⟨(smul_eq_zero.1 h1).resolve_left (mul_ne_zero hα (by norm_num)),
      (smul_eq_zero.1 h2).resolve_left (mul_ne_zero hβ (by norm_num))⟩
  · rintro ⟨hp, hj⟩
    rw [add_mulVec, smul_mulVec, smul_mulVec, hp, hj]; simp

/-- `𝒢 w = 0 ↔ E w = 0`. -/
theorem gramM_mulVec_eq_zero_iff (hG : G.IsSRGWith 154 72 26 40) (w : Fin 154 → ℝ) :
    gramM G *ᵥ w = 0 ↔ idemE G *ᵥ w = 0 := by
  have e1 : gramM G = (1 : ℝ) • gramP G + (17 / 11 : ℝ) • Jm := by rw [gramM_eq_E, one_smul]
  rw [e1, idemE, comb_mulVec_eq_zero_iff hG _ _ (by norm_num) (by norm_num),
    comb_mulVec_eq_zero_iff hG _ _ (by norm_num) (by norm_num)]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {v : Fin 154 → F}

/-- `w ↦ ∑ wᵢ vᵢ`. -/
noncomputable def Bmap (v : Fin 154 → F) : (Fin 154 → ℝ) →ₗ[ℝ] F where
  toFun w := ∑ i, w i • v i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, smul_smul]

theorem range_Bmap : LinearMap.range (Bmap v) = Wsp v := by
  ext x
  rw [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun]
  rfl

theorem ker_Bmap (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) :
    LinearMap.ker (Bmap v) = LinearMap.ker (Matrix.toLin' (idemE G)) := by
  ext w
  simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
  rw [← gramM_mulVec_eq_zero_iff hG]
  change ∑ i, w i • v i = 0 ↔ _
  constructor
  · intro h
    funext i
    rw [← inner_v_comb hv, h, inner_zero_right]; rfl
  · intro h
    rw [← inner_self_eq_zero (𝕜 := ℝ), inner_comb_comb hv, h, dotProduct_zero]

/-- **`dim W = 22`**: the vertex vectors span a space of dimension `22` (rank of `-A+2I+2J`). -/
theorem finrank_W (hG : G.IsSRGWith 154 72 26 40) (hv : IsRep G v) : Module.finrank ℝ (Wsp v) = 22 := by
  have hidem : IsIdempotentElem (Matrix.toLin' (idemE G)) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, idemE_idem hG]
  have htr : LinearMap.trace ℝ _ (Matrix.toLin' (idemE G)) = 22 := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 154)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin', trace_idemE]
  rw [(LinearMap.IsIdempotentElem.isProj_range _ hidem).trace] at htr
  have hrE : Module.finrank ℝ (LinearMap.range (Matrix.toLin' (idemE G))) = 22 := by exact_mod_cast htr
  have h1 := LinearMap.finrank_range_add_finrank_ker (Bmap v)
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (idemE G))
  rw [ker_Bmap hG hv] at h1
  rw [← range_Bmap]
  omega

end Srg154
