import Srg154.Parameters
import Srg154.Admissible

/-!
# The dual-vector lemma (Lemma `lem:V`(ii),(iii)) from the graph

Let `B` be the `22 × 154` matrix with columns the vertex vectors `vᵢ`, so `B^T B = 𝒢 := -A + 2I + 2J`.
A vector of the span is `x = B w` (`w ∈ ℝ¹⁵⁴`), with `x² = w^T 𝒢 w` and `zᵢ = ⟨x, vᵢ⟩ = (𝒢 w)ᵢ`.
We prove, for ANY `w` and directly from `G.IsSRGWith 154 72 26 40` (no lattice theory):

  `𝒢² = 18 𝒢 + 340 J`, hence `∑ z² = 18 x² + (5/17) ℓ²` and `A z = -16 z + 4ℓ 𝟙`, where `7ℓ = ∑ z`.

Consequently, whenever `z` is integral, `51 x² = m ∈ ℤ` and `∑ z = 7ℓ` with `ℓ ∈ ℤ` (these three facts are
what Lemmas `lem:y`, `lem:max` and Proposition `prop:forms` provide for `x ∈ N^#`; they are NOT formalised),
`(m, ℓ)` has a witness with `Γᵢ = Γ(i)`, the neighbourhood of `i`.  This is equation `(eq:adm)`, i.e. the only
way the graph enters the rest of the proof.
-/

namespace Srg154

open Matrix

variable (G : SimpleGraph (Fin 154)) [DecidableRel G.Adj]

/-- The Gram matrix `-A + 2I + 2J` of the vertex vectors. -/
noncomputable def gramM : Matrix (Fin 154) (Fin 154) ℝ :=
  (2 : ℝ) • (1 : Matrix (Fin 154) (Fin 154) ℝ) + (2 : ℝ) • Jm - G.adjMatrix ℝ

theorem Jm_mul_Jm : Jm * Jm = (154 : ℝ) • Jm := by
  ext i j; simp [Jm, Matrix.mul_apply]

theorem Jm_transpose : Jmᵀ = Jm := by ext i j; simp [Jm]

theorem Jm_mulVec (v : Fin 154 → ℝ) (i : Fin 154) : (Jm *ᵥ v) i = ∑ j, v j := by
  simp [Jm, Matrix.mulVec, dotProduct]

variable {G}

theorem Jm_mul_adj (hG : G.IsSRGWith 154 72 26 40) : Jm * G.adjMatrix ℝ = (72 : ℝ) • Jm := by
  have h := congrArg Matrix.transpose (srg_reg G hG)
  rw [Matrix.transpose_mul, Matrix.transpose_smul, Jm_transpose,
    (G.isSymm_adjMatrix (α := ℝ)).eq] at h
  exact h

theorem gramM_sq (hG : G.IsSRGWith 154 72 26 40) :
    gramM G * gramM G = (18 : ℝ) • gramM G + (340 : ℝ) • Jm := by
  have hsq := srg_sq G hG
  have hreg := srg_reg G hG
  have hJA := Jm_mul_adj hG
  have hJJ := Jm_mul_Jm
  simp only [gramM, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hsq, hreg, hJA, hJJ]
  module

theorem Jm_mul_gramM (hG : G.IsSRGWith 154 72 26 40) : Jm * gramM G = (238 : ℝ) • Jm := by
  have hJA := Jm_mul_adj hG
  simp only [gramM, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hJA, Jm_mul_Jm]
  module

theorem gramM_transpose : (gramM G)ᵀ = gramM G := by
  simp only [gramM, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_one, Jm_transpose, (G.isSymm_adjMatrix (α := ℝ)).eq]

/-- **Lemma `lem:V` (ii)-(iii), real form.** For every `w`, with `z = 𝒢 w`, `a = w^T 𝒢 w`: -/
theorem dual_vector_real (hG : G.IsSRGWith 154 72 26 40) (w : Fin 154 → ℝ) :
    let z := gramM G *ᵥ w
    (∑ i, z i = 238 * ∑ i, w i) ∧
    (∑ i, z i ^ 2 = 18 * (w ⬝ᵥ z) + 340 * (∑ i, w i) ^ 2) ∧
    (∀ i, ∑ j ∈ G.neighborFinset i, z j = -16 * z i + 2 * ∑ j, z j - 340 * ∑ j, w j) := by
  intro z
  have hsumz : ∀ i : Fin 154, (Jm *ᵥ z) i = 238 * ∑ j, w j := by
    intro i
    rw [show z = gramM G *ᵥ w from rfl, mulVec_mulVec, Jm_mul_gramM hG, smul_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, Jm_mulVec]
  have h1 : ∑ i, z i = 238 * ∑ i, w i := by rw [← Jm_mulVec z 0, hsumz 0]
  have hgz : gramM G *ᵥ z = (18 : ℝ) • z + (340 : ℝ) • (Jm *ᵥ w) := by
    simp only [z, mulVec_mulVec, gramM_sq hG, add_mulVec, smul_mulVec]
  refine ⟨h1, ?_, ?_⟩
  · -- ∑ z² = z·z = w·(𝒢² w)
    have : ∑ i, z i ^ 2 = z ⬝ᵥ z := by simp [dotProduct, sq]
    rw [this]
    have e : z ⬝ᵥ z = w ⬝ᵥ (gramM G *ᵥ z) := by
      conv_lhs => rw [show z = gramM G *ᵥ w from rfl]
      rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, gramM_transpose, dotProduct_comm]
    rw [e, hgz, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have : w ⬝ᵥ (Jm *ᵥ w) = (∑ i, w i) ^ 2 := by
      simp only [dotProduct, Jm_mulVec, ← Finset.sum_mul, sq]
    rw [this]
  · intro i
    rw [← SimpleGraph.adjMatrix_mulVec_apply]
    have hA : G.adjMatrix ℝ = (2 : ℝ) • (1 : Matrix (Fin 154) (Fin 154) ℝ) + (2 : ℝ) • Jm - gramM G := by
      simp [gramM]
    rw [hA, sub_mulVec, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hgz]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Jm_mulVec]
    ring

/-- **Lemma `lem:V` ⇒ `(eq:adm)`.** If `z = 𝒢 w` is integral, `51 x² = m` and `∑ z = 7ℓ` with integers
`m, ℓ`, then `(m, ℓ)` has a witness, with `Γ i` the neighbourhood of `i` in the graph. -/
theorem dual_vector_witness (hG : G.IsSRGWith 154 72 26 40) (w : Fin 154 → ℝ) (z : Fin 154 → ℤ)
    (hz : ∀ i, (z i : ℝ) = (gramM G *ᵥ w) i) (m ℓ : ℤ)
    (hm : (m : ℝ) = 51 * (w ⬝ᵥ (gramM G *ᵥ w))) (hl : ∑ i, z i = 7 * ℓ) :
    Witness m ℓ z (fun i => G.neighborFinset i) := by
  obtain ⟨h1, h2, h3⟩ := dual_vector_real hG w
  set zr := gramM G *ᵥ w with hzr
  have hzr' : zr = fun i => (z i : ℝ) := funext fun i => (hz i).symm
  have hlr : ∑ i, zr i = 7 * (ℓ : ℝ) := by
    have e : ((∑ i, z i : ℤ) : ℝ) = ((7 * ℓ : ℤ) : ℝ) := by rw [hl]
    rw [hzr']; push_cast at e ⊢; linarith
  have hw : ∑ i, w i = (ℓ : ℝ) / 34 := by rw [hlr] at h1; linarith
  refine ⟨hl, ?_, ?_, ?_, ?_⟩
  · have : (17 : ℝ) * ∑ i, (z i : ℝ) ^ 2 = 6 * m + 5 * ℓ ^ 2 := by
      have e : ∑ i, (z i : ℝ) ^ 2 = ∑ i, zr i ^ 2 := by rw [hzr']
      rw [e, h2, hw, hm]; ring
    exact_mod_cast this
  · intro i
    rw [SimpleGraph.card_neighborFinset_eq_degree, hG.regular i]
  · intro i; simp
  · intro i
    have := h3 i
    rw [hlr, hw] at this
    have e : ∑ j ∈ G.neighborFinset i, (z j : ℝ) = -16 * (z i : ℝ) + 4 * ℓ := by
      have e1 : ∑ j ∈ G.neighborFinset i, (z j : ℝ) = ∑ j ∈ G.neighborFinset i, zr j := by
        rw [hzr']
      rw [e1, this, hzr']; ring
    exact_mod_cast e

end Srg154
