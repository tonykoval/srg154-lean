import Mathlib

/-!
# Item 1. Parameters of srg(154,72,26,40)

* `eig_quadratic`: the restricted eigenvalues are the roots `2, -16` of `x² - (λ-μ)x - (k-μ) = x² + 14x - 32`.
* `mult_arith`: multiplicities `f = 132`, `g = 21` from `1 + f + g = 154` and the trace `72 + 2f - 16g = 0`.
* `gram_eigen`: `G = -A + 2I + 2J` has eigenvalues `238, 0, 18` on `𝟙`, the `2`- and the `(-16)`-eigenspace.
* `srg_spectrum` (**no hypotheses beyond the graph**): for any `G : SimpleGraph (Fin 154)` with
  `G.IsSRGWith 154 72 26 40`, the Hermitian eigenvalues of the real adjacency matrix (Mathlib's
  `Matrix.IsHermitian.eigenvalues`, with multiplicity) take the value `72` once, `2` exactly 132 times and
  `-16` exactly 21 times.  Proved from Mathlib's `IsSRGWith.matrix_eq` and the spectral theorem.
-/

namespace Srg154

open Matrix

theorem eig_quadratic (x : ℝ) : x ^ 2 - (26 - 40) * x - (72 - 40) = 0 ↔ x = 2 ∨ x = -16 := by
  constructor
  · intro h
    have : (x - 2) * (x + 16) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

theorem mult_arith (f g : ℤ) (h1 : 1 + f + g = 154) (h2 : 72 + 2 * f - 16 * g = 0) :
    f = 132 ∧ g = 21 := by omega

/-- Eigenvalues of `-A + 2I + 2J` (`J = 154` on `𝟙`, `0` on `𝟙^⊥`). -/
theorem gram_eigen : -72 + 2 + 2 * 154 = (238 : ℤ) ∧ -2 + 2 = (0 : ℤ) ∧ 16 + 2 = (18 : ℤ) := by
  norm_num

/-! ## The spectrum from the graph -/

/-- all-ones matrix -/
def Jm : Matrix (Fin 154) (Fin 154) ℝ := Matrix.of fun _ _ => 1

section Spectrum

variable (A : Matrix (Fin 154) (Fin 154) ℝ)

theorem eigen_cubic (hA : A.IsHermitian)
    (hsq : A * A = (32 : ℝ) • (1 : Matrix (Fin 154) (Fin 154) ℝ) - (14 : ℝ) • A + (40 : ℝ) • Jm)
    (hreg : A * Jm = (72 : ℝ) • Jm) (i : Fin 154) :
    (hA.eigenvalues i - 72) * ((hA.eigenvalues i - 2) * (hA.eigenvalues i + 16)) = 0 := by
  set v : Fin 154 → ℝ := ⇑(hA.eigenvectorBasis i) with hvdef
  set e := hA.eigenvalues i
  have hv : A *ᵥ v = e • v := hA.mulVec_eigenvectorBasis i
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 := hA.eigenvectorBasis.orthonormal.1 i
    have : hA.eigenvectorBasis i = 0 := by
      ext k; simpa [hvdef] using congrFun h0 k
    rw [this, norm_zero] at h1; exact zero_ne_one h1
  -- (A*A) v = e² v
  have h1 : (A * A) *ᵥ v = (e * e) • v := by
    rw [← mulVec_mulVec, hv, mulVec_smul, hv, smul_smul]
  -- 40 J v = (e² + 14e - 32) v
  have h2 : (40 : ℝ) • (Jm *ᵥ v) = (e * e + 14 * e - 32) • v := by
    rw [hsq, add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hv] at h1
    rw [smul_smul] at h1
    have : (40 : ℝ) • (Jm *ᵥ v) = (e * e) • v - ((32 : ℝ) • v - (14 * e) • v) := by
      rw [← h1]; abel
    rw [this, sub_smul, add_smul]; abel
  have h3 : A *ᵥ (Jm *ᵥ v) = (72 : ℝ) • (Jm *ᵥ v) := by
    rw [mulVec_mulVec, hreg, smul_mulVec]
  have h4 := congrArg (fun x => A *ᵥ x) h2
  simp only [mulVec_smul, h3, hv, smul_smul] at h4
  -- h4 : (40*72) • Jv = (p(e) * e) • v ;  and 72 • (40 • Jv) = 72 p(e) v
  have h5 : ((40 : ℝ) * 72) • (Jm *ᵥ v) = (72 * (e * e + 14 * e - 32)) • v := by
    rw [mul_comm (40 : ℝ) 72, ← smul_smul, h2, smul_smul]
  rw [h5] at h4
  have h6 : ((72 * (e * e + 14 * e - 32)) - (e * e + 14 * e - 32) * e) • v = 0 := by
    rw [sub_smul, h4, sub_self]
  rcases smul_eq_zero.1 h6 with h | h
  · linear_combination (-1 : ℝ) * h
  · exact absurd h hv0

theorem trace_mul_self_eq (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 := by
  have hs := hA.spectral_theorem
  set U := hA.eigenvectorUnitary
  set D : Matrix (Fin 154) (Fin 154) ℝ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hAA : A * A = Unitary.conjStarAlgAut ℝ _ U (D * D) := by
    rw [map_mul, ← hs]
  rw [hAA, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self, Matrix.one_mul]
  simp [D, diagonal_mul_diagonal, trace_diagonal, sq]

end Spectrum

/-- The SRG equation `A² = 32 I - 14 A + 40 J` (from Mathlib's `IsSRGWith.matrix_eq`). -/
theorem srg_sq (G : SimpleGraph (Fin 154)) [DecidableRel G.Adj] (hG : G.IsSRGWith 154 72 26 40) :
    G.adjMatrix ℝ * G.adjMatrix ℝ =
      (32 : ℝ) • (1 : Matrix (Fin 154) (Fin 154) ℝ) - (14 : ℝ) • G.adjMatrix ℝ + (40 : ℝ) • Jm := by
  set A := G.adjMatrix ℝ with hAdef
  -- the complement's adjacency matrix is J - I - A
  have hcompl : Gᶜ.adjMatrix ℝ = Jm - 1 - A := by
    ext i j
    simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj, Jm, Matrix.sub_apply,
      Matrix.of_apply, Matrix.one_apply, hAdef]
    by_cases hij : i = j
    · subst hij; simp
    · by_cases ha : G.Adj i j <;> simp [hij, ha]
  have := hG.matrix_eq (α := ℝ)
  rw [sq, hcompl] at this
  rw [this]
  simp only [← Nat.cast_smul_eq_nsmul ℝ]
  push_cast
  module

/-- Regularity `A J = 72 J`. -/
theorem srg_reg (G : SimpleGraph (Fin 154)) [DecidableRel G.Adj] (hG : G.IsSRGWith 154 72 26 40) :
    G.adjMatrix ℝ * Jm = (72 : ℝ) • Jm := by
  ext i j
  rw [SimpleGraph.adjMatrix_mul_apply]
  simp only [Jm, Matrix.of_apply, Finset.sum_const, nsmul_eq_mul, mul_one, Matrix.smul_apply,
    smul_eq_mul]
  rw [SimpleGraph.card_neighborFinset_eq_degree, hG.regular i]
  norm_num

/-- **Item 1, from the graph.** The spectrum of an srg(154,72,26,40): eigenvalue `72` once, `2` with
multiplicity `132`, `-16` with multiplicity `21` (counted with Mathlib's Hermitian eigenvalues). -/
theorem srg_spectrum (G : SimpleGraph (Fin 154)) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 154 72 26 40) :
    let hA : (G.adjMatrix ℝ).IsHermitian := Matrix.isHermitian_iff_isSymm.2 (G.isSymm_adjMatrix)
    (Finset.univ.filter (fun i => hA.eigenvalues i = 72)).card = 1 ∧
    (Finset.univ.filter (fun i => hA.eigenvalues i = 2)).card = 132 ∧
    (Finset.univ.filter (fun i => hA.eigenvalues i = -16)).card = 21 := by
  intro hA
  set A := G.adjMatrix ℝ with hAdef
  have hsq := srg_sq G hG
  have hreg := srg_reg G hG
  have hroot := eigen_cubic A hA hsq hreg
  have hmem : ∀ i, hA.eigenvalues i = 72 ∨ hA.eigenvalues i = 2 ∨ hA.eigenvalues i = -16 := by
    intro i
    rcases mul_eq_zero.1 (hroot i) with h | h
    · left; linarith
    · rcases mul_eq_zero.1 h with h | h
      · right; left; linarith
      · right; right; linarith
  -- trace identities
  have htr1 : ∑ i, hA.eigenvalues i = 0 := by
    have := hA.trace_eq_sum_eigenvalues
    rw [SimpleGraph.trace_adjMatrix] at this
    simpa using this.symm
  have htr2 : ∑ i, hA.eigenvalues i ^ 2 = 154 * 72 := by
    rw [← trace_mul_self_eq A hA, hsq]
    simp [hAdef, Jm, Matrix.trace]
    norm_num
  -- indicator decomposition
  set a := (Finset.univ.filter (fun i => hA.eigenvalues i = 72)).card
  set b := (Finset.univ.filter (fun i => hA.eigenvalues i = 2)).card
  set c := (Finset.univ.filter (fun i => hA.eigenvalues i = -16)).card
  have ind : ∀ (F : ℝ → ℝ), ∑ i, F (hA.eigenvalues i) = F 72 * a + F 2 * b + F (-16) * c := by
    intro F
    have : ∀ i, F (hA.eigenvalues i) =
        F 72 * (if hA.eigenvalues i = 72 then 1 else 0) + F 2 * (if hA.eigenvalues i = 2 then 1 else 0)
          + F (-16) * (if hA.eigenvalues i = -16 then 1 else 0) := by
      intro i
      rcases hmem i with h | h | h <;> rw [h] <;> norm_num
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp [a, b, c]
  have e0 := ind (fun _ => 1)
  have e1 := ind id
  have e2 := ind (fun x => x ^ 2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, id] at e0 e1 e2
  rw [htr1] at e1
  rw [htr2] at e2
  norm_num at e0 e1 e2
  have ha : (a : ℝ) = 1 := by linarith
  have hb : (b : ℝ) = 132 := by linarith
  have hc : (c : ℝ) = 21 := by linarith
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hc⟩

end Srg154
