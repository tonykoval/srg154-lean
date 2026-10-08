import Srg154.Main
import Srg154.VertexLattice
import Srg154.GenusIReduce

/-! Literal exports of (eq:adm) and the geometric Lemma A1 hypothesis.
Contributed by the independent review C30 (Codex), 2026-10-08, kernel-checked against this API. -/

namespace Srg154.Exports

open Srg154 RealInnerProductSpace

variable {graph : SimpleGraph (Fin 154)} [DecidableRel graph.Adj]
variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
variable {vertices : Fin 154 → Space} {lattice : AddSubgroup Space}

theorem full_admissibility (parameters : graph.IsSRGWith 154 72 26 40)
    (representation : IsRep graph vertices) (maximal : MaxEven vertices lattice)
    {vector : Space} (dual : vector ∈ Dual vertices lattice) (nonzero : vector ≠ 0) :
    ∃ numerator pairing : ℤ, (numerator : ℝ) = 51 * ⟪vector, vector⟫ ∧
      (pairing : ℝ) = 17 * ⟪yv vertices, vector⟫ ∧ Admissible numerator pairing := by
  obtain ⟨numerator, pairing, norm_identity, pairing_identity, values, coordinates, witness⟩ :=
    eq_adm parameters representation maximal dual
  have positive : (0 : ℝ) < numerator := by
    rw [norm_identity]
    exact mul_pos (by norm_num) (real_inner_self_pos.2 nonzero)
  have positive_integer : (0 : ℤ) < numerator := by exact_mod_cast positive
  refine ⟨numerator, pairing, norm_identity, pairing_identity, by omega,
    HasWitness.ell_bound ⟨values, _, witness⟩, values, ?_, _, witness⟩
  intro index
  have diagonal : ⟪vertices index, vertices index⟫ = 4 := by
    rw [representation]
    norm_num [gramM, Jm]
  have bound := real_inner_mul_inner_self_le (vertices index) vector
  rw [diagonal, ← coordinates index] at bound
  have real_bound : (51 : ℝ) * (values index : ℝ) ^ 2 ≤ 4 * numerator := by
    rw [norm_identity]
    nlinarith
  exact_mod_cast real_bound

theorem dual_has_nontrivial_class (parameters : graph.IsSRGWith 154 72 26 40)
    (representation : IsRep graph vertices) (maximal : MaxEven vertices lattice) :
    yv vertices ∈ Dual vertices lattice ∧ yv vertices ∉ lattice := by
  exact ⟨⟨y_mem, fun _ membership => maximal.inner_y parameters representation membership⟩,
    maximal.y_not_mem parameters representation⟩

theorem root_projection_nonzero (root distinguished candidate : Space)
    (root_norm : ⟪root, root⟫ = 2) (root_pair : ⟪root, distinguished⟫ = 1)
    (distinguished_norm : ⟪distinguished, distinguished⟫ = 26)
    (candidate_norm : ⟪candidate, candidate⟫ = 2)
    (alpha beta : ℤ) (alpha_pair : ⟪candidate, root⟫ = alpha)
    (beta_pair : ⟪candidate, distinguished⟫ = beta)
    (not_root : candidate ≠ root) (not_negative_root : candidate ≠ -root) :
    projI root distinguished candidate ≠ 0 := by
  intro zero_projection
  obtain ⟨_, _, norm_projection⟩ := projI_spec root distinguished candidate root_norm root_pair distinguished_norm
  rw [zero_projection, inner_zero_left, candidate_norm, alpha_pair, beta_pair] at norm_projection
  have equation : (26 * alpha ^ 2 - 2 * alpha * beta + 2 * beta ^ 2 : ℤ) = 102 := by
    have real_equation : (26 : ℝ) * alpha ^ 2 - 2 * alpha * beta + 2 * beta ^ 2 = 102 := by
      linarith
    exact_mod_cast real_equation
  have alpha_bounds : -2 ≤ alpha ∧ alpha ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg (2 * beta - alpha)]
  have beta_bounds : -8 ≤ beta ∧ beta ≤ 8 := by
    constructor <;> nlinarith [sq_nonneg (26 * alpha - beta)]
  have cases : (alpha = 2 ∧ beta = 1) ∨ (alpha = -2 ∧ beta = -1) := by
    obtain ⟨alpha_lower, alpha_upper⟩ := alpha_bounds
    obtain ⟨beta_lower, beta_upper⟩ := beta_bounds
    interval_cases alpha <;> interval_cases beta <;> omega
  have reversed_pair : ⟪root, candidate⟫ = (alpha : ℝ) := by
    rw [real_inner_comm]
    exact alpha_pair
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have difference : ⟪candidate - root, candidate - root⟫ = 0 := by
      simp only [inner_sub_left, inner_sub_right, reversed_pair,
        candidate_norm, root_norm, alpha_pair]
      norm_num
    exact not_root (sub_eq_zero.1 ((inner_self_eq_zero (𝕜 := ℝ)).1 difference))
  · have total : ⟪candidate + root, candidate + root⟫ = 0 := by
      simp only [inner_add_left, inner_add_right, reversed_pair,
        candidate_norm, root_norm, alpha_pair]
      norm_num
    exact not_negative_root (eq_neg_of_add_eq_zero_left ((inner_self_eq_zero (𝕜 := ℝ)).1 total))


end Srg154.Exports
