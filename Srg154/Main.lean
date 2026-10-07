import Srg154.Parameters
import Srg154.DualVector
import Srg154.Certificates
import Srg154.GenusI
import Srg154.GenusII

/-!
# Capstone: what the formalisation establishes

`no_host_conditional` says: neither of the two host configurations of Proposition `prop:forms` can exist,
where each configuration is packaged with exactly the hypotheses that are NOT formalised here
(gluing / Niemeier E2 for genus I; gluing, the frame identity E3 and the 7-design property E4 for genus II;
and, in both, the lattice facts that turn a dual vector of `N` into integer data for `dual_vector_witness`).

The step "srg(154,72,26,40) exists ⇒ one of the two packages exists" (vertex lattice, `y = s/119`, maximal even
overlattice, Milgram's formula, gluing) is NOT formalised; see README.md.
-/

namespace Srg154

open RealInnerProductSpace

/-- Hypothesis package for a host of type (I), in the coordinates given by E2 (`X ≅ A₁²⁴`). -/
structure GenusIHost where
  𝒢 : Set (Fin 24 → ZMod 2)
  zero_mem : (0 : Fin 24 → ZMod 2) ∈ 𝒢
  weights : ∀ c ∈ 𝒢, c ≠ 0 → wt c ∈ ({8, 12, 16, 24} : Finset ℕ)
  x : Fin 24 → ℤ
  x_mem : mod2 x ∈ 𝒢
  x0 : x 0 = 1
  xx : dot x x = 52
  adm : ∀ v : Fin 24 → ℤ, mod2 v ∈ 𝒢 → ∀ m : ℤ, (m : ℚ) = mI x v → m ≠ 0 → ∃ ℓ, HasWitness m ℓ

/-- Hypothesis package for a host of type (II): the glue configuration together with E3 and E4. -/
structure GenusIIHost (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  K : Config E
  frame : (∀ v ∈ K.U, ⟪v, v⟫ ≠ 1) → ∃ R C : Finset E, FrameIdentity K.U R C
  design : (∀ v ∈ K.U, ⟪v, v⟫ ≠ 1) → (∀ v ∈ K.U, ⟪v, v⟫ ≠ 2) →
    ∃ Ψ : Finset E, (∀ v ∈ Ψ, v ∈ K.U ∧ ⟪v, v⟫ = 3) ∧ DesignMoments Ψ

theorem no_genusI_host : IsEmpty GenusIHost :=
  ⟨fun H => genusI_impossible H.𝒢 H.zero_mem H.weights H.x H.x_mem H.x0 H.xx H.adm⟩

theorem no_genusII_host (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    IsEmpty (GenusIIHost E) :=
  ⟨fun H => genusII_impossible H.K H.frame H.design⟩

/-- **Main conditional theorem.** -/
theorem no_host_conditional (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    IsEmpty GenusIHost ∧ IsEmpty (GenusIIHost E) :=
  ⟨no_genusI_host, no_genusII_host E⟩

/-- The design constants `ν_k = 4600 · 3^k · (1·3⋯(2k-1)) / (23·25⋯(21+2k))` of Lemma `lem:design`, and the
value `-2880` of Theorem `thm:B`. -/
theorem design_constants :
    (4600 : ℚ) * 3 / 23 = 600 ∧ (4600 : ℚ) * 3 ^ 2 * 3 / (23 * 25) = 216 ∧
    (4600 : ℚ) * 3 ^ 3 * (3 * 5) / (23 * 25 * 27) = 120 ∧
    ((120 : ℤ) * 7 ^ 2 - 5 * 216 * 7 + 4 * 600) * (3 * 15 - 7 * 7) = -2880 := by
  norm_num

end Srg154
