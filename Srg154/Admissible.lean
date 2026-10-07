import Mathlib

/-!
# Admissibility of dual-vector pairs for srg(154,72,26,40)

Formalises Definition `def:adm` of the paper (`docs/paper/srg154.tex`, Section 3) and proves the
soundness of the four one-line tests (L0)-(L3) of Lemma `lem:tools` (Section 5), in a slightly
strengthened single form.

`Witness m ℓ z Γ` is the integer content of Definition `def:adm`:
  * `∑ z = 7ℓ`,
  * `17 ∑ z² = 6m + 5ℓ²`   (i.e. `∑ z² = (6m+5ℓ²)/17`),
  * for every `i` a 72-set `Γ i ∌ i` with `∑_{j∈Γ i} z j = -16 z i + 4ℓ`.

`Admissible m ℓ` adds the side conditions of the paper (`m ≥ 1`, `3ℓ² ≤ 44 m`,
`|z i| ≤ 2 √(m/51)`, written `51 z_i² ≤ 4m`).  All non-admissibility results below are proved for the
WEAKER predicate `HasWitness m ℓ` (no side conditions), hence are STRONGER statements.
-/

open Finset

namespace Srg154

/-- The integer conditions of Definition `def:adm`. -/
def Witness (m ℓ : ℤ) (z : Fin 154 → ℤ) (Γ : Fin 154 → Finset (Fin 154)) : Prop :=
  (∑ i, z i = 7 * ℓ) ∧ (17 * ∑ i, z i ^ 2 = 6 * m + 5 * ℓ ^ 2) ∧
  (∀ i, (Γ i).card = 72) ∧ (∀ i, i ∉ Γ i) ∧
  (∀ i, ∑ j ∈ Γ i, z j = -16 * z i + 4 * ℓ)

/-- `(m, ℓ)` has an integer witness (Definition `def:adm` without its side conditions). -/
def HasWitness (m ℓ : ℤ) : Prop := ∃ z Γ, Witness m ℓ z Γ

/-- Definition `def:adm` of the paper, verbatim. -/
def Admissible (m ℓ : ℤ) : Prop :=
  1 ≤ m ∧ 3 * ℓ ^ 2 ≤ 44 * m ∧
  ∃ z : Fin 154 → ℤ, (∀ i, 51 * z i ^ 2 ≤ 4 * m) ∧ ∃ Γ, Witness m ℓ z Γ

theorem Admissible.hasWitness {m ℓ : ℤ} (h : Admissible m ℓ) : HasWitness m ℓ := by
  obtain ⟨-, -, z, -, Γ, hw⟩ := h
  exact ⟨z, Γ, hw⟩

/-- `adm(m) = -adm(m)`: replace `z` by `-z`. -/
theorem HasWitness.neg {m ℓ : ℤ} (h : HasWitness m ℓ) : HasWitness m (-ℓ) := by
  obtain ⟨z, Γ, h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun i => -z i, Γ, ?_, ?_, h3, h4, ?_⟩
  · simp [Finset.sum_neg_distrib, h1]
  · simpa only [neg_sq] using h2
  · intro i
    rw [Finset.sum_neg_distrib, h5 i]; ring

theorem hasWitness_neg_iff {m ℓ : ℤ} : HasWitness m (-ℓ) ↔ HasWitness m ℓ :=
  ⟨fun h => by simpa using h.neg, fun h => h.neg⟩

/-- Cauchy–Schwarz on `z`: a witness forces `3ℓ² ≤ 44m` (the bound `ℓ² ≤ 44m/3` of Lemma `lem:V`(i)). -/
theorem HasWitness.ell_bound {m ℓ : ℤ} (h : HasWitness m ℓ) : 3 * ℓ ^ 2 ≤ 44 * m := by
  obtain ⟨z, Γ, h1, h2, -, -, -⟩ := h
  have cs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 154))) (f := z)
  simp only [Finset.card_univ, Fintype.card_fin] at cs
  rw [h1] at cs
  push_cast at cs
  nlinarith [cs, h2]

/-! ## Shifted vectors (Lemma `lem:tools`) -/

/-- The data `d = z - γ` of Lemma `lem:tools`: `∑ d = S`, `∑ d² = Q`, `∑_{Γ i} d = t - 16 d i`. -/
structure Shifted (d : Fin 154 → ℤ) (Γ : Fin 154 → Finset (Fin 154)) (Q S t : ℤ) : Prop where
  sum : ∑ i, d i = S
  sq : ∑ i, d i ^ 2 = Q
  irr : ∀ i, i ∉ Γ i
  nbr : ∀ i, ∑ j ∈ Γ i, d j = t - 16 * d i

/-- The numbers of Lemma `lem:tools` for the shift `γ`. -/
def sigma2 (m ℓ : ℤ) : ℤ := (6 * m + 5 * ℓ ^ 2) / 17
def QQ (m ℓ γ : ℤ) : ℤ := sigma2 m ℓ - 2 * γ * (7 * ℓ) + 154 * γ ^ 2
def SS (ℓ γ : ℤ) : ℤ := 7 * ℓ - 154 * γ
def TT (ℓ γ : ℤ) : ℤ := 4 * ℓ - 88 * γ

/-- (L0): a witness forces `17 ∣ 6m + 5ℓ²`. -/
theorem Witness.L0 {m ℓ : ℤ} {z Γ} (h : Witness m ℓ z Γ) : (6 * m + 5 * ℓ ^ 2) % 17 = 0 := by
  obtain ⟨-, h2, -⟩ := h
  rw [← h2]; simp

theorem Witness.sigma2_eq {m ℓ : ℤ} {z Γ} (h : Witness m ℓ z Γ) : sigma2 m ℓ = ∑ i, z i ^ 2 := by
  obtain ⟨-, h2, -⟩ := h
  unfold sigma2; rw [← h2]; simp

/-- Shifting a witness by `γ` (first line of the proof of Lemma `lem:tools`). -/
theorem Witness.shift {m ℓ : ℤ} {z Γ} (h : Witness m ℓ z Γ) (γ : ℤ) :
    Shifted (fun i => z i - γ) Γ (QQ m ℓ γ) (SS ℓ γ) (TT ℓ γ) := by
  have hs2 := h.sigma2_eq
  obtain ⟨h1, -, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, h4, ?_⟩
  · rw [Finset.sum_sub_distrib, h1]; simp [SS]
  · have : ∀ i, (z i - γ) ^ 2 = z i ^ 2 - 2 * γ * z i + γ ^ 2 := fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1]
    simp [QQ, hs2]
  · intro i
    rw [Finset.sum_sub_distrib, h5 i]; simp [h3 i, TT]; ring

namespace Shifted

variable {d : Fin 154 → ℤ} {Γ : Fin 154 → Finset (Fin 154)} {Q S t : ℤ}

theorem abs_le_sq (x : ℤ) : |x| ≤ x ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have : 1 ≤ |x| := Int.one_le_abs hx
    rw [← sq_abs]; nlinarith

theorem sum_abs_le (h : Shifted d Γ Q S t) : ∑ i, |d i| ≤ Q := by
  rw [← h.sq]; exact Finset.sum_le_sum fun i _ => abs_le_sq (d i)

/-- (L1), first half: `|S| ≤ Q`. -/
theorem abs_S_le (h : Shifted d Γ Q S t) : |S| ≤ Q := by
  rw [← h.sum]; exact (Finset.abs_sum_le_sum_abs _ _).trans h.sum_abs_le

/-- (L1), second half: `Q ≡ S (mod 2)`. -/
theorem even_Q_sub_S (h : Shifted d Γ Q S t) : Even (Q - S) := by
  rw [← h.sq, ← h.sum, ← Finset.sum_sub_distrib]
  refine Finset.even_sum _ fun i _ => ?_
  have := Int.even_mul_succ_self (d i - 1)
  have e : (d i - 1) * (d i - 1 + 1) = d i ^ 2 - d i := by ring
  rwa [e] at this

/-- (L2): `|t - 16 d_i| ≤ Q - d_i²` for every `i`. -/
theorem nbr_abs (h : Shifted d Γ Q S t) (i : Fin 154) : |t - 16 * d i| ≤ Q - d i ^ 2 := by
  rw [← h.nbr i]
  have hsub : Γ i ⊆ Finset.univ.erase i := fun j hj =>
    Finset.mem_erase.2 ⟨fun e => h.irr i (e ▸ hj), Finset.mem_univ _⟩
  calc |∑ j ∈ Γ i, d j| ≤ ∑ j ∈ Γ i, |d j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.univ.erase i, |d j| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => abs_nonneg _
    _ ≤ ∑ j ∈ Finset.univ.erase i, d j ^ 2 := Finset.sum_le_sum fun j _ => abs_le_sq _
    _ = Q - d i ^ 2 := by
        rw [← h.sq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring

/-- (L3), lower half: `S - Q ≤ 2 (t - 16 d_i)` for every `i` (the sum over `Γ i` is at least `-P_-`). -/
theorem nbr_lower (h : Shifted d Γ Q S t) (i : Fin 154) : S - Q ≤ 2 * (t - 16 * d i) := by
  rw [← h.nbr i]
  -- 2 min(x,0) = x - |x|
  have key : ∀ x : ℤ, x - |x| ≤ 0 := fun x => by have := le_abs_self x; linarith
  have key2 : ∀ x : ℤ, x - |x| ≤ 2 * x := fun x => by have := neg_abs_le x; linarith
  calc S - Q ≤ ∑ j, (d j - |d j|) := by
        rw [Finset.sum_sub_distrib, h.sum]; linarith [h.sum_abs_le]
    _ ≤ ∑ j ∈ Γ i, (d j - |d j|) := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => -(d j - |d j|))
          (Finset.subset_univ (Γ i)) (fun j _ _ => by linarith [key (d j)])
        simp only [Finset.sum_neg_distrib] at this; linarith
    _ ≤ ∑ j ∈ Γ i, 2 * d j := Finset.sum_le_sum fun j _ => key2 _
    _ = 2 * ∑ j ∈ Γ i, d j := by rw [Finset.mul_sum]

/-- (L3), upper half: `2 (t - 16 d_i) ≤ Q + S` for every `i` (the sum over `Γ i` is at most `P_+`). -/
theorem nbr_upper (h : Shifted d Γ Q S t) (i : Fin 154) : 2 * (t - 16 * d i) ≤ Q + S := by
  rw [← h.nbr i]
  have key : ∀ x : ℤ, 0 ≤ x + |x| := fun x => by have := neg_abs_le x; linarith
  have key2 : ∀ x : ℤ, 2 * x ≤ x + |x| := fun x => by have := le_abs_self x; linarith
  calc 2 * ∑ j ∈ Γ i, d j = ∑ j ∈ Γ i, 2 * d j := by rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Γ i, (d j + |d j|) := Finset.sum_le_sum fun j _ => key2 _
    _ ≤ ∑ j, (d j + |d j|) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => key _
    _ ≤ Q + S := by rw [Finset.sum_add_distrib, h.sum]; linarith [h.sum_abs_le]

/-- The value filter: every entry `d_i` satisfies it (tests (L2) and (L3) at a single vertex). -/
def Filt (Q S t x : ℤ) : Prop :=
  |t - 16 * x| ≤ Q - x ^ 2 ∧ S - Q ≤ 2 * (t - 16 * x) ∧ 2 * (t - 16 * x) ≤ Q + S

theorem filt (h : Shifted d Γ Q S t) (i : Fin 154) : Filt Q S t (d i) :=
  ⟨h.nbr_abs i, h.nbr_lower i, h.nbr_upper i⟩

/-- If all nonzero entries equal `v`, then `Q = v S`. -/
theorem Q_eq_of_vals (h : Shifted d Γ Q S t) (v : ℤ) (hv : ∀ i, d i ≠ 0 → d i = v) : Q = v * S := by
  rw [← h.sq, ← h.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne (d i) 0 with e | e
  · simp [e]
  · rw [hv i e]; ring

/-- If there are no nonzero entries, `Q = 0`. -/
theorem Q_eq_zero_of_vals (h : Shifted d Γ Q S t) (hv : ∀ i, d i = 0) : Q = 0 := by
  rw [← h.sq]; simp [hv]

/-! ### Existence of positive / negative entries (L3) -/

def HasPos (d : Fin 154 → ℤ) : Prop := ∃ i, 1 ≤ d i
def HasNeg (d : Fin 154 → ℤ) : Prop := ∃ i, d i ≤ -1

theorem hasPos_of_S_pos (h : Shifted d Γ Q S t) (hS : 0 < S) : HasPos d := by
  by_contra hc
  simp only [HasPos, not_exists, not_le] at hc
  have : ∑ i, d i ≤ 0 := Finset.sum_nonpos fun i _ => by have := hc i; omega
  rw [h.sum] at this; omega

theorem hasNeg_of_S_neg (h : Shifted d Γ Q S t) (hS : S < 0) : HasNeg d := by
  by_contra hc
  simp only [HasNeg, not_exists, not_le] at hc
  have : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ => by have := hc i; omega
  rw [h.sum] at this; omega

theorem hasPos_of_S_zero (h : Shifted d Γ Q S t) (hS : S = 0) (hQ : 0 < Q) : HasPos d := by
  by_contra hc
  simp only [HasPos, not_exists, not_le] at hc
  have hle : ∀ i, d i ≤ 0 := fun i => by have := hc i; omega
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 154)), -d i = 0 := by
    have h0 : ∑ i, -d i = 0 := by rw [Finset.sum_neg_distrib, h.sum, hS]; simp
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => by linarith [hle i]).1 h0
  have : Q = 0 := h.Q_eq_zero_of_vals fun i => by linarith [hz i (Finset.mem_univ i)]
  omega

theorem hasNeg_of_S_zero (h : Shifted d Γ Q S t) (hS : S = 0) (hQ : 0 < Q) : HasNeg d := by
  by_contra hc
  simp only [HasNeg, not_exists, not_le] at hc
  have hle : ∀ i, 0 ≤ d i := fun i => by have := hc i; omega
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 154)), d i = 0 := by
    have h0 : ∑ i, d i = 0 := by rw [h.sum, hS]
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hle i).1 h0
  have : Q = 0 := h.Q_eq_zero_of_vals fun i => hz i (Finset.mem_univ i)
  omega

/-- If some `d_i ≥ 1` and `t < 16`, the neighbourhood sum `t - 16 d_i < 0` forces a negative entry. -/
theorem hasNeg_of_pos (h : Shifted d Γ Q S t) (hp : HasPos d) (ht : t < 16) : HasNeg d := by
  obtain ⟨i, hi⟩ := hp
  by_contra hc
  simp only [HasNeg, not_exists, not_le] at hc
  have : 0 ≤ ∑ j ∈ Γ i, d j := Finset.sum_nonneg fun j _ => by have := hc j; omega
  rw [h.nbr i] at this; omega

theorem hasPos_of_neg (h : Shifted d Γ Q S t) (hn : HasNeg d) (ht : -16 < t) : HasPos d := by
  obtain ⟨i, hi⟩ := hn
  by_contra hc
  simp only [HasPos, not_exists, not_le] at hc
  have : ∑ j ∈ Γ i, d j ≤ 0 := Finset.sum_nonpos fun j _ => by have := hc j; omega
  rw [h.nbr i] at this; omega

theorem bound_of_pos (h : Shifted d Γ Q S t) (hp : HasPos d) : S - Q ≤ 2 * (t - 16) := by
  obtain ⟨i, hi⟩ := hp
  have := h.nbr_lower i; linarith

theorem bound_of_neg (h : Shifted d Γ Q S t) (hn : HasNeg d) : 2 * (t + 16) ≤ Q + S := by
  obtain ⟨i, hi⟩ := hn
  have := h.nbr_upper i; linarith

end Shifted

end Srg154
