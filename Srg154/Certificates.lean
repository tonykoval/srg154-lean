import Srg154.Admissible

/-!
# The 521 forbidden pairs (Theorem `thm:forb`, Lemma `lem:special`, Proposition `prop:sixty`)

A Boolean certificate checker `forbiddenCheck m ℓ` is defined and proved SOUND
(`forbiddenCheck m ℓ = true → ¬ HasWitness m ℓ`) from the generic lemmas of `Admissible.lean`.
The checker tries the shifts `γ ∈ {-3,…,3}` and, for each, the tests
  * (L0) `17 ∤ 6m + 5ℓ²`,
  * (L1) `Q < |S|` or `Q ≢ S (mod 2)`,
  * (L2') every nonzero entry `d_i` lies in `{x ≠ 0 : Filt Q S t x}` (the set `𝒱` of (L2), intersected with the
          one-vertex bounds of (L3)); if that set is `⊆ {v}` then `Q = v S` must hold,
  * (L3)  the sign-propagation contradiction.
(L2') with the (L3) bounds is exactly the argument of Lemma `lem:special` for `(83,4)` and `(128,26)`; for the
eleven (L2) rows of the paper's table it reduces to the printed `𝒱 ∈ {∅, {1}, {-1}}`.

All 521 instances are then discharged by `decide +kernel` (kernel evaluation; no `native_decide`).
-/

namespace Srg154

open Shifted

/-! ## The checker -/

def l1Kill (Q S : ℤ) : Bool := decide (Q < S) || decide (Q < -S) || decide ((Q - S) % 2 ≠ 0)

def filtB (Q S t x : ℤ) : Bool :=
  decide (t - 16 * x ≤ Q - x ^ 2) && decide (-(t - 16 * x) ≤ Q - x ^ 2) &&
  decide (S - Q ≤ 2 * (t - 16 * x)) && decide (2 * (t - 16 * x) ≤ Q + S)

/-- candidate nonzero entries `x ∈ [-13, 13]` passing the filter -/
def vals (Q S t : ℤ) : List ℤ :=
  ((List.range 27).map (fun n : ℕ => (n : ℤ) - 13)).filter (fun x => decide (x ≠ 0) && filtB Q S t x)

def vKill (Q S t : ℤ) : Bool :=
  decide (Q ≤ 169) &&
    match vals Q S t with
    | [] => decide (Q ≠ 0)
    | [v] => decide (Q ≠ v * S)
    | _ => false

def P0 (Q S : ℤ) : Bool := decide (0 < S) || (decide (S = 0) && decide (0 < Q))
def N0 (Q S : ℤ) : Bool := decide (S < 0) || (decide (S = 0) && decide (0 < Q))
def P1 (Q S t : ℤ) : Bool := P0 Q S || (N0 Q S && decide (-16 < t))
def N1 (Q S t : ℤ) : Bool := N0 Q S || (P0 Q S && decide (t < 16))
def P2 (Q S t : ℤ) : Bool := P1 Q S t || (N1 Q S t && decide (-16 < t))
def N2 (Q S t : ℤ) : Bool := N1 Q S t || (P1 Q S t && decide (t < 16))

def l3Kill (Q S t : ℤ) : Bool :=
  (P2 Q S t && decide (2 * (t - 16) < S - Q)) || (N2 Q S t && decide (Q + S < 2 * (t + 16)))

def killQST (Q S t : ℤ) : Bool := l1Kill Q S || vKill Q S t || l3Kill Q S t

/-- The certificate checker for a pair `(m, ℓ)`. -/
def forbiddenCheck (m ℓ : ℤ) : Bool :=
  decide ((6 * m + 5 * ℓ ^ 2) % 17 ≠ 0) ||
    (List.range 7).any fun n => killQST (QQ m ℓ ((n : ℤ) - 3)) (SS ℓ ((n : ℤ) - 3)) (TT ℓ ((n : ℤ) - 3))

/-! ## Soundness -/

section Soundness

variable {d : Fin 154 → ℤ} {Γ : Fin 154 → Finset (Fin 154)} {Q S t : ℤ}

theorem l1Kill_false (h : Shifted d Γ Q S t) : l1Kill Q S = false := by
  have h1 := h.abs_S_le
  have h2 := h.even_Q_sub_S
  rw [abs_le] at h1
  have h3 : (Q - S) % 2 = 0 := Int.even_iff.1 h2
  simp only [l1Kill, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt, ne_eq, not_not]
  exact ⟨⟨by linarith, by linarith⟩, h3⟩

theorem filtB_of_filt {x : ℤ} (hf : Filt Q S t x) : filtB Q S t x = true := by
  obtain ⟨h1, h2, h3⟩ := hf
  rw [abs_le] at h1
  simp only [filtB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨by linarith, by linarith⟩, h2⟩, h3⟩

theorem mem_vals (h : Shifted d Γ Q S t) (hQ : Q ≤ 169) (i : Fin 154) (hi : d i ≠ 0) :
    d i ∈ vals Q S t := by
  have hf := h.filt i
  have hsq : d i ^ 2 ≤ 169 := by
    have := hf.1; have := abs_nonneg (t - 16 * d i); linarith
  have hb : -13 ≤ d i ∧ d i ≤ 13 := by
    constructor <;> nlinarith [sq_nonneg (d i - 13), sq_nonneg (d i + 13)]
  simp only [vals, List.mem_filter, List.mem_map, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨⟨(d i + 13).toNat, by omega, by omega⟩, hi, filtB_of_filt hf⟩

theorem vKill_false (h : Shifted d Γ Q S t) : vKill Q S t = false := by
  unfold vKill
  by_cases hQ : Q ≤ 169
  · simp only [decide_eq_true hQ, Bool.true_and]
    have hm := mem_vals h hQ
    generalize hv : vals Q S t = L at hm
    match L, hm with
    | [], hm =>
      have : ∀ i, d i = 0 := fun i => by
        by_contra hc; exact absurd (hm i hc) (by simp)
      simp [h.Q_eq_zero_of_vals this]
    | [v], hm =>
      have : ∀ i, d i ≠ 0 → d i = v := fun i hi => by simpa using hm i hi
      simp [h.Q_eq_of_vals v this]
    | _ :: _ :: _, _ => rfl
  · simp [hQ]

theorem P0_sound (h : Shifted d Γ Q S t) (hb : P0 Q S = true) : HasPos d := by
  simp only [P0, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
  rcases hb with hb | ⟨hb1, hb2⟩
  · exact h.hasPos_of_S_pos hb
  · exact h.hasPos_of_S_zero hb1 hb2

theorem N0_sound (h : Shifted d Γ Q S t) (hb : N0 Q S = true) : HasNeg d := by
  simp only [N0, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
  rcases hb with hb | ⟨hb1, hb2⟩
  · exact h.hasNeg_of_S_neg hb
  · exact h.hasNeg_of_S_zero hb1 hb2

theorem P1_sound (h : Shifted d Γ Q S t) (hb : P1 Q S t = true) : HasPos d := by
  simp only [P1, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
  rcases hb with hb | ⟨hb1, hb2⟩
  · exact P0_sound h hb
  · exact h.hasPos_of_neg (N0_sound h hb1) hb2

theorem N1_sound (h : Shifted d Γ Q S t) (hb : N1 Q S t = true) : HasNeg d := by
  simp only [N1, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
  rcases hb with hb | ⟨hb1, hb2⟩
  · exact N0_sound h hb
  · exact h.hasNeg_of_pos (P0_sound h hb1) hb2

theorem P2_sound (h : Shifted d Γ Q S t) (hb : P2 Q S t = true) : HasPos d := by
  simp only [P2, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
  rcases hb with hb | ⟨hb1, hb2⟩
  · exact P1_sound h hb
  · exact h.hasPos_of_neg (N1_sound h hb1) hb2

theorem N2_sound (h : Shifted d Γ Q S t) (hb : N2 Q S t = true) : HasNeg d := by
  simp only [N2, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
  rcases hb with hb | ⟨hb1, hb2⟩
  · exact N1_sound h hb
  · exact h.hasNeg_of_pos (P1_sound h hb1) hb2

theorem l3Kill_false (h : Shifted d Γ Q S t) : l3Kill Q S t = false := by
  rw [← Bool.not_eq_true]
  intro hb
  simp only [l3Kill, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
  rcases hb with ⟨hp, hlt⟩ | ⟨hn, hlt⟩
  · have := h.bound_of_pos (P2_sound h hp); linarith
  · have := h.bound_of_neg (N2_sound h hn); linarith

theorem killQST_false (h : Shifted d Γ Q S t) : killQST Q S t = false := by
  simp [killQST, l1Kill_false h, vKill_false h, l3Kill_false h]

end Soundness

/-- **Soundness of the certificate checker.** -/
theorem not_hasWitness_of_check {m ℓ : ℤ} (hc : forbiddenCheck m ℓ = true) : ¬ HasWitness m ℓ := by
  rintro ⟨z, Γ, hw⟩
  have h0 := hw.L0
  simp only [forbiddenCheck, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range] at hc
  rcases hc with hc | ⟨n, -, hn⟩
  · exact hc h0
  · rw [killQST_false (hw.shift _)] at hn; exact Bool.false_ne_true hn

theorem not_admissible_of_check {m ℓ : ℤ} (hc : forbiddenCheck m ℓ = true) : ¬ Admissible m ℓ :=
  fun h => not_hasWitness_of_check hc h.hasWitness

/-- Both signs of `ℓ` (since `adm(m) = -adm(m)`). -/
theorem not_hasWitness_abs {m ℓ : ℤ} (hc : forbiddenCheck m |ℓ| = true) : ¬ HasWitness m ℓ := by
  intro h
  rcases abs_choice ℓ with e | e <;> rw [e] at hc
  · exact not_hasWitness_of_check hc h
  · exact not_hasWitness_of_check hc h.neg

/-! ## Whole norms: `(a)` of Theorem `thm:forb` -/

/-- `L` is `⌊√(44m/3)⌋` and every `0 ≤ ℓ ≤ L` is certified. -/
def normCheck (m : ℤ) (L : ℕ) : Bool :=
  decide (3 * (L : ℤ) ^ 2 ≤ 44 * m) && decide (44 * m < 3 * ((L : ℤ) + 1) ^ 2) &&
    (List.range (L + 1)).all fun l => forbiddenCheck m l

theorem forbidden_of_normCheck {m : ℤ} {L : ℕ} (hc : normCheck m L = true) (ℓ : ℤ) :
    ¬ HasWitness m ℓ := by
  intro h
  simp only [normCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hc
  obtain ⟨⟨-, hL⟩, hall⟩ := hc
  have hb := h.ell_bound
  have habs : |ℓ| ≤ L := by
    by_contra hc; push Not at hc
    have : ((L : ℤ) + 1) ^ 2 ≤ |ℓ| ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); omega
    rw [sq_abs] at this; linarith
  have := hall (|ℓ|).toNat (by omega)
  rw [Int.toNat_of_nonneg (abs_nonneg ℓ)] at this
  exact not_hasWitness_abs this h

/-- The norms of `𝓕_I` and `𝓕_U` with `ℓ_max` as printed in Table `tab:lzero`. -/
def normTable : List (ℤ × ℕ) :=
  [(4, 7), (16, 15), (30, 20), (36, 22), (52, 27), (60, 29), (64, 30), (70, 32), (72, 32), (76, 33),
   (94, 37),
   (2, 5), (15, 14), (26, 19), (35, 22), (42, 24), (47, 26), (50, 27), (51, 27)]

theorem normTable_ok : normTable.all (fun p => normCheck p.1 p.2) = true := by decide +kernel

/-- **Theorem `thm:forb`(a).** Every norm of `𝓕_I ∪ 𝓕_U` is forbidden: no pairing `ℓ` has a witness. -/
theorem forb_a (m : ℤ)
    (hm : m ∈ ({4, 16, 30, 36, 52, 60, 64, 70, 72, 76, 94, 2, 15, 26, 35, 42, 47, 50, 51} : Finset ℤ))
    (ℓ : ℤ) : ¬ HasWitness m ℓ := by
  have hall := List.all_eq_true.1 normTable_ok
  have key : ∀ m ∈ ({4, 16, 30, 36, 52, 60, 64, 70, 72, 76, 94, 2, 15, 26, 35, 42, 47, 50, 51} :
      Finset ℤ), ∃ p ∈ normTable, p.1 = m := by decide
  obtain ⟨p, hp, rfl⟩ := key m hm
  exact forbidden_of_normCheck (hall p hp) ℓ

/-- **Proposition `prop:sixty`.** The key norm `20/17` (`m = 60`) is forbidden. -/
theorem sixty_forbidden (ℓ : ℤ) : ¬ HasWitness 60 ℓ := forb_a 60 (by simp) ℓ

/-! ## Roots, characteristic vectors, norm 3: `(b)`, `(c)`, `(d)` of Theorem `thm:forb` -/

def rootCond (α β : ℤ) : Bool :=
  decide (7 * α ^ 2 - 30 * α * β + 51 * β ^ 2 ≤ 264) && decide (α ^ 2 < 102) &&
    decide (1 ≤ α * (α - 3 * β)) && !(decide (α = 1) && decide (β = 0))

def rootCheck : Bool :=
  (List.range 10).all fun a => (List.range 7).all fun b =>
    let α : ℤ := (a : ℤ) + 1
    let β : ℤ := (b : ℤ) - 3
    !(rootCond α β) || forbiddenCheck (102 - α ^ 2) (17 * β - 5 * α)

theorem rootCheck_ok : rootCheck = true := by decide +kernel

/-- **Theorem `thm:forb`(b)** (roots). -/
theorem forb_b (α β : ℤ) (h1 : 1 ≤ α) (hG : 7 * α ^ 2 - 30 * α * β + 51 * β ^ 2 ≤ 264)
    (h2 : α ^ 2 < 102) (h3 : 1 ≤ α * (α - 3 * β)) (h4 : (α, β) ≠ (1, 0)) :
    ¬ HasWitness (102 - α ^ 2) (17 * β - 5 * α) := by
  have hα : α ≤ 10 := by nlinarith
  have hβ : β ^ 2 ≤ 14 := by nlinarith [sq_nonneg (7 * α - 15 * β)]
  have hβ' : -3 ≤ β ∧ β ≤ 3 := by constructor <;> nlinarith
  have hc := rootCheck_ok
  simp only [rootCheck, List.all_eq_true, List.mem_range] at hc
  have := hc (α - 1).toNat (by omega) (β + 3).toNat (by omega)
  rw [show (((α - 1).toNat : ℕ) : ℤ) + 1 = α by omega,
    show (((β + 3).toNat : ℕ) : ℤ) - 3 = β by omega] at this
  have hrc : rootCond α β = true := by
    simp only [rootCond, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨⟨hG, h2⟩, h3⟩, ?_⟩
    by_contra hc'; push Not at hc'; exact h4 (by rw [hc'.1, hc'.2])
  simp only [hrc, Bool.not_true, Bool.false_or] at this
  exact not_hasWitness_of_check this

def charCond (α β : ℤ) : Bool :=
  decide (α % 2 = 1) && decide (β % 2 = 1 ∨ β % 2 = -1) &&
    decide (7 * α ^ 2 - 30 * α * β + 51 * β ^ 2 ≤ 924) && decide (α ^ 2 < 357) &&
    !(decide (α = 15) && decide (β = 7)) &&
    !(decide ((α = 1 ∨ α = 3) ∧ 2 ≤ 3 * α * β - α ^ 2))

def charCheck : Bool :=
  (List.range 18).all fun a => (List.range 15).all fun b =>
    let α : ℤ := (a : ℤ) + 1
    let β : ℤ := (b : ℤ) - 7
    !(charCond α β) || forbiddenCheck ((357 - α ^ 2) / 4) ((17 * β - 5 * α) / 2)

theorem charCheck_ok : charCheck = true := by decide +kernel

/-- **Theorem `thm:forb`(c)** (characteristic vectors), with `4m = 357 - α²`, `2ℓ = 17β - 5α`. -/
theorem forb_c (α β m ℓ : ℤ) (h1 : 1 ≤ α) (hαo : Odd α) (hβo : Odd β)
    (hG : 7 * α ^ 2 - 30 * α * β + 51 * β ^ 2 ≤ 924) (h2 : α ^ 2 < 357)
    (h3 : (α, β) ≠ (15, 7)) (h4 : ¬ ((α = 1 ∨ α = 3) ∧ 2 ≤ 3 * α * β - α ^ 2))
    (hm : 4 * m = 357 - α ^ 2) (hl : 2 * ℓ = 17 * β - 5 * α) :
    ¬ HasWitness m ℓ := by
  have hα : α ≤ 18 := by nlinarith
  have hβ : β ^ 2 ≤ 49 := by nlinarith [sq_nonneg (7 * α - 15 * β)]
  have hβ' : -7 ≤ β ∧ β ≤ 7 := by constructor <;> nlinarith
  have hc := charCheck_ok
  simp only [charCheck, List.all_eq_true, List.mem_range] at hc
  have := hc (α - 1).toNat (by omega) (β + 7).toNat (by omega)
  rw [show (((α - 1).toNat : ℕ) : ℤ) + 1 = α by omega,
    show (((β + 7).toNat : ℕ) : ℤ) - 7 = β by omega] at this
  obtain ⟨k, hk⟩ := hαo
  obtain ⟨j, hj⟩ := hβo
  have hcc : charCond α β = true := by
    simp only [charCond, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.or_eq_true]
    refine ⟨⟨⟨⟨⟨by omega, by omega⟩, hG⟩, h2⟩, ?_⟩, ?_⟩
    · by_contra hc'; push Not at hc'; exact h3 (by rw [hc'.1, hc'.2])
    · exact h4
  simp only [hcc, Bool.not_true, Bool.false_or] at this
  rw [show (357 - α ^ 2) / 4 = m by omega, show (17 * β - 5 * α) / 2 = ℓ by omega] at this
  exact not_hasWitness_of_check this

def norm3Check : Bool :=
  (List.range 12).all fun a =>
    let α : ℤ := (a : ℤ) + 1
    decide (α = 7) || forbiddenCheck (153 - α ^ 2) (51 - 5 * α)

theorem norm3Check_ok : norm3Check = true := by decide +kernel

/-- **Theorem `thm:forb`(d)** (norm 3). -/
theorem forb_d (α : ℤ) (h1 : 1 ≤ α) (h2 : α ≤ 12) (h3 : α ≠ 7) :
    ¬ HasWitness (153 - α ^ 2) (51 - 5 * α) := by
  have hc := norm3Check_ok
  simp only [norm3Check, List.all_eq_true, List.mem_range] at hc
  have := hc (α - 1).toNat (by omega)
  rw [show (((α - 1).toNat : ℕ) : ℤ) + 1 = α by omega] at this
  simp only [Bool.or_eq_true, decide_eq_true_eq, h3, false_or] at this
  exact not_hasWitness_of_check this

/-- **Lemma `lem:special`.** -/
theorem special_83_4 : ¬ HasWitness 83 4 := not_hasWitness_of_check (by decide +kernel)
theorem special_128_26 : ¬ HasWitness 128 26 := not_hasWitness_of_check (by decide +kernel)

/-! ## The list of the 521 pairs (for cross-checking against the paper's program) -/

def pairsNorms : List (ℤ × ℤ) :=
  normTable.flatMap fun p => (List.range (p.2 + 1)).map fun l => (p.1, (l : ℤ))

def pairsRoots : List (ℤ × ℤ) :=
  (List.range 10).flatMap fun a => ((List.range 7).filter fun b =>
      rootCond ((a : ℤ) + 1) ((b : ℤ) - 3)).map fun b =>
    (102 - ((a : ℤ) + 1) ^ 2, |17 * ((b : ℤ) - 3) - 5 * ((a : ℤ) + 1)|)

def pairsChars : List (ℤ × ℤ) :=
  (List.range 18).flatMap fun a => ((List.range 15).filter fun b =>
      charCond ((a : ℤ) + 1) ((b : ℤ) - 7)).map fun b =>
    ((357 - ((a : ℤ) + 1) ^ 2) / 4, |17 * ((b : ℤ) - 7) - 5 * ((a : ℤ) + 1)| / 2)

def pairsNorm3 : List (ℤ × ℤ) :=
  ((List.range 12).filter fun a => (a : ℤ) + 1 ≠ 7).map fun a =>
    (153 - ((a : ℤ) + 1) ^ 2, |51 - 5 * ((a : ℤ) + 1)|)

def pairs521 : List (ℤ × ℤ) := pairsNorms ++ pairsRoots ++ pairsChars ++ pairsNorm3

theorem pairs521_length : pairs521.length = 521 := by decide +kernel

/-- All 521 pairs of Theorem `thm:forb` pass the certified checker. -/
theorem pairs521_all : pairs521.all (fun p => forbiddenCheck p.1 p.2) = true := by decide +kernel

theorem pairs521_forbidden : ∀ p ∈ pairs521, ¬ HasWitness p.1 p.2 := fun p hp =>
  not_hasWitness_of_check (List.all_eq_true.1 pairs521_all p hp)


/-! ## Positive control: the predicate is not vacuous

`x = y/2` gives `(m, ℓ) = (33, 22)` with `z = 𝟙` (Remark `rem:lemU`); here it is an honest witness of
Definition `def:adm` (any 72-sets avoiding `i` work, since `z` is constant). The checker must not (and,
by soundness, cannot) kill it; `forbiddenCheck 33 22 = false` is confirmed below as well. -/

def ctrlΓ (i : Fin 154) : Finset (Fin 154) :=
  if i.val < 72 then Finset.univ.filter (fun j => 72 ≤ j.val ∧ j.val < 144)
  else Finset.univ.filter (fun j => j.val < 72)

theorem control_33_22 : Admissible 33 22 := by
  refine ⟨by norm_num, by norm_num, fun _ => 1, fun _ => by norm_num, ctrlΓ, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro i; unfold ctrlΓ; split_ifs <;> decide
  · intro i; unfold ctrlΓ; split_ifs with h <;> simp <;> omega
  · intro i
    have : (ctrlΓ i).card = 72 := by unfold ctrlΓ; split_ifs <;> decide
    simp [this]

theorem control_check_33_22 : forbiddenCheck 33 22 = false := by decide +kernel

end Srg154
