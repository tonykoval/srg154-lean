import Srg154.Certificates

/-!
# The printed certificate tables of Appendix `app:cert`, checked row by row

`paperL0` and `paperCert` are Tables `tab:lzero` and `tab:cert` of `docs/paper/srg154.tex`, transcribed by
`gen_tables.py` (a parser of the .tex source; no numbers typed by hand).  For each printed row of
`tab:cert`, `rowCheck` verifies that `(6m+5ℓ²) ≡ 0 (mod 17)`, that the printed `Q, S, t` are the numbers of
Lemma `lem:tools` at the printed shift `γ`, and that the NAMED test fails:
  * L1: `Q < |S|` or `Q ≢ S (mod 2)`;
  * L2: the printed `𝒱` equals `{d ≠ 0 : |t - 16d| ≤ Q - d²}` and no combination of it gives `(S, Q)`
        (all printed `𝒱` are `∅`, `{1}`, `{-1}`);
  * L3: the printed `P^max_± = (Q ± S)/2` and the sign conditions of (L3) contradict each other;
  * Lemma `lem:special`: the argument of its proof (the (L2) set refined by the (L3) bounds is `{1}`, `Q ≠ S`).
`rowCheck_sound` proves that a passing row is not admissible.  All rows are discharged by `decide +kernel`,
and the tables are checked to cover exactly the 521 pairs (414 failing (L0), 107 printed rows split 83/11/11/2).
-/

namespace Srg154

open Shifted

inductive Test where
  | L1
  | L2 (V : List ℤ)
  | L3 (Pmax Nmax : ℤ)
  | special
  deriving DecidableEq, Repr

structure CertRow where
  m : ℤ
  ℓ : ℤ
  test : Test
  γ : ℤ
  Q : ℤ
  S : ℤ
  t : ℤ
  deriving Repr

/-- Table `tab:lzero` as printed in the paper: `(m, ℓ_max, the ℓ passing (L0))`. -/
def paperL0 : List (ℤ × ℕ × List ℤ) := [
  (4, 7, [6]),
  (16, 15, [5, 12]),
  (30, 20, [7, 10]),
  (36, 22, [1, 16, 18]),
  (52, 27, [3, 14, 20]),
  (60, 29, [8, 9, 25, 26]),
  (64, 30, [7, 10, 24, 27]),
  (70, 32, [1, 16, 18]),
  (72, 32, [6, 11, 23, 28]),
  (76, 33, [2, 15, 19, 32]),
  (94, 37, [8, 9, 25, 26]),
  (2, 5, [1]),
  (15, 14, [4, 13]),
  (26, 19, [8, 9]),
  (35, 22, [3, 14, 20]),
  (42, 24, [2, 15, 19]),
  (47, 26, [7, 10, 24]),
  (50, 27, [5, 12, 22]),
  (51, 27, [0, 17])]

/-- Table `tab:cert` as printed in the paper: `⟨m, ℓ, test, γ, Q, S, t⟩`. -/
def paperCert : List CertRow := [
  ⟨4, 6, Test.L1, 0, 12, 42, 24⟩,
  ⟨16, 5, Test.L1, 0, 13, 35, 20⟩,
  ⟨16, 12, Test.L1, 1, 34, -70, -40⟩,
  ⟨30, 7, Test.L1, 0, 25, 49, 28⟩,
  ⟨30, 10, Test.L1, 0, 40, 70, 40⟩,
  ⟨36, 1, Test.L2 [1], 0, 13, 7, 4⟩,
  ⟨36, 16, Test.L1, 1, 18, -42, -24⟩,
  ⟨36, 18, Test.L1, 1, 10, -28, -16⟩,
  ⟨52, 3, Test.L3 21 0, 0, 21, 21, 12⟩,
  ⟨52, 14, Test.L1, 1, 34, -56, -32⟩,
  ⟨52, 20, Test.L1, 1, 10, -14, -8⟩,
  ⟨60, 8, Test.L1, 0, 40, 56, 32⟩,
  ⟨60, 9, Test.L1, 0, 45, 63, 36⟩,
  ⟨60, 25, Test.L1, 1, 9, 21, 12⟩,
  ⟨60, 26, Test.L1, 1, 10, 28, 16⟩,
  ⟨64, 7, Test.L1, 0, 37, 49, 28⟩,
  ⟨64, 10, Test.L1, 0, 52, 70, 40⟩,
  ⟨64, 24, Test.L1, 1, 10, 14, 8⟩,
  ⟨64, 27, Test.L1, 1, 13, 35, 20⟩,
  ⟨70, 1, Test.L3 16 9, 0, 25, 7, 4⟩,
  ⟨70, 16, Test.L1, 1, 30, -42, -24⟩,
  ⟨70, 18, Test.L1, 1, 22, -28, -16⟩,
  ⟨72, 6, Test.L1, 0, 36, 42, 24⟩,
  ⟨72, 11, Test.L1, 0, 61, 77, 44⟩,
  ⟨72, 23, Test.L2 [1], 1, 13, 7, 4⟩,
  ⟨72, 28, Test.L1, 1, 18, 42, 24⟩,
  ⟨76, 2, Test.L3 21 7, 0, 28, 14, 8⟩,
  ⟨76, 15, Test.L1, 1, 37, -49, -28⟩,
  ⟨76, 19, Test.L3 0 21, 1, 21, -21, -12⟩,
  ⟨76, 32, Test.L1, 1, 34, 70, 40⟩,
  ⟨94, 8, Test.L1, 0, 52, 56, 32⟩,
  ⟨94, 9, Test.L1, 0, 57, 63, 36⟩,
  ⟨94, 25, Test.L3 21 0, 1, 21, 21, 12⟩,
  ⟨94, 26, Test.L1, 1, 22, 28, 16⟩,
  ⟨2, 1, Test.L1, 0, 1, 7, 4⟩,
  ⟨15, 4, Test.L1, 0, 10, 28, 16⟩,
  ⟨15, 13, Test.L1, 1, 27, -63, -36⟩,
  ⟨26, 8, Test.L1, 0, 28, 56, 32⟩,
  ⟨26, 9, Test.L1, 0, 33, 63, 36⟩,
  ⟨35, 3, Test.L1, 0, 15, 21, 12⟩,
  ⟨35, 14, Test.L1, 1, 28, -56, -32⟩,
  ⟨35, 20, Test.L1, 1, 4, -14, -8⟩,
  ⟨42, 2, Test.L2 [1], 0, 16, 14, 8⟩,
  ⟨42, 15, Test.L1, 1, 25, -49, -28⟩,
  ⟨42, 19, Test.L1, 1, 9, -21, -12⟩,
  ⟨47, 7, Test.L1, 0, 31, 49, 28⟩,
  ⟨47, 10, Test.L1, 0, 46, 70, 40⟩,
  ⟨47, 24, Test.L1, 1, 4, 14, 8⟩,
  ⟨50, 5, Test.L1, 0, 25, 35, 20⟩,
  ⟨50, 12, Test.L1, 1, 46, -70, -40⟩,
  ⟨50, 22, Test.L2 [], 1, 6, 0, 0⟩,
  ⟨51, 0, Test.L3 9 9, 0, 18, 0, 0⟩,
  ⟨51, 17, Test.L1, 1, 19, -35, -20⟩,
  ⟨101, 22, Test.L3 12 12, 1, 24, 0, 0⟩,
  ⟨98, 27, Test.L1, 1, 25, 35, 20⟩,
  ⟨98, 10, Test.L1, 0, 64, 70, 40⟩,
  ⟨93, 32, Test.L1, 1, 40, 70, 40⟩,
  ⟨93, 15, Test.L1, 1, 43, -49, -28⟩,
  ⟨86, 20, Test.L2 [-1], 1, 22, -14, -8⟩,
  ⟨86, 3, Test.L3 27 6, 0, 33, 21, 12⟩,
  ⟨77, 25, Test.L1, 1, 15, 21, 12⟩,
  ⟨77, 8, Test.L1, 0, 46, 56, 32⟩,
  ⟨66, 30, Test.L1, 1, 22, 56, 32⟩,
  ⟨66, 13, Test.L1, 1, 45, -63, -36⟩,
  ⟨53, 18, Test.L1, 1, 16, -28, -16⟩,
  ⟨53, 1, Test.L2 [1], 0, 19, 7, 4⟩,
  ⟨38, 23, Test.L1, 1, 1, 7, 4⟩,
  ⟨38, 6, Test.L1, 0, 24, 42, 24⟩,
  ⟨21, 11, Test.L1, 0, 43, 77, 44⟩,
  ⟨2, 1, Test.L1, 0, 1, 7, 4⟩,
  ⟨89, 28, Test.L1, 1, 24, 42, 24⟩,
  ⟨89, 11, Test.L1, 0, 67, 77, 44⟩,
  ⟨87, 33, Test.L1, 1, 43, 77, 44⟩,
  ⟨87, 16, Test.L1, 1, 36, -42, -24⟩,
  ⟨87, 1, Test.L3 19 12, 0, 31, 7, 4⟩,
  ⟨83, 21, Test.L2 [-1], 1, 19, -7, -4⟩,
  ⟨83, 4, Test.special, 0, 34, 28, 16⟩,
  ⟨83, 13, Test.L1, 1, 51, -63, -36⟩,
  ⟨83, 30, Test.L1, 1, 28, 56, 32⟩,
  ⟨77, 26, Test.L1, 1, 16, 28, 16⟩,
  ⟨77, 9, Test.L1, 0, 51, 63, 36⟩,
  ⟨77, 8, Test.L1, 0, 46, 56, 32⟩,
  ⟨77, 25, Test.L1, 1, 15, 21, 12⟩,
  ⟨69, 31, Test.L1, 1, 27, 63, 36⟩,
  ⟨69, 14, Test.L1, 1, 40, -56, -32⟩,
  ⟨69, 3, Test.L3 24 3, 0, 27, 21, 12⟩,
  ⟨69, 20, Test.L2 [-1], 1, 16, -14, -8⟩,
  ⟨59, 19, Test.L1, 1, 15, -21, -12⟩,
  ⟨59, 2, Test.L2 [1], 0, 22, 14, 8⟩,
  ⟨59, 15, Test.L1, 1, 31, -49, -28⟩,
  ⟨47, 24, Test.L1, 1, 4, 14, 8⟩,
  ⟨47, 7, Test.L1, 0, 31, 49, 28⟩,
  ⟨47, 10, Test.L1, 0, 46, 70, 40⟩,
  ⟨33, 12, Test.L1, 1, 40, -70, -40⟩,
  ⟨33, 5, Test.L1, 0, 19, 35, 20⟩,
  ⟨17, 0, Test.L2 [], 0, 6, 0, 0⟩,
  ⟨152, 46, Test.L1, 2, 4, 14, 8⟩,
  ⟨149, 41, Test.L1, 2, 15, -21, -12⟩,
  ⟨144, 36, Test.L1, 2, 40, -56, -32⟩,
  ⟨137, 31, Test.L1, 1, 51, 63, 36⟩,
  ⟨128, 26, Test.special, 1, 34, 28, 16⟩,
  ⟨117, 21, Test.L3 12 19, 1, 31, -7, -4⟩,
  ⟨89, 11, Test.L1, 0, 67, 77, 44⟩,
  ⟨72, 6, Test.L1, 0, 36, 42, 24⟩,
  ⟨53, 1, Test.L2 [1], 0, 19, 7, 4⟩,
  ⟨32, 4, Test.L1, 0, 16, 28, 16⟩,
  ⟨9, 9, Test.L1, 0, 27, 63, 36⟩]

/-- the set `𝒱` of (L2), exactly as in the paper, on the window `[-13, 13]` -/
def paperV (Q t : ℤ) : List ℤ :=
  ((List.range 27).map (fun n : ℕ => (n : ℤ) - 13)).filter
    (fun d => decide (d ≠ 0) && decide (t - 16 * d ≤ Q - d ^ 2) && decide (-(t - 16 * d) ≤ Q - d ^ 2))

def l2Paper (V : List ℤ) (Q S t : ℤ) : Bool :=
  decide (Q ≤ 169) && decide (paperV Q t = V) &&
    match V with
    | [] => decide (Q ≠ 0)
    | [v] => decide (Q ≠ v * S)
    | _ => false

def rowCheck (r : CertRow) : Bool :=
  decide ((6 * r.m + 5 * r.ℓ ^ 2) % 17 = 0) && decide (r.Q = QQ r.m r.ℓ r.γ) &&
    decide (r.S = SS r.ℓ r.γ) && decide (r.t = TT r.ℓ r.γ) &&
    match r.test with
    | .L1 => l1Kill r.Q r.S
    | .L2 V => l2Paper V r.Q r.S r.t
    | .L3 P N => decide (2 * P = r.Q + r.S) && decide (2 * N = r.Q - r.S) && l3Kill r.Q r.S r.t
    | .special => vKill r.Q r.S r.t

section Soundness

variable {d : Fin 154 → ℤ} {Γ : Fin 154 → Finset (Fin 154)} {Q S t : ℤ}

theorem mem_paperV (h : Shifted d Γ Q S t) (hQ : Q ≤ 169) (i : Fin 154) (hi : d i ≠ 0) :
    d i ∈ paperV Q t := by
  have h1 := h.nbr_abs i
  have hsq : d i ^ 2 ≤ 169 := by have := abs_nonneg (t - 16 * d i); linarith
  have hb : -13 ≤ d i ∧ d i ≤ 13 := by
    constructor <;> nlinarith [sq_nonneg (d i - 13), sq_nonneg (d i + 13)]
  rw [abs_le] at h1
  simp only [paperV, List.mem_filter, List.mem_map, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨⟨(d i + 13).toNat, by omega, by omega⟩, ⟨hi, by linarith⟩, by linarith⟩

theorem l2Paper_false (h : Shifted d Γ Q S t) (V : List ℤ) : l2Paper V Q S t = false := by
  unfold l2Paper
  by_cases hQ : Q ≤ 169
  · by_cases hV : paperV Q t = V
    · simp only [decide_eq_true hQ, decide_eq_true hV, Bool.true_and]
      have hm := mem_paperV h hQ
      rw [hV] at hm
      match V, hm with
      | [], hm =>
        have : ∀ i, d i = 0 := fun i => by
          by_contra hc; exact absurd (hm i hc) (by simp)
        simp [h.Q_eq_zero_of_vals this]
      | [v], hm =>
        have : ∀ i, d i ≠ 0 → d i = v := fun i hi => by simpa using hm i hi
        simp [h.Q_eq_of_vals v this]
      | _ :: _ :: _, _ => rfl
    · simp [hV]
  · simp [hQ]

end Soundness

/-- **Soundness of a printed row.** -/
theorem rowCheck_sound (r : CertRow) (hr : rowCheck r = true) : ¬ HasWitness r.m r.ℓ := by
  rintro ⟨z, Γ, hw⟩
  have hs := hw.shift r.γ
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨-, hQ⟩, hS⟩, ht⟩, htest⟩ := hr
  rw [← hQ, ← hS, ← ht] at hs
  revert htest
  cases r.test with
  | L1 => simp [l1Kill_false hs]
  | L2 V => simp [l2Paper_false hs V]
  | L3 P N => simp [l3Kill_false hs]
  | special => simp [vKill_false hs]

theorem paperCert_ok : paperCert.all rowCheck = true := by decide +kernel

theorem paperCert_length : paperCert.length = 107 := by decide +kernel

/-- the split `83 / 11 / 11 / 2` of the printed table -/
theorem paperCert_split :
    (paperCert.filter fun r => decide (r.test = .L1)).length = 83 ∧
    (paperCert.filter fun r => match r.test with | .L2 _ => true | _ => false).length = 11 ∧
    (paperCert.filter fun r => match r.test with | .L3 _ _ => true | _ => false).length = 11 ∧
    (paperCert.filter fun r => decide (r.test = .special)).length = 2 := by decide +kernel

def passL0 (p : ℤ × ℤ) : Bool := decide ((6 * p.1 + 5 * p.2 ^ 2) % 17 = 0)

/-- The printed rows are exactly the pairs of `pairs521` passing (L0), in the same order. -/
theorem paperCert_matches_pairs521 :
    paperCert.map (fun r => (r.m, r.ℓ)) = pairs521.filter passL0 := by decide +kernel

/-- 414 of the 521 pairs fail (L0). -/
theorem L0_count : (pairs521.filter fun p => !passL0 p).length = 414 := by decide +kernel

/-- Table `tab:lzero`: the norms and `ℓ_max` agree with `normTable`, and the printed lists are exactly the
`ℓ ∈ [0, ℓ_max]` passing (L0). -/
theorem paperL0_ok :
    paperL0.map (fun p => (p.1, p.2.1)) = normTable ∧
    paperL0.all (fun p => decide (((List.range (p.2.1 + 1)).map (fun l : ℕ => (l : ℤ))).filter
      (fun l => passL0 (p.1, l)) = p.2.2)) = true := by decide +kernel

/-- **Second route to Theorem `thm:forb`, via the printed tables only.** Every one of the 521 pairs is
not admissible: either it fails (L0), or its printed row of Table `tab:cert` is verified. -/
theorem pairs521_forbidden_by_paper_tables : ∀ p ∈ pairs521, ¬ HasWitness p.1 p.2 := by
  intro p hp ⟨z, Γ, hw⟩
  by_cases h0 : passL0 p = true
  · have hmem : p ∈ paperCert.map (fun r => (r.m, r.ℓ)) := by
      rw [paperCert_matches_pairs521]; exact List.mem_filter.2 ⟨hp, h0⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hmem
    exact rowCheck_sound r (List.all_eq_true.1 paperCert_ok r hr) ⟨z, Γ, hw⟩
  · simp only [passL0, decide_eq_true_eq] at h0
    exact h0 hw.L0

end Srg154
