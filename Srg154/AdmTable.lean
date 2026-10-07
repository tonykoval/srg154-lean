import Srg154.Certificates

/-!
# Bonus: the admissibility table for `m ≤ 110` (upper bound), kernel-checked

Computation `comp:adm` of the paper lists, from exhaustive deciders (not used in the proof), the non-forbidden
norms `m ≤ 110` and their admissible pairings.  Here the proved-sound checker shows that NO other pair with
`1 ≤ m ≤ 110` has a witness, i.e. `adm(m) ⊆` the printed list.  (It does not show that the listed pairs are
admissible, except `(33, 22)`, see `control_33_22`.)  This makes, e.g., `adm(84) ⊆ {±5}` and
`adm(100) ⊆ {±4}` (used by the second genus-I argument, Remark `rem:genusI2`) machine-checked as well.
-/

namespace Srg154

/-- the pairs `(m, |ℓ|)`, `m ≤ 110`, listed as admissible in Computation `comp:adm` -/
def admList110 : List (ℤ × ℤ) :=
  [(33, 22), (66, 4), (84, 5), (87, 18), (89, 6), (93, 2), (98, 7), (100, 4), (101, 5),
   (102, 0), (102, 17), (103, 3), (104, 1), (104, 16), (106, 6), (110, 2), (110, 15)]

/-- `⌊√(44m/3)⌋` for `m ≤ 110` is at most `40`; we scan `ℓ ∈ [0, 40]` and check the bound separately. -/
def admTableCheck : Bool :=
  (List.range 110).all fun k =>
    let m : ℤ := (k : ℤ) + 1
    decide (44 * m < 3 * 41 ^ 2) &&
    (List.range 41).all fun l => forbiddenCheck m l || decide ((m, (l : ℤ)) ∈ admList110)

theorem admTableCheck_ok : admTableCheck = true := by decide +kernel

/-- **Upper bound for the admissibility table, `1 ≤ m ≤ 110`.** -/
theorem adm_le_110 (m ℓ : ℤ) (h1 : 1 ≤ m) (h2 : m ≤ 110) (hw : HasWitness m ℓ) :
    (m, |ℓ|) ∈ admList110 := by
  have hb := hw.ell_bound
  have habs : |ℓ| ≤ 40 := by
    by_contra hc; push Not at hc
    have : (41 : ℤ) ^ 2 ≤ |ℓ| ^ 2 := by
      apply pow_le_pow_left₀ (by norm_num); omega
    rw [sq_abs] at this; linarith
  have hc := admTableCheck_ok
  simp only [admTableCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨-, hc⟩ := hc (m - 1).toNat (by omega)
  have := hc (|ℓ|).toNat (by omega)
  rw [show (((m - 1).toNat : ℕ) : ℤ) + 1 = m by omega, Int.toNat_of_nonneg (abs_nonneg ℓ)] at this
  rcases this with h | h
  · exact absurd hw (not_hasWitness_abs h)
  · exact h

theorem adm84 (ℓ : ℤ) (hw : HasWitness 84 ℓ) : ℓ = 5 ∨ ℓ = -5 := by
  have := adm_le_110 84 ℓ (by norm_num) (by norm_num) hw
  simp [admList110] at this
  rcases abs_choice ℓ with e | e <;> omega

theorem adm100 (ℓ : ℤ) (hw : HasWitness 100 ℓ) : ℓ = 4 ∨ ℓ = -4 := by
  have := adm_le_110 100 ℓ (by norm_num) (by norm_num) hw
  simp [admList110] at this
  rcases abs_choice ℓ with e | e <;> omega

end Srg154
