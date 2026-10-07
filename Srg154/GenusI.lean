import Srg154.Certificates

/-!
# Item 5. Genus I (Section `sec:genusI`)

* `projI`: the projection formula `(eq:projI)`: for `K_I = ℤr ⊕ ℤf` with Gram `[[2,1],[1,26]]`, the
  orthogonal projection `π` onto `K_I^⊥` satisfies `51 π(v)² = 51 v² - (26a² - 2ab + 2b²)`,
  `a = ⟨v,r⟩`, `b = ⟨v,f⟩` (proved in any real inner product space).
* `lemmaA1_arith`: the arithmetic of Lemma `lem:A1`: a root `ρ ≠ ±r` whose projection is not forbidden
  (graph hypothesis) has `⟨ρ,r⟩ = 0` and `⟨ρ,f⟩ ∈ {0,±1,±3}`.
* `genusI_impossible`: Theorem `thm:genusI` in coordinates.  After E2 (`X ≅ A_1^{24}`, external input,
  HYPOTHESIS) we may write `X = {v/√2 : v ∈ ℤ²⁴, v mod 2 ∈ 𝒢}`, `r = √2 e₀`, `f = x/√2`.  We model
  `v/√2` by the integer vector `v` with inner product `(v·v')/2`.  Hypotheses: `𝒢` contains `0` and all its
  nonzero words have weight `8, 12, 16` or `24` (Golay code weights, E2); `x mod 2 ∈ 𝒢`, `x₀ = 1`,
  `∑ xᵢ² = 52` (i.e. `⟨r,f⟩ = 1`, `f² = 26`); and the graph hypothesis `(eq:adm)` for the projections of
  vectors of `X` (with `(eq:projI)`).  Lean then derives `xᵢ ∈ {0,±1,±3}` from the forbidden norms, the
  dodecad structure (`weight 12`, five entries `±3`), builds the witness `ξ = sign(x)/√2` and computes
  `51 π(ξ)² = 60`, which is forbidden (Proposition `prop:sixty`, kernel-checked).
-/

namespace Srg154

open RealInnerProductSpace

/-! ## The projection formula -/

section Proj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `π(v) = v - ((26a - b)/51) r - ((2b - a)/51) f`. -/
noncomputable def projI (r f v : E) : E :=
  v - ((26 * ⟪v, r⟫ - ⟪v, f⟫) / 51) • r - ((2 * ⟪v, f⟫ - ⟪v, r⟫) / 51) • f

theorem projI_spec (r f v : E) (hr : ⟪r, r⟫ = 2) (hrf : ⟪r, f⟫ = 1) (hf : ⟪f, f⟫ = 26) :
    ⟪projI r f v, r⟫ = 0 ∧ ⟪projI r f v, f⟫ = 0 ∧
    51 * ⟪projI r f v, projI r f v⟫ =
      51 * ⟪v, v⟫ - (26 * ⟪v, r⟫ ^ 2 - 2 * ⟪v, r⟫ * ⟪v, f⟫ + 2 * ⟪v, f⟫ ^ 2) := by
  have hfr : ⟪f, r⟫ = 1 := by rw [real_inner_comm]; exact hrf
  have hrv : ⟪r, v⟫ = ⟪v, r⟫ := real_inner_comm _ _
  have hfv : ⟪f, v⟫ = ⟪v, f⟫ := real_inner_comm _ _
  unfold projI
  refine ⟨?_, ?_, ?_⟩
  · simp only [inner_sub_left, real_inner_smul_left, hr, hfr]; field_simp; ring
  · simp only [inner_sub_left, real_inner_smul_left, hrf, hf]; field_simp; ring
  · simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hr, hrf,
      hfr, hf, hrv, hfv]
    field_simp; ring

end Proj

/-! ## Lemma `lem:A1` (arithmetic part) -/

/-- The norms `𝓕_I`. -/
def FI : Finset ℤ := {4, 16, 30, 36, 52, 60, 64, 70, 72, 76, 94}

theorem FI_forbidden {m : ℤ} (hm : m ∈ FI) (ℓ : ℤ) : ¬ HasWitness m ℓ :=
  forb_a m (by simp only [FI, Finset.mem_insert, Finset.mem_singleton] at hm ⊢; omega) ℓ

def a1Check : Bool :=
  (List.range 3).all fun a => (List.range 15).all fun b =>
    let α : ℤ := (a : ℤ) - 1
    let β : ℤ := (b : ℤ) - 7
    let m : ℤ := 102 - (26 * α ^ 2 - 2 * α * β + 2 * β ^ 2)
    !(decide (0 < m)) || decide (m ∈ FI) ||
      (decide (α = 0) && decide (β = 0 ∨ β = 1 ∨ β = -1 ∨ β = 3 ∨ β = -3))

theorem a1Check_ok : a1Check = true := by decide +kernel

/-- **Lemma `lem:A1`, arithmetic.** If `m = 102 - (26α₀² - 2α₀β₀ + 2β₀²) > 0` is the norm of the
projection of a root and some pairing `ℓ` is admissible for it, then `α₀ = 0` and `β₀ ∈ {0,±1,±3}`.
So `r` spans an `A₁` component (the input needed to apply E2). -/
theorem lemmaA1_arith (α β : ℤ) (hm : 0 < 102 - (26 * α ^ 2 - 2 * α * β + 2 * β ^ 2))
    (hadm : ∃ ℓ, HasWitness (102 - (26 * α ^ 2 - 2 * α * β + 2 * β ^ 2)) ℓ) :
    α = 0 ∧ (β = 0 ∨ β = 1 ∨ β = -1 ∨ β = 3 ∨ β = -3) := by
  have hα : -1 ≤ α ∧ α ≤ 1 := by constructor <;> nlinarith [sq_nonneg (2 * β - α)]
  have hβ : -7 ≤ β ∧ β ≤ 7 := by constructor <;> nlinarith [sq_nonneg (2 * β - α), sq_nonneg (5 * α - β)]
  have hc := a1Check_ok
  simp only [a1Check, List.all_eq_true, List.mem_range] at hc
  have := hc (α + 1).toNat (by omega) (β + 7).toNat (by omega)
  rw [show (((α + 1).toNat : ℕ) : ℤ) - 1 = α by omega,
    show (((β + 7).toNat : ℕ) : ℤ) - 7 = β by omega] at this
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt,
    decide_eq_true_eq, Bool.and_eq_true] at this
  rcases this with (h | h) | h
  · omega
  · obtain ⟨ℓ, hw⟩ := hadm; exact absurd hw (FI_forbidden h ℓ)
  · exact h

/-! ## The dodecad -/

/-- If every entry is `0, ±1, ±3`, `∑ x² = 52` and the support has size `8, 12, 16` or `24`, then the
support is a dodecad with five entries `±3`; in particular `∑ |x| = 22`. -/
theorem dodecad (x : Fin 24 → ℤ) (hv : ∀ i, x i = 0 ∨ x i = 1 ∨ x i = -1 ∨ x i = 3 ∨ x i = -3)
    (hn : ∑ i, x i ^ 2 = 52)
    (hw : (Finset.univ.filter (fun i => x i ≠ 0)).card ∈ ({8, 12, 16, 24} : Finset ℕ)) :
    (Finset.univ.filter (fun i => x i ≠ 0)).card = 12 ∧
    (Finset.univ.filter (fun i => |x i| = 3)).card = 5 ∧ ∑ i, |x i| = 22 := by
  set n1 := (Finset.univ.filter (fun i => |x i| = 1)).card
  set n3 := (Finset.univ.filter (fun i => |x i| = 3)).card
  have ind : ∀ F : ℤ → ℤ, F 0 = 0 → F 1 = F (-1) → F 3 = F (-3) →
      ∑ i, F (x i) = F 1 * n1 + F 3 * n3 := by
    intro F h0 h1 h3
    have : ∀ i, F (x i) = F 1 * (if |x i| = 1 then 1 else 0) + F 3 * (if |x i| = 3 then 1 else 0) := by
      intro i
      rcases hv i with h | h | h | h | h <;> rw [h] <;> simp [h0, h1, h3]
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp [n1, n3]
  have hsupp : (Finset.univ.filter (fun i => x i ≠ 0)).card = n1 + n3 := by
    have := ind (fun z => if z ≠ 0 then 1 else 0) (by simp) (by simp) (by simp)
    simp only [Finset.sum_boole] at this
    norm_num at this
    exact_mod_cast this
  have hsq := ind (fun z => z ^ 2) (by simp) (by simp) (by simp)
  have habs := ind (fun z => |z|) (by simp) (by simp) (by simp)
  rw [hn] at hsq
  norm_num at hsq habs
  rw [hsupp] at hw ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  have : n1 + n3 = 12 ∧ n3 = 5 := by omega
  refine ⟨this.1, this.2, ?_⟩
  rw [habs]; omega

/-! ## Theorem `thm:genusI` in coordinates -/

/-- Twice the inner product in the model `v/√2`. -/
def dot (v v' : Fin 24 → ℤ) : ℤ := ∑ i, v i * v' i

/-- `51 π(v)²` for `v/√2`, via `(eq:projI)`, with `a = ⟨v,r⟩ = v₀` and `b = ⟨v,f⟩ = (v·x)/2`. -/
noncomputable def mI (x v : Fin 24 → ℤ) : ℚ :=
  51 * ((dot v v : ℚ) / 2) -
    (26 * (v 0 : ℚ) ^ 2 - 2 * (v 0 : ℚ) * ((dot v x : ℚ) / 2) + 2 * ((dot v x : ℚ) / 2) ^ 2)

def mod2 (v : Fin 24 → ℤ) : Fin 24 → ZMod 2 := fun i => (v i : ZMod 2)

def wt (c : Fin 24 → ZMod 2) : ℕ := (Finset.univ.filter (fun i => c i ≠ 0)).card

/-- **Theorem `thm:genusI`** (in the coordinates provided by E2). -/
theorem genusI_impossible (𝒢 : Set (Fin 24 → ZMod 2)) (h0 : (0 : Fin 24 → ZMod 2) ∈ 𝒢)
    (hwt : ∀ c ∈ 𝒢, c ≠ 0 → wt c ∈ ({8, 12, 16, 24} : Finset ℕ))
    (x : Fin 24 → ℤ) (hxG : mod2 x ∈ 𝒢) (hx0 : x 0 = 1) (hxn : dot x x = 52)
    (adm : ∀ v : Fin 24 → ℤ, mod2 v ∈ 𝒢 → ∀ m : ℤ, (m : ℚ) = mI x v → m ≠ 0 → ∃ ℓ, HasWitness m ℓ) :
    False := by
  -- Step 1: the roots √2 eᵢ (i ≠ 0) force xᵢ ∈ {0, ±1, ±3}.
  have hvals : ∀ i, x i = 0 ∨ x i = 1 ∨ x i = -1 ∨ x i = 3 ∨ x i = -3 := by
    intro i
    by_cases hi : i = 0
    · subst hi; right; left; exact hx0
    set e : Fin 24 → ℤ := fun j => if j = i then 2 else 0 with he
    have he0 : e 0 = 0 := by simp [he, Ne.symm hi]
    have hee : dot e e = 4 := by simp [dot, he]
    have hex : dot e x = 2 * x i := by simp [dot, he]
    have hmod : mod2 e ∈ 𝒢 := by
      have : mod2 e = 0 := by
        funext j; simp only [mod2, he]; split_ifs <;> simp; decide
      rw [this]; exact h0
    have hm : mI x e = ((102 - 2 * x i ^ 2 : ℤ) : ℚ) := by
      simp only [mI, hee, hex, he0]; push_cast; ring
    -- xᵢ² ≤ 51
    have hsq : x i ^ 2 ≤ 51 := by
      have : x 0 ^ 2 + x i ^ 2 ≤ ∑ j, x j ^ 2 := by
        rw [← Finset.sum_pair (f := fun j => x j ^ 2) (Ne.symm hi)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => sq_nonneg _)
      have hd : ∑ j, x j ^ 2 = 52 := by rw [← hxn]; simp [dot, sq]
      rw [hd, hx0] at this; linarith
    have hb : -7 ≤ x i ∧ x i ≤ 7 := by constructor <;> nlinarith
    have hne : (102 - 2 * x i ^ 2 : ℤ) ≠ 0 := by
      have key : ∀ a : ℤ, -7 ≤ a → a ≤ 7 → 102 - 2 * a ^ 2 ≠ 0 := by
        intro a h1 h2; interval_cases a <;> omega
      exact key _ hb.1 hb.2
    obtain ⟨ℓ, hw⟩ := adm e hmod _ hm.symm hne
    have := lemmaA1_arith 0 (x i) (by nlinarith) ⟨ℓ, by
      have : (102 : ℤ) - (26 * 0 ^ 2 - 2 * 0 * x i + 2 * x i ^ 2) = 102 - 2 * x i ^ 2 := by ring
      rw [this]; exact hw⟩
    rcases this.2 with h | h | h | h | h <;> simp [h]
  -- Step 2: the support of x is a codeword, so a dodecad with five entries ±3.
  have hsupp : wt (mod2 x) = (Finset.univ.filter (fun i => x i ≠ 0)).card := by
    unfold wt mod2
    congr 1; ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hvals i with h | h | h | h | h <;> rw [h] <;> decide
  have hx0' : mod2 x ≠ 0 := by
    intro h; have := congrFun h 0; simp [mod2, hx0] at this
  have hsq : ∑ i, x i ^ 2 = 52 := by rw [← hxn]; simp [dot, sq]
  obtain ⟨-, -, habs⟩ := dodecad x hvals hsq (hsupp ▸ hwt _ hxG hx0')
  -- Step 3: the witness ξ = sign(x)/√2.
  set s : Fin 24 → ℤ := fun i => Int.sign (x i) with hs
  have hsx : ∀ i, s i * x i = |x i| := fun i => by simp [hs]
  have hss : ∀ i, s i * s i = (if x i ≠ 0 then 1 else 0) := fun i => by
    rcases hvals i with h | h | h | h | h <;> simp [hs, h] <;> decide
  have hmods : mod2 s = mod2 x := by
    funext i; simp only [mod2, hs]
    rcases hvals i with h | h | h | h | h <;> rw [h] <;> decide
  have hs0 : s 0 = 1 := by simp [hs, hx0]
  have hdss : dot s s = 12 := by
    have h12 := (dodecad x hvals hsq (hsupp ▸ hwt _ hxG hx0')).1
    simp only [dot, hss, Finset.sum_boole]
    exact_mod_cast h12
  have hdsx : dot s x = 22 := by simp only [dot, hsx]; exact habs
  have hm60 : mI x s = ((60 : ℤ) : ℚ) := by
    simp only [mI, hdss, hdsx, hs0]; norm_num
  obtain ⟨ℓ, hw⟩ := adm s (hmods ▸ hxG) 60 hm60.symm (by norm_num)
  exact sixty_forbidden ℓ hw

end Srg154
