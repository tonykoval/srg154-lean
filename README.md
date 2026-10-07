# srg154-lean — Lean 4 / Mathlib formalisation of the core of "There is no srg(154,72,26,40)"

Paper: `orbit-gen/docs/paper/srg154.tex` (A. Kovaľ, October 2026). This project machine-checks the
**arithmetic and combinatorial core** of the nonexistence proof. The lattice-theoretic and modular-forms inputs are
**hypotheses** of the main theorems, not axioms (there is no `axiom` declaration anywhere).

Status (2026-10-07): **all files compile, 0 `sorry`, 0 `admit`, 0 `native_decide`, 0 custom axioms.**

## Toolchain and build

| item | value |
|---|---|
| Lean | `leanprover/lean4:v4.35.0-rc4` (see `lean-toolchain`) |
| Mathlib | `021ce68bf125a049beee22b3fc7664d78728e21d` (master on 2026-10-07; pinned in `lakefile.toml` / `lake-manifest.json`) |
| options | `autoImplicit = false` |

```bash
lake exe cache get     # downloads the Mathlib build cache (~9000 files); do NOT build Mathlib from source
lake build             # builds the 9 project files + root module
lake env lean Axioms.lean   # prints the axioms of the 35 main theorems
```

Build time of the project after the cache download: **about 50–80 s** on 4 cores (48 s incremental-clean, 78 s in a fresh directory) (x86_64 Linux, docker
`srg-queue`). The slowest file is `Certificates.lean` at about 10 s, which includes the kernel evaluation of all 521
certificates. Built and audited at `/root/lean154` inside the container; this folder is the canonical copy.

## Axioms (`lake env lean Axioms.lean`, full output in `tools/axioms_output.txt`)

Every audited theorem depends only on `[propext, Classical.choice, Quot.sound]` (31 theorems) or `[propext]` (4 pure
`decide +kernel` facts). **No `sorryAx`, no `Lean.ofReduceBool`/`trustCompiler`.** All finite computations use
`decide +kernel`, so they are checked by the Lean kernel; the compiler is not trusted anywhere.

## Files and what is formally proved

| file | paper | main results |
|---|---|---|
| `Srg154/Parameters.lean` | §1, §3 (item 1) | `srg_spectrum`: **from `G.IsSRGWith 154 72 26 40` alone** (Mathlib's `SimpleGraph.IsSRGWith`), Mathlib's Hermitian eigenvalues of the real adjacency matrix take the value 72 once, 2 exactly 132 times, −16 exactly 21 times. Proved with `IsSRGWith.matrix_eq`, the spectral theorem and traces. Also `srg_sq` (A² = 32I − 14A + 40J), `srg_reg`, `mult_arith`, `eig_quadratic`, `gram_eigen`. |
| `Srg154/DualVector.lean` | Lemma `lem:V`(ii),(iii) | `gramM_sq`: 𝒢² = 18𝒢 + 340J for 𝒢 = −A+2I+2J. `dual_vector_real`: for every w, with z = 𝒢w: Σz = 238Σw, Σz² = 18·wᵀ𝒢w + 340(Σw)², Az = −16z + 2Σz − 340Σw. `dual_vector_witness`: if z is integral, 51x² = m ∈ ℤ and Σz = 7ℓ with ℓ ∈ ℤ, then **(m, ℓ) has a witness with Γᵢ = Γ(i)** (equation `(eq:adm)`). |
| `Srg154/Admissible.lean` | Def. `def:adm`, Lemma `lem:tools` | `Witness`, `HasWitness`, `Admissible` (the paper's definition verbatim); soundness of tests L0–L3 (`Witness.L0`, `Shifted.abs_S_le`, `even_Q_sub_S`, `nbr_abs`, `nbr_lower`, `nbr_upper`, sign-propagation lemmas); `HasWitness.neg` (adm(m) = −adm(m)); `ell_bound` (3ℓ² ≤ 44m, Cauchy–Schwarz on z). |
| `Srg154/Certificates.lean` | Thm `thm:forb`, Lemma `lem:special`, Prop `prop:sixty` (item 2) | `not_hasWitness_of_check`: **soundness of the Boolean certificate checker**. `forb_a`, `forb_b`, `forb_c`, `forb_d`: Theorem `thm:forb`(a)–(d) **as stated in the paper, for all integer parameters** (finite ranges derived inside Lean). `special_83_4`, `special_128_26`, `sixty_forbidden`. `pairs521` (the list, `length = 521`), `pairs521_forbidden`. Positive control `control_33_22 : Admissible 33 22`, so the predicate is not vacuous. |
| `Srg154/PaperTables.lean` | Appendix `app:cert` | Tables `tab:lzero` and `tab:cert` **as printed** (parsed from the .tex by `tools/gen_tables.py`). `rowCheck_sound` + `paperCert_ok`: every printed row (γ, Q, S, t, 𝒱, P^max±, named test) is verified and sound. `paperCert_matches_pairs521`: the 107 rows are exactly the pairs passing L0, in order. `paperCert_split`: 83/11/11/2. `L0_count`: 414. `paperL0_ok`. `pairs521_forbidden_by_paper_tables`: a **second, table-only proof** of all 521 pairs. |
| `Srg154/AdmTable.lean` | Computation `comp:adm` (bonus) | `adm_le_110`: for 1 ≤ m ≤ 110 every pair with a witness is in the paper's list of 17 admissible pairs (upper bound only). `adm84`, `adm100` (the inputs of Remark `rem:genusI2`). |
| `Srg154/GenusII.lean` | §§`sec:dict`–`sec:rootless` (items 3, 4) | `gram_bound` (Gram determinant, proved). `Config` = glue data of Prop `prop:dict` + `(eq:adm)` as hypotheses. **Pins derived in Lean from the certificates**: `no_units` (a), `root_pin` (b), `char_pin` (c), `norm3_pin` (d). `theoremA`: frame identity (hypothesis) ⇒ no roots. `theoremB`: 7-design moments (hypothesis) ⇒ roots. `genusII_impossible`. |
| `Srg154/GenusI.lean` | §`sec:genusI` (item 5) | `projI_spec`: the projection formula `(eq:projI)`. `lemmaA1_arith`: arithmetic of Lemma `lem:A1`. `dodecad`: weight 12, five entries ±3, Σ\|x\| = 22. `genusI_impossible`: in the A₁²⁴ coordinates given by E2, the witness ξ = sign(x)/√2 has 51π(ξ)² = 60, which is forbidden. |
| `Srg154/Main.lean` | §`sec:proof` | `no_host_conditional`: neither host package (`GenusIHost`, `GenusIIHost`) can exist. `design_constants`: ν = 600, 216, 120 and the value −2880. |
| `Srg154.lean`, `Axioms.lean` | | root import; axiom audit |

## What is assumed (hypotheses, never axioms)

The step "an srg(154,72,26,40) exists ⇒ one of the two host packages of `Main.lean` exists" is **not**
formalised. In detail:

1. **Vertex lattice and dual vectors** (§3): the existence of the vectors vᵢ ∈ ℝ²² with Gram −A+2I+2J (the PSD/rank
   statement is not proved; the spectrum is), the lattice L, y = s/119, Lemma `lem:y`, the maximal even
   overlattice and Lemma `lem:max`. These lemmas provide, for x ∈ N^#, the integrality of z, of 51x² and of
   ℓ = Σz/7. Given that integrality, `dual_vector_witness` **is** the formal bridge from the graph to `(eq:adm)`.
2. **Two genera** (Prop `prop:forms`: Milgram's formula, Chevalley–Warning, anisotropy). Not formalised.
3. **Gluing** (Lemmas `lem:glue`, `lem:test`, Prop `prop:dict`, `(eq:projII)`). Not formalised. They enter as the
   fields of `Config` (U integral, w, u ∈ U with w² = 51, u² = 7, ⟨u,w⟩ = 15) and its two `(eq:adm)` hypotheses
   `adm_proj` and `adm_char`, and as the field `adm` of `GenusIHost`. For genus I the projection formula itself
   **is** proved (`projI_spec`).
4. **E2 (Niemeier / Golay)**: that X ≅ A₁²⁴ in coordinates with r = √2e₀, f = x/√2, and that the Golay code has
   weights 0, 8, 12, 16, 24. These are hypotheses of `genusI_impossible`. The arithmetic step of Lemma `lem:A1`
   that justifies using E2 is proved (`lemmaA1_arith`).
5. **E3, the frame identity** (Theorem `thm:frameid`, K105 / Nebe–Venkov). It is a hypothesis of `theoremA`,
   required only for unit-free U. Unit-freeness is **proved** (`no_units`).
6. **E4, the 7-design property** (Lemma `lem:design`: moments 600, 216, 120 on the 4600 norm-3 vectors). It is a
   hypothesis of `theoremB`, required only for U without units and roots. The values ν_k from |Ψ| = 4600 are
   checked as arithmetic in `design_constants`.
7. The PSD of −A+2I+2J (Lemma `lem:V`(i), |zᵢ| ≤ 2√a) is not needed: every non-admissibility result is proved for
   `HasWitness`, which omits the side conditions of `Admissible`. These are **stronger** statements than the
   paper's, and correspondingly the `(eq:adm)` hypotheses are **weaker**.

No classification-dependent fact (the 49 unit-free lattices, O₂₃) is used, as in the paper.

## Deviations from the paper (all in the safe direction)

* `HasWitness` vs `Admissible`: see item 7 above.
* The checker of `Certificates.lean` tries every γ ∈ [−3, 3] and uses a single value filter that combines
  (L2) with the one-vertex bounds of (L3). This is exactly the argument of Lemma `lem:special`. Its soundness is
  proved generically. `PaperTables.lean` independently verifies the printed table verbatim with the paper's own
  test per row, so both routes are formal.
* Pins (c): `char_pin` proves "3αβ − α² ≥ 2, and = 2 ⇒ α² = 1" for every characteristic η of norm 7, including
  η = ±u (value 90). This is all that Theorem A uses. It removes the ε-bookkeeping of the paper's proof.

## Cross-checks done while building

* `pairs521` (Lean) = `scripts/srg154_paper/regen_certificates.py: needed()` (same list, same order) =
  `out/srg154_rep2/hand_tools.txt` (same multiset); see `tools/compare_pairs.py`. The Python verdict split
  414/83/11/11/2 matches `L0_count` and `paperCert_split`.
* Negative test: changing one printed number of `tab:cert` (t = 12 → 13 in the row (94, 25)) makes
  `paperCert_ok` fail (`tools/neg_test.sh`).
* `tools/ctrl_eval.lean`: the checker kills every pair with m ≤ 110 except exactly the 17 pairs that the
  paper's exhaustive deciders found admissible, and it kills none of those 17.

## Honest assessment: how much of the proof is machine-checked

* **Fully formal (no hypotheses beyond Mathlib):** the SRG spectrum (132/21); the dual-vector identities from the
  graph; the admissibility definition and the soundness of tests L0–L3; **all 521 forbidden pairs** (two
  independent formal routes, including the printed Appendix-A tables line by line); Lemma `lem:special`; the key
  norm 20/17; the Gram bounds; pins (a)–(d) as consequences of `(eq:adm)`; the inequality argument of Theorem A;
  the design-polynomial argument of Theorem B (sum −2880); the projection formula, the A₁-component arithmetic and
  the dodecad witness of genus I.
* **Hypotheses:** everything that turns the graph into lattices: the vertex lattice, the maximal overlattice,
  Milgram and the two genera, gluing and the dictionary, and E2/E3/E4. These are the standard lattice and
  modular-forms inputs. The paper's own "computer-assembled" part (the certificate table, residual point 2 of
  §`sec:residual`) is now **fully kernel-checked**.
* Roughly: of the 7 steps in the paper's Table `tab:status`, step 3 is complete and formal. Steps 4–7 are formal
  in their combinatorial and inequality core, conditional on the stated inputs. Steps 1–2 are formal only in
  their graph-side identities (spectrum, `dual_vector_witness`); the lattice-theoretic parts are assumed.

## Layout

```
lakefile.toml  lean-toolchain  lake-manifest.json  Srg154.lean  Axioms.lean  README.md
Srg154/        the 9 source files
tools/         build.sh, check.sh (docker helpers), gen_tables.py, compare_pairs.py, pairs521_lean.txt,
               dump.lean, ctrl_eval.lean, neg_test.sh, axioms_output.txt
```
