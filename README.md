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
lake build             # builds the 15 project files + root module
lake env lean Axioms.lean   # prints the axioms of the 76 audited theorems
```

Build time of the project after the cache download: **about 90–110 s** on 4 cores (92–108 s in a fresh directory) (x86_64 Linux, docker
`srg-queue`). The slowest file is `Certificates.lean` at about 10 s, which includes the kernel evaluation of all 521
certificates. Built and audited at `/root/lean154` inside the container; this folder is the canonical copy.

## Axioms (`lake env lean Axioms.lean`, full output in `tools/axioms_output.txt`)

Every audited theorem depends only on `[propext, Classical.choice, Quot.sound]` (69 theorems) or `[propext]` (4 pure
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
| `Srg154/VertexLattice.lean` | §`sec:vertex`: Lemmas `lem:M`, `lem:y`, `lem:max`, `lem:V`; last sentence of Prop `prop:forms` | **From `G.IsSRGWith 154 72 26 40` alone.** `exists_rep`: vertex vectors with Gram −A+2I+2J exist (PSD via 𝒢 = 𝒢'ᵀ𝒢'/18 + (17/11)J, 𝒢'² = 18𝒢'). For ANY such family `v` in ANY real inner product space (`IsRep`), with `W` = span: `lemM` (M = 18I + (5/833)ssᵀ on W), `s_sq` (s² = 36652), `lemY` (119 ∣ ⟨s,x⟩ for every integral N ⊇ L in W), `y_sq` (y² = 44/17), `inner_v_y`, `lemM_y` (M = 18I + 85yyᵀ). `MaxEven` = maximal even subgroup of W containing L (no discreteness assumed); `exists_maxEven` (Zorn). Lemma `lem:max`: `seventeen_y_mem`, `y_not_mem` (a), `lemMax_b`, `mul306_mem` (b), `mem_of_dual_even` (c, anisotropy). `parity` (the parity fact), `d2_int`, `d3_elem`, `mul102_mem` (exponent of D(N) divides 102), `norm51` (51x² ∈ ℤ on N^#, **without Milgram**). `eq_adm`, `eq_adm_hasWitness`: **equation `(eq:adm)` from the graph** for every x ∈ N^#, with m ≡ 2ℓ² (mod 17). Capstone `graph_to_eq_adm`. |
| `Srg154/Rank.lean` | §`sec:vertex` ("rank 22") | `finrank_W`: for every `IsRep` family, dim W = 22 (idempotent E = 𝒢'/18 + J/154 of trace 22 with ker E = ker 𝒢). This is the signature 22 in Milgram's formula. |
| `Srg154/DiscForm.lean` | proof of Prop `prop:forms` up to Milgram | Phrased for representatives x ∈ N^# (no quotient group built): `primary_decomp` (D = D₂⊕D₃⊕D₁₇), `coprime_orth`, `d17_cyclic` (D₁₇ = ⟨ȳ⟩), `y_sq_mod` (q(ȳ) ≡ 10/17), `d2_odd` (q ≡ 1 on D₂∖0), `d2_rank` (dim D₂ ≤ 2), `d3_norm` (q ∈ (2/3)ℤ on D₃, ≢ 0 off 0), `d3_rank` (dim D₃ ≤ 2; `ternary_isotropic_F3`: every ternary form over 𝔽₃ is isotropic, by `decide`). |
| `Srg154/Gauss17.lean` | Prop `prop:forms`, "Gauss sum of ⟨10/17⟩ is −√17" | `gauss17`: ∑_{x mod 17} e^{πi·10x²/17} = −√17 (**proved**: S² = 17 by character orthogonality with Mathlib's `ZMod.stdAddChar`, sign by cosine bounds Re S ≤ 3 < √17). So Br⟨10/17⟩ = 4 is not a hypothesis. |
| `Srg154/FiniteForms.lean` | Prop `prop:forms`, Milgram step | Finite model `Cand` = (dim D₂, dim D₃, the 𝔽₃-form of D₃), `Valid` = the vector-level facts of DiscForm; `gaussTotal` = the Gauss sum of D₂⊕D₃⊕⟨10/17⟩ in ℂ; `Milgram c` = Milgram's formula with signature 22 (**hypothesis**: not in Mathlib). `classification_finite` (kernel exhaustion over 243 candidates), `milgram_int`, **`forms_classification`**: Valid + Milgram ⇒ form (I) ⟨2/3⟩⊕⟨10/17⟩ or form (II) V₂⊕⟨4/3⟩⊕⟨10/17⟩; `det_cases`: \|D\| ∈ {51, 204}; `formI_milgram`, `formII_milgram`: both satisfy Milgram (so exactly two). |
| `Srg154/GenusIReduce.lean` | Lemma `lem:A1`, start of Thm `thm:genusI` | `lemA1_geom`: Lemma `lem:A1` in any real inner product space (α = 0, β ∈ {0,±1,±3}). `A1_24_roots`: the roots of the A₁²⁴ model are ±√2eᵢ, from the code weights alone. `genusI_impossible_general`: Theorem `thm:genusI` for an ARBITRARY root r of the model (the renumbering/sign change "r = √2e₁" is done in Lean, the code replaced by its image). |
| `Srg154/Exports.lean` | `(eq:adm)` with `Admissible`; Lemma `lem:A1` hypothesis | Contributed by the independent review C30 (Codex). `full_admissibility`: from the graph, every **nonzero** x ∈ N^# gives (m, ℓ) with the FULL predicate `Admissible` (side conditions included, not only `HasWitness`). `dual_has_nontrivial_class`: y ∈ N^# ∖ N. `root_projection_nonzero`: π(ρ) ≠ 0 for every norm-2 ρ ≠ ±r, the explicit hypothesis of `lemA1_geom`, derived from the Gram data. |
| `Srg154.lean`, `Axioms.lean` | | root import; axiom audit |

## What is assumed (hypotheses, never axioms)

The step "an srg(154,72,26,40) exists ⇒ one of the two host packages of `Main.lean` exists" is **not**
formalised as a single theorem. In detail (updated 2026-10-07, second pass):

1. **Vertex lattice and dual vectors** (§3): **now formal** (`VertexLattice.lean`, `Rank.lean`). From
   `G.IsSRGWith 154 72 26 40` alone: vertex vectors exist, span a space of dimension 22, a maximal even
   overlattice N exists, and for EVERY maximal even overlattice and every x ∈ N^#: z ∈ ℤ¹⁵⁴, ℓ = 17⟨y,x⟩ ∈ ℤ,
   51x² ∈ ℤ, and `(eq:adm)` holds (`eq_adm`, `graph_to_eq_adm`). "Lattice" means here an even additive subgroup
   of the span W; discreteness is never used, so no lattice framework is needed.
2. **Two genera** (Prop `prop:forms`): **formal except two inputs.** Proved: the primary decomposition, D₁₇ = ⟨ȳ⟩
   with q ≡ 10/17, D₂ elementary with q ≡ 1 off 0 and rank ≤ 2, D₃ elementary anisotropic of rank ≤ 2
   (Chevalley–Warning for ternary forms over 𝔽₃ by exhaustion), 51x² ∈ ℤ (which needs no Milgram), the Gauss
   sum −√17 of ⟨10/17⟩, rank 22, and the finite classification: a candidate satisfying Milgram's formula is
   (I) or (II), |D| ∈ {51, 204}, and both satisfy it. **Not formal:** (a) Milgram's formula itself (the
   hypothesis `Milgram c`; not in Mathlib); (b) the packaging of D(N) = N^#/N as a finite quadratic module and
   its identification with a candidate `c` (choice of bases of D₂, D₃; nondegeneracy). The vector-level facts
   that make the candidate `Valid` are proved in `DiscForm.lean`.
3. **Gluing** (Lemmas `lem:glue`, `lem:test`, Prop `prop:dict`, `(eq:projII)`). Not formalised. They enter as the
   fields of `Config` (U integral, w, u ∈ U with w² = 51, u² = 7, ⟨u,w⟩ = 15) and its two `(eq:adm)` hypotheses
   `adm_proj` and `adm_char`, and as the field `adm` of `GenusIHost`. For genus I the projection formula itself
   **is** proved (`projI_spec`). (Note: `(eq:adm)` for x ∈ N^# is now a theorem; what is missing is that the
   projections π(v) of the glued lattice lie in N^#.)
4. **E2 (Niemeier / Golay)**: that X ≅ A₁²⁴ (as the doubled-coordinate model with a code 𝒢) and that the Golay
   code has weights 0, 8, 12, 16, 24. These remain hypotheses. **Now formal:** Lemma `lem:A1` in geometric form
   (`lemA1_geom`), the roots of the model are ±√2eᵢ (`A1_24_roots`, from the weights alone), and the
   normalisation r = √2e₀ (`genusI_impossible_general` takes an arbitrary root r of the model).
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
  the dodecad witness of genus I. **Second pass:** the vertex vectors (PSD, rank 22), y = s/119, Lemmas
  `lem:M`/`lem:y`/`lem:max`/`lem:V`, existence of a maximal even overlattice, `(eq:adm)` for every x ∈ N^# from
  the graph; the structure of D(N) up to Milgram; the Gauss sum of ⟨10/17⟩; the Milgram classification as a
  finite computation; Lemma `lem:A1` geometrically, the roots of A₁²⁴ and the coordinate normalisation.
* **Hypotheses:** Milgram's formula and the identification of D(N) with a finite candidate form; gluing and the
  dictionary; E2 (Niemeier classification, Golay weights), E3, E4. These are the standard lattice and
  modular-forms inputs. The paper's own "computer-assembled" part (the certificate table, residual point 2 of
  §`sec:residual`) is **fully kernel-checked**.
* Roughly: of the 7 steps in the paper's Table `tab:status`, steps 1 and 3 are complete and formal, step 2 is
  formal up to Milgram's formula and the finite-module packaging of D(N), steps 4–7 are formal in their
  combinatorial and inequality core, conditional on the stated inputs.

## Layout

```
lakefile.toml  lean-toolchain  lake-manifest.json  Srg154.lean  Axioms.lean  README.md
Srg154/        the 15 source files
tools/         build.sh, check.sh (docker helpers), gen_tables.py, compare_pairs.py, pairs521_lean.txt,
               dump.lean, ctrl_eval.lean, neg_test.sh, axioms_output.txt
```

## Independent review (2026-10-07)
An independent review (Codex, report `docs/codex_review_srg154_lean_2026_10_07.md` in the orbit-gen repository, commit
c75d9e4) rebuilt this project from a fresh copy (`lake exe cache get` + `lake build`: PASS), reproduced all 35 axiom
audits, and found no blocking defect. Verdict: **a sound conditional formalization of the core, not a full formal
nonexistence proof.** It showed that the hypothesis bundles of `theoremA` and `theoremB` are satisfiable (explicit
rooted and rootless configurations), so the conclusions are not vacuous. Clarifications from the review:
- `dual_vector_witness` gives a witness for the admissibility conditions *conditional on the representation and
  integrality data*; it does not formalize the whole of (eq:adm) from a graph.
- `FrameIdentity` does not encode the uniqueness of antipodal pairs, and only the pins used by Theorems A/B are exported.
  These are safe weakenings (they only strengthen the formal conclusions).
- Not formalized (eight groups): PSD representation and vertex lattice; y and the maximal even overlattice;
  discriminant forms / the two genera; gluing dictionaries; the geometric genus-I reduction to A1^24; the frame identity
  (E3); the 7-design property (E4); the final graph-to-host assembly.

### Status of the eight groups after the second pass (2026-10-07)

| # | group (review C29) | status now | where |
|---|---|---|---|
| 1 | PSD representation and vertex lattice | **formal** (vectors exist, Gram −A+2I+2J, dim W = 22) | `VertexLattice.lean` (`exists_rep`), `Rank.lean` (`finrank_W`) |
| 2 | y and the maximal even overlattice | **formal** (Lemmas y, max (a)–(c), V; existence by Zorn; `(eq:adm)` for every x ∈ N^#) | `VertexLattice.lean` (`eq_adm`, `graph_to_eq_adm`) |
| 3 | discriminant forms / the two candidate forms | **formal except** Milgram's formula (hypothesis `Milgram`) and the identification of D(N) with a finite candidate form | `DiscForm.lean`, `Gauss17.lean`, `FiniteForms.lean` |
| 4 | gluing dictionaries | not formalised (fields of `Config`, `GenusIHost.adm`) | — |
| 5 | geometric genus-I reduction to A₁²⁴ | **partly formal**: Lemma A1 geometric, roots of A₁²⁴, coordinate normalisation; E2 itself (Niemeier, Golay weights) remains a hypothesis | `GenusIReduce.lean` |
| 6 | frame identity (E3) | not formalised (hypothesis of `theoremA`) | — |
| 7 | 7-design property (E4) | not formalised (hypothesis of `theoremB`) | — |
| 8 | final graph-to-host assembly | not formalised; the graph side (`(eq:adm)` on N^#) is now a theorem, the missing links are groups 3(a,b), 4, 5 (E2), 6, 7 | — |

Remaining unformalised steps, in one list: Milgram's formula; D(N) as a finite quadratic module ≅ candidate, and the
identification of the two candidate discriminant forms with genera of lattices (`det_cases` counts candidate
cardinalities, it is not a determinant theorem about N);
gluing (Lemmas `lem:glue`, `lem:test`, Prop `prop:dict`); E2; E3; E4; the assembly theorem.
