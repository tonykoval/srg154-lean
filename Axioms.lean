import Srg154
open Srg154
-- Item 1
#print axioms srg_spectrum
#print axioms mult_arith
-- dual-vector lemma (graph -> (eq:adm))
#print axioms dual_vector_witness
-- Item 2
#print axioms not_hasWitness_of_check
#print axioms forb_a
#print axioms forb_b
#print axioms forb_c
#print axioms forb_d
#print axioms special_83_4
#print axioms special_128_26
#print axioms sixty_forbidden
#print axioms pairs521_forbidden
#print axioms pairs521_length
#print axioms control_33_22
-- Items 3 and 4
#print axioms Config.no_units
#print axioms Config.root_pin
#print axioms Config.char_pin
#print axioms Config.norm3_pin
#print axioms theoremA
#print axioms theoremB
#print axioms genusII_impossible
-- Item 5
#print axioms projI_spec
#print axioms lemmaA1_arith
#print axioms dodecad
#print axioms genusI_impossible
-- capstone
#print axioms no_host_conditional
#print axioms design_constants
-- printed tables
#print axioms rowCheck_sound
#print axioms paperCert_ok
#print axioms paperCert_matches_pairs521
#print axioms paperL0_ok
#print axioms pairs521_forbidden_by_paper_tables
-- bonus table m <= 110
#print axioms adm_le_110
#print axioms adm84
#print axioms adm100
-- Group 1-2: vertex vectors, y, maximal even overlattice (VertexLattice.lean)
#print axioms exists_rep
#print axioms lemM
#print axioms s_sq
#print axioms lemY
#print axioms y_sq
#print axioms inner_v_y
#print axioms exists_maxEven
#print axioms MaxEven.seventeen_y_mem
#print axioms MaxEven.y_not_mem
#print axioms MaxEven.lemMax_b
#print axioms MaxEven.mul306_mem
#print axioms MaxEven.mem_of_dual_even
#print axioms MaxEven.parity
#print axioms MaxEven.mul102_mem
#print axioms MaxEven.norm51
#print axioms eq_adm
#print axioms eq_adm_hasWitness
#print axioms graph_to_eq_adm
-- Group 3: structure of D(N) (DiscForm.lean), Gauss sum, Milgram classification (Gauss17/FiniteForms.lean)
#print axioms MaxEven.primary_decomp
#print axioms MaxEven.coprime_orth
#print axioms MaxEven.d17_cyclic
#print axioms MaxEven.d2_odd
#print axioms MaxEven.d2_rank
#print axioms MaxEven.d3_norm
#print axioms MaxEven.d3_rank
#print axioms ternary_isotropic_F3
#print axioms gauss17_sq
#print axioms gauss17
#print axioms classification_finite
#print axioms milgram_int
#print axioms forms_classification
#print axioms det_cases
#print axioms formI_milgram
#print axioms formII_milgram
-- Group 5: genus-I reduction (GenusIReduce.lean)
#print axioms lemA1_geom
#print axioms A1_24_roots
#print axioms genusI_impossible_general
