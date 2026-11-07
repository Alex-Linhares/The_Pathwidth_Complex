/-
Axiom audit for `lean/MOSPFormalization/Search/MinorTabu.lean` and
`lean/MOSPFormalization/Blockage.lean` (the `paper1/axiom_check.lean` pattern). Expected:
`[propext, Classical.choice, Quot.sound]` on every line.

    cd lean && lake env lean ../reports/scratch/minor_tabu_lean/axiom_check.lean
-/
import MOSPFormalization

open MOSPFormalization MOSPFormalization.MinorTabu MOSPFormalization.Blockage

-- the walk
#print axioms Idem.mergeRep
#print axioms Idem.ufRep
#print axioms mergeRep_ne_self
#print axioms ufRep_ne_self
#print axioms quotient_id
#print axioms quotient_adj_rep
#print axioms contractEdge_quotient
#print axioms applySeq_ufSeq
#print axioms isContractionSeq_ufSeq
#print axioms mem_removed_ufSeq
#print axioms applySeq_ufSeq_id
#print axioms isContractionSeq_ufSeq_id
#print axioms mem_removed_ufSeq_id
#print axioms tabuMinor_eq
#print axioms removed_ufSeq_id_eq
#print axioms pathwidth_tabuMinor_le
#print axioms IsForest.isContractionSeq
#print axioms IsForest.pathwidth_le
-- the two certificate kinds
#print axioms floor_sound_of_refutation
#print axioms floor_sound_of_degeneracy
#print axioms degeneracy_tabuMinor_le
#print axioms Justified.edgesOf
#print axioms Justified.le_pathwidth_tabuMinor
#print axioms Justified.le_pathwidth
-- the run
#print axioms Run.le_output_iff
#print axioms Run.given_le_output
#print axioms tabu_output_le_pathwidth
#print axioms tabu_output_ge_of_visited_refutation
#print axioms tabu_output_ge_of_refuted
#print axioms exists_visited_of_le_output
#print axioms reaches_iff
#print axioms output_eq_pathwidth_iff
-- MOSP units
#print axioms MOSPInstance.floor_sound_of_refutation_mosp
#print axioms MOSPInstance.tabu_output_lt_mospValue
-- blockages
#print axioms complementary_compl
#print axioms inter_compl
#print axioms complementary_union_compl
#print axioms union_inter_compl
#print axioms IsBlockage.mem_of_mem
#print axioms IsBlockage.empty_mem_and_univ_not_mem
#print axioms att_prefixUnion_subset
#print axioms att_prefixUnion_succ_subset
#print axioms prefixUnion_succ_sdiff_subset
#print axioms prefixUnion_last
#print axioms pathwidth_ge_of_isBlockage
