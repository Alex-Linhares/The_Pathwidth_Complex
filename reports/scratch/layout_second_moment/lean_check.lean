import MOSPFormalization.LayoutMoment
open MOSPFormalization
-- the Lean chain on rationals, to compare with learning.layout_moment.chain_q_exact
#print axioms MOSPFormalization.expected_narrowLayouts
#print axioms MOSPFormalization.narrowWeight_eq
#print axioms MOSPFormalization.sum_gnpWeight_pattern
#print axioms MOSPFormalization.vertexSepOfLayout_comap_relabel
#print axioms MOSPFormalization.gnpWeight_comap
#eval (List.range 8).flatMap (fun n => (List.range n).map (fun w =>
  ((n, w), chainQ (K := ℚ) n (1/2) w, chainQ (K := ℚ) n (3/10) w, chainQ (K := ℚ) n (1/7) w)))
