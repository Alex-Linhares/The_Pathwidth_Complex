/-
Copyright (c) 2026 Alexandre Linhares. All rights reserved.
Released under the MIT license as described in the file LICENSE.

# Register sufficiency exceeds `pw(G_u) + 1` without bound

On the complete binary out-tree of height `h` (`binaryOutTree h`, root → leaves):

* `pb_binaryOutTree`: the one-shot black pebble demand is **exactly `h + 1`** — the layout
  formula `pb_eq_topologicalDemand` (`RegisterSufficiencyFormula.lean`) with
  `topologicalDemand_binaryOutTree` (`BinaryOutTreeDemand.lean`: every topological layout has a
  step with `h` earlier vertices still waiting for a successor, and the depth-first layout
  attains it);
* `pbw_binaryOutTree_le`: the black-white demand, which is `pw(G_u) + 1` (Lengauer, row 13), is
  at most `⌈h/2⌉ + 1`, because `G_u` is the tree itself and the tree has pathwidth `≤ ⌈h/2⌉`
  (`BinaryOutTreeWidth.lean`);
* `pb_sub_pbw_binaryOutTree`: so `pb − pbw ≥ ⌊h/2⌋`, and `exists_gap_binaryOutTree`: **for
  every `c` some height has `pbw + c < pb`**. No constant band `pw(G_u) + 1 ≤ pb ≤ pw(G_u) + 1 + c`
  holds for the one-shot game: Garey & Johnson's PO1 is a container of the complex, not a
  sandwich member.

Measured (`reports/scratch/ss7_register_sufficiency/binary_tree_gap.log`): `pb = h + 1` and
`pw = ⌈h/2⌉` at `h = 0..6`, so the pathwidth bound is sharp and the gap is `⌊h/2⌋` exactly.
-/

import MOSPFormalization.Complex.RegisterSufficiencyFormula
import MOSPFormalization.Complex.BinaryOutTreeDemand
import MOSPFormalization.Complex.BinaryOutTreeWidth

set_option linter.unusedSectionVars false

namespace MOSPFormalization

namespace Complex

/-- The one-shot black pebble demand of the complete binary out-tree of height `h` is
`h + 1`. -/
theorem pb_binaryOutTree (h : ℕ) : pb (binaryOutTree h) = h + 1 := by
  rw [pb_eq_topologicalDemand, topologicalDemand_binaryOutTree]

/-- `pb − pbw ≥ ⌊h/2⌋` on the binary out-tree of height `h`. -/
theorem pb_sub_pbw_binaryOutTree (h : ℕ) :
    h / 2 ≤ pb (binaryOutTree h) - pbw (binaryOutTree h) := by
  have h1 := pb_binaryOutTree h
  have h2 := pbw_binaryOutTree_le h
  omega

/-- The gap between the black and the black-white one-shot demands is unbounded. -/
theorem exists_gap_binaryOutTree (c : ℕ) :
    ∃ h, pbw (binaryOutTree h) + c < pb (binaryOutTree h) := by
  refine ⟨2 * c + 2, ?_⟩
  have h1 := pb_binaryOutTree (2 * c + 2)
  have h2 := pbw_binaryOutTree_le (2 * c + 2)
  omega

/-- In pathwidth terms: `pw(G_u) + 1 + ⌊h/2⌋ ≤ pb` on the binary out-tree. -/
theorem pathwidth_lengauerU_add_le_pb_binaryOutTree (h : ℕ) :
    pathwidth (lengauerU (binaryOutTree h)) + 1 + h / 2 ≤ pb (binaryOutTree h) := by
  have h1 := pb_binaryOutTree h
  have h2 := pathwidth_binaryTree_le h
  rw [lengauerU_binaryOutTree]
  omega

end Complex

end MOSPFormalization
