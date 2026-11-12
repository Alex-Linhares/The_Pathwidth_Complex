# SS7 and register sufficiency: two containers of the complex

*2026-11-12. The item "Two Garey & Johnson problems that contain the complex" of
`paper1/todo.md`, after `reports/garey_johnson_complex.md` §3. Four provers and one
literature agent ran in parallel on briefs written from the brute force of §1–§3; the
coordinator assembled the files, the audit and this report.*

## §0 Summary

Garey & Johnson's 1979 list holds no member of the pathwidth complex, but two of its
entries contain it. Both are now settled, each with a Lean theorem, a smallest witness
and a brute-force check behind every statement.

**SS7, SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST (p. 238), is a container, not a
member.** MOSP embeds: an opening task at cost `+1` and a closing task at cost `−1` per
customer, a task at cost `0` per pattern, `open(c) ≺ p ≺ close(c)` for every pattern `p`
customer `c` requires and `open(c) ≺ close(c)` for every customer, and the SS7 optimum of
the embedded instance equals the number of open stacks, `mospValue = pw(MOSP graph) + 1`
(`Complex/SequencingMaxCost.lean`, `ss7Value_toSS7`, both directions, for every instance
with a requirement; every matrix with `≤ 3` customers and `≤ 3` patterns checked, 673 of
them). The image has costs in `{−1, 0, 1}`, the restriction Garey & Johnson record as
NP-complete, so the 1979 list carries open stacks without naming them, as the sub-case
that is pathwidth plus one of the customer graph. General SS7 has **no derived graph**:
the value is not a function of the comparability graph and the costs (two tasks, `a ≺ b`
at `+1, −1` has value `1`, its dual `0`; `exists_same_compGraph_cost_ne_ss7Value`), and
no graph on the tasks whose adjacency reads the two costs and the mutual order (nor, on
paper, any bounded-radius rule on the Hasse diagram) is within a constant of the value
(`no_local_derived_graph`: an antichain of `+1` tasks forces such tasks adjacent, and
matched pairs `a_i ≺ b_i` then carry a clique at value `1`). The restriction of SS7 to
MOSP-shaped instances is exactly MOSP; the series-parallel restriction that Abdel-Wahab &
Kameda (1978) solve in polynomial time meets MOSP only where the MOSP graph is a disjoint
union of cliques with disjoint pattern sets (N-free ⇔ customers sharing a pattern have
equal pattern sets, all 673 matrices), i.e. where the optimum is the largest block.
Proposed status: **container**; its MOSP-shaped restriction **member** (= row 1).

**PO1, REGISTER SUFFICIENCY (p. 272), is a container too, with an unbounded gap.**
The one-shot black pebble game with a retained set `R` (Sethi 1975; `R = outputs` is
Garey & Johnson's, `R = ∅` is Kirousis & Papadimitriou's `pb`) equals **pathwidth with a
precedence constraint on the layout**:

    pb_R(D) = 1 + min over topological layouts σ of max_i |{w : σ(w) < i, w ∈ R or w has a successor at ≥ i}|

(`Complex/RegisterSufficiencyFormula.lean`, every digraph and every `R`, both sides `0`
when no topological layout exists; checked on all 33,867 labelled dags to 6 vertices
under both retention conventions against a game search and a brute force over
orderings, and on 2,000 random dags on 9 vertices). **The formula is in print**: Austrin,
Pitassi & Wu (2011), Lemma 2.12, state `BP1s(D) = Layout(D; V, max)` with the same
two-line argument, and cite Ravi, Agrawal & Klein (1991) for the layout reading of
register sufficiency; their count is taken after the placed vertex is dropped, which is
one below the count at the placement (a single vertex has `Layout = 0` and needs one
pebble), so the exact statement is `BP1s = Layout + 1`, the form proved here. What is
ours is the retained set, the Lean proof and the comparison with row 13. Row 13 gives `pbw(D) = pw(G_u) + 1 ≤
pb(D)`. The gap is unbounded: on the **complete binary out-tree** of height `h`
(root → leaves, in-degrees `≤ 1` so `G_u` is the tree itself) `pb = h + 1` while
`pw = ⌈h/2⌉`, so `pb − pbw = ⌊h/2⌋` (`Complex/BinaryOutTree*.lean`: every topological
layout has a step with `h` earlier vertices still waiting for a successor, and the tree
has pathwidth `≤ ⌈h/2⌉`; measured exactly at `h ≤ 6`). No constant band `pw ≤ f ≤ pw + c`
exists, so PO1 is not a sandwich member. We found no prior statement of the gap
or of its family. The parametric question — is `pb ≤ f(pw(G_u))`
— is answered for out-forests (`pb ≤ 2 pw + 2`, on paper, §3.5) and left open for
general dags, where every dag on record satisfies `pb ≤ 2 pw(G_u) + 1` (all dags to 6
vertices, 20,500 sparse random dags to 11). The link to the complex is through the best
orientation: `min over acyclic orientations of pb = pw + 1` (Kirousis & Papadimitriou
Thm 3.1, row 13), not through a given dag.

A by-product: `fixed_parameter_algorithm/pathwidth_fpt.py` returns `1` on the complete
binary trees of height 4 and 5 (31 and 63 vertices), whose pathwidth is `2` and `3`
(the C program proves both by refutation); the Python branch and bound is wrong on trees
above its exact-DP threshold, presumably in its pendant-removal preprocessing (§3.7).

Nothing was re-solved; `solutions/` is untouched; the compute is under one core-hour.
Lean: seven new files, no `sorry`, no `axiom`, every theorem on the three standard axioms
(§5). Literature: §4.

## §1 SS7 contains MOSP

### §1.1 The problem as Garey & Johnson state it

p. 238: *Instance*: a set `T` of tasks, a partial order `≺` on `T`, a cost `c(t) ∈ ℤ` for
each task ("if `c(t) < 0`, it can be viewed as a profit"), a constant `K ∈ ℤ`.
*Question*: is there a one-processor schedule `σ` obeying the precedence constraints
such that for every task `t` the sum of the costs of the tasks `t'` with `σ(t') ≤ σ(t)`
is at most `K`? Reference Abdel-Wahab (1976), transformation from REGISTER SUFFICIENCY.
Comment: NP-complete even if `c(t) ∈ {−1, 0, 1}` for all `t`; polynomial when `≺` is
series-parallel (Abdel-Wahab & Kameda 1978; Monma & Sidney 1977).

In Lean (`SequencingMaxCost.lean`): `SS7Instance T` carries `prec : T → T → Prop` and
`cost : T → ℤ`; a layout `σ : LinearLayout T` is a linear extension when `prec a b →
σ a < σ b` (any relation is accepted; the value depends only on the transitive closure);
`prefixCost σ i` is the sum over the tasks at positions `≤ i`; `WithinCost K` asks for a
linear extension with every prefix cost `≤ K`; `ss7Value = sInf {K : ℕ | WithinCost K}`.

### §1.2 The embedding

Tasks `C ⊕ (C ⊕ P)`: `inl c` is `open(c)` at `+1`, `inr (inl c)` is `close(c)` at `−1`,
`inr (inr p)` is the pattern `p` at `0`. Precedence: `open(c) ≺ close(c)` for every
customer, `open(c) ≺ p` and `p ≺ close(c)` whenever `c` requires `p`, nothing else
(`MOSPInstance.toSS7`). The pair `open(c) ≺ close(c)` is implied by transitivity when `c`
requires a pattern and is **necessary** when it does not: without it `close(c)` may precede
`open(c)` and lower every prefix sum by one, and the equality fails on 232 of the 673
matrices below (`ss7_embed_exhaustive.log`). The earlier check (`garey_johnson/ss7_mosp.py`)
did not see this because it drew only matrices with a product in every row.

**Theorem** (`ss7Value_toSS7`, `ss7Value_toSS7_eq_pathwidth_add_one`). For every instance
with a requirement, `ss7Value (toSS7 M) = mospValue M = pathwidth (mospGraph M) + 1`.

*Pattern order to linear extension* (`exists_linearExtension_of_layout`): given a pattern
order `σ`, sort the tasks by the key `open(c) ↦ 3·first(c)`, `p ↦ 3·σ(p) + 1`,
`close(c) ↦ 3·last(c) + 2`, with `first`/`last` the positions of the customer's first and
last pattern, and the pairs of pattern-less customers at the end with distinct keys. Every
precedence strictly increases the key. In any linear extension the prefix cost at a
position is the number of customers whose opening task is placed and whose closing task is
not (`prefixCost_toSS7`; the pair `open ≺ close` makes "close placed" imply "open placed",
and patterns cost `0`). At the position of a pattern `p` at step `s` such a customer has
`first ≤ s ≤ last`, so it is active at `s`; at an opening or closing task the same holds at
`first` or `last`; the pattern-less pairs at the end count at most one, and one stack is
open somewhere under the hypothesis. So every prefix cost is `≤ maxOpenStacks σ`.

*Linear extension to pattern order* (`exists_layout_of_linearExtension`, no hypothesis):
restrict the extension to the patterns. A customer active at step `j` of the restriction
has a pattern at `≤ j` and one at `≥ j`, so in the extension its opening task is before and
its closing task after the pattern placed at `j`; the active customers inject into the set
the prefix cost counts, which is `≤ K`.

*Edge cases.* With no requirement `mospValue = 0` (`mospValue_eq_zero_of_forall_not`) while
the embedded SS7 value is `1` if there is a customer (`ss7Value_toSS7_eq_one_of_forall_not`:
some opening task is placed with its closing task later) and `0` if there is none
(`ss7Value_toSS7_eq_zero_of_isEmpty`). The hypothesis `∃ c p, requires c p` is exactly the
one `mospValue_eq_pathwidth_add_one` carries.

*Costs.* `toSS7_cost_mem`: every cost is in `{−1, 0, 1}`. Garey & Johnson's comment —
NP-complete even with costs in `{−1, 0, 1}` — is the statement the embedding lands in; it
is cited, not proved (no complexity theory in the development). Since MOSP is NP-hard
(Linhares & Yanasse 2002) the embedding is a second proof of that comment, through the
other special case than the one Abdel-Wahab used.

### §1.3 Brute force

`reports/scratch/ss7_register_sufficiency/ss7_embed_exhaustive.py`: every 0/1 matrix with
`n ≤ 3` customers and `m ≤ 3` patterns, rows allowed empty; the SS7 optimum of the
embedded poset by a DP over order ideals (`paper1/ss7_register.py::ss7_value`), the MOSP
optimum by brute force over pattern orders, and the exact pathwidth of the MOSP graph plus
one (subset DP). 673 matrices with a requirement, **0 mismatches**; the 16 shapes without
a requirement give `(SS7, MOSP) = (0, 0)` with no customer and `(1, 0)` otherwise. The
log is `ss7_embed_exhaustive.log`. (`garey_johnson/ss7_mosp.py`'s 300 random instances
with `n ≤ 5`, `m ≤ 6` stand.)

## §2 Member or container

### §2.1 What a member needs

Section 3's members are *problems with a derived graph*: a graph `H(I)` read off the
instance locally (the MOSP graph: customers adjacent iff a pattern needs both; `G_u`:
an arc or a common successor), with `f(I) = pw(H(I)) + c`. Without a locality
requirement the question is void — map an instance of value `v` to `K_v` — so the
negative results fix what "read off the instance" may mean.

### §2.2 The value is not a function of the comparability graph and the costs

Two tasks, `a ≺ b`, `c(a) = +1`, `c(b) = −1`: the only extension is `a, b`, prefix sums
`1, 0`, value `1`. The dual order `b ≺ a`: prefix sums `−1, 0`, value `0`. Same costs,
same comparability graph (an edge). Lean: `SS7Instance.compGraph`, `SS7Instance.dual`,
`compGraph_dual`, `ss7Value_dual_ne`, `exists_same_compGraph_cost_ne_ss7Value`. So any
derived graph must read the orientation of `≺` against the signs.

### §2.3 No pairwise-local derived graph, and none of bounded radius

Let `localGraph rule I` join `a ≠ b` iff `rule (c a) (c b) (mutual a b)` or the
symmetric call, where `mutual ∈ {lt, gt, none}` is the order between the two tasks.

**Theorem** (`no_local_derived_graph`). For every `rule` and every constant `c` there is
an instance with `ss7Value ≠ pw(localGraph rule I) + c`. Witnesses: `A₁` (one task at
`+1`: value `1`, pathwidth `0`, so `c = 1`); `A₂` (two incomparable tasks at `+1`: value
`2`, so the graph has an edge, so `rule 1 1 none` holds); `D₂` (`a₁ ≺ b₁`, `a₂ ≺ b₂`,
`a` at `+1`, `b` at `−1`: value `1` by `a₁ b₁ a₂ b₂`, but `a₁ a₂` are adjacent, pathwidth
`≥ 1`, value would be `≥ 2`). Checked: `ss7_witnesses.log` (`A_k = k`, `D_k = 1`, `k ≤ 4`).
The band form (`|value − pw| ≤ c` for all instances) fails the same way with `A_{2c+2}`
and `D_{2c+2}`, whose opening tasks form a clique `K_{2c+2}`.

*Bounded radius, on paper.* Let the rule read, for a pair `{a, b}`, the sub-instance
induced on the radius-`r` balls around `a` and `b` in the Hasse diagram (cover graph), with
the order and the costs on that set. On a chain `t₁ ≺ … ≺ t_L` with costs `±1` the ball is
a window of `2r + 1` consecutive tasks, and for `|i − j| > 2r + 1` interior pairs with
all-`+1` windows all see the same sub-instance. The all-`+1` chain has value `L`; if those
pairs were non-adjacent, `H` would have bandwidth `≤ 2r + 1` outside `2r` end vertices,
pathwidth `O(r)`, so for `L` large they are adjacent. The chain of `m` blocks
`(+1)^{2r+1} (−1)^{2r+1}` has value `2r + 1`, and the middle tasks of its `+1` blocks are
pairwise far apart with all-`+1` windows: a clique `K_m` in `H`, pathwidth `≥ m − 1`. So no
rule of radius `r` is within any constant of the value, on chains alone. Not in Lean (the
quantification over rules of radius `r` is not worth the formalisation); the `r = 0` case
is the theorem above.

### §2.4 Which restrictions are members

*MOSP-shaped instances.* Costs in `{−1, 0, 1}`; the `+1` tasks `O` and the `−1` tasks in
bijection `o ↦ k(o)` with `o ≺ k(o)`; each `0`-task `p` has as predecessors a set `O_p ⊆ O`
and as successors exactly `{k(o) : o ∈ O_p}`; no other relation (the order is the
transitive closure of these). This is the image of `toSS7` up to relabelling, and its value
is `pw(G) + 1` for the graph on `O` with `o ~ o'` iff some `O_p` holds both — the theorem of
§1.2. *(Lean: the image statement is `ss7Value_toSS7`; relabelling invariance is
`SS7Instance.ss7Value_relabel`, and the matched pairs `D_k` of §2.3 are built exactly so,
as `toSS7` of a pattern-less instance relabelled onto `Fin n`, `pairsInstance`.)* Status: **member**, and it is row 1 under another name.

*Abdel-Wahab's register-sufficiency instances* (`compute(v)` at `+1`, `free(v)` at `−1`,
`compute(u) ≺ compute(v) ≺ free(u)` per arc, `compute(v) ≺ free(v)`): their value is
`pb(D)` (`garey_johnson/ss7_mosp.py`, all 1,099 dags to 5 vertices), which §3 shows is not
`pw(G_u) + c` for any `c`. A restriction of SS7 that is itself a container.

*Series-parallel orders* (Abdel-Wahab & Kameda 1978, polynomial). An embedded MOSP
instance is N-free iff any two customers sharing a pattern have the same pattern set
(`ss7_witnesses.py`, all 673 matrices, 0 mismatches; 225 of them are series-parallel):
the N is `open(c₁) ≺ p`, `open(c₂) ≺ p`, `open(c₂) ≺ p'` with `p' ∉ P_{c₁}`, and its
mirror on closing tasks. Then the MOSP graph is a disjoint union of cliques with disjoint
pattern sets and the optimum is the largest clique — the instances that need no algorithm.
So the polynomial class of SS7 meets the complex only at pathwidth = clique number − 1;
it corresponds to no pathwidth class worth the name, and the pathwidth problem restricted
to those graphs is trivially polynomial too.

### §2.5 Verdict and proposed rows

| problem | relation | Lean | status |
|---|---|---|---|
| SS7, max cumulative cost (G&J p. 238; Abdel-Wahab 1976) | contains MOSP (`ss7Value (toSS7 M) = Z(M) = pw(G_M) + 1`, costs in `{−1, 0, 1}`) and register sufficiency (Abdel-Wahab's encoding, = `pb`); no derived graph: not a function of comparability graph + costs (2 tasks), no pairwise-local or bounded-radius rule within any constant | `ss7Value_toSS7`, `ss7Value_toSS7_eq_pathwidth_add_one`, `toSS7_cost_mem`, `exists_same_compGraph_cost_ne_ss7Value`, `no_local_derived_graph` (`Complex/SequencingMaxCost.lean`) | **container** |
| SS7 on MOSP-shaped instances | `= Z = pw + 1` of the customer graph | the same theorem | **member** (= row 1) |
| PO1, register sufficiency (G&J p. 272; Sethi 1975) | `pb_R(D) = 1 + min_{σ topological} max_i |preBoundary|` (vertex separation with a precedence constraint); `pw(G_u) + 1 = pbw ≤ pb`, gap `⌊h/2⌋` on binary out-trees, unbounded; `min_{orientations} pb = pw + 1` (row 13) | `pbR_eq_topologicalDemand`, `pb_eq_topologicalDemand`, `registerDemand_eq_topologicalDemand` (`RegisterSufficiencyFormula.lean`); `pb_binaryOutTree_ge`, `pbw_binaryOutTree_le`, `exists_gap_binaryOutTree` (`BinaryOutTree*.lean`) | **container** (no constant band; `≤ 2 pw + 1` on every dag on record, open in general) |

Proposed for `paper1/equivalences.md` (rows 15–16 of the master table, or a short
"containers" table after it) and for Section 3, not applied — §6.

## §3 Register sufficiency

### §3.1 The game as Garey & Johnson state it

p. 272 (an arc `(v, u)` means `u` is an operand of `v`; below, arcs run operand →
consumer, so Garey & Johnson's in-degree-0 vertices are our sinks): an ordering
`v₁, …, v_n` and register contents `S₀ = ∅, S₁, …, S_n`, `|S_i| ≤ K`, `v_i ∈ S_i`,
`S_i − {v_i} ⊆ S_{i−1}`, every operand of `v_i` in `S_{i−1}`, and every output in `S_n`.
In pebble vocabulary: a black pebble goes on a never-pebbled vertex whose predecessors are
pebbled; a pebble not on an output may be removed; every vertex is pebbled exactly once;
the play ends when every vertex has been pebbled, the outputs still carrying their pebbles.
`RegisterSufficiency.lean` defines the game with an arbitrary retained set `R`
(`BlackMove.LegalR`, `BlackStepR`), `outputs D`, the topological layouts
(`IsTopological`), the pre-placement boundary

    preBoundary D R σ i = {w : σ(w) < i and (w ∈ R or ∃ u, w → u, σ(u) ≥ i)},

`layoutDemand = max_i (|preBoundary i| + 1)` and `topologicalDemand = min` over
topological layouts. The end condition: the coordinator's first draft of `BlackPebblesWithinR`
ended at the all-`done` position, which a play with `R ≠ ∅` can never reach (a retained
pebble is never removed, so `done` is never reached on `R`); the prover found this and
proved the formula for the end condition "every vertex has been pebbled", which is now
the definition (`BlackPebblesWithinR`, `pbR`, `registerDemand`); at `R = ∅` it agrees with
Kirousis & Papadimitriou's all-`done` form (`blackPebblesWithinR_empty_iff_reflTransGen`,
`blackPebblesWithinR_empty_iff`, `pbR_empty`: the black pebbles of a completed position
are removed one by one). A lesson of the kind `CLAUDE.md` records: a definition written
before its first theorem was wrong on every instance with an output.

### §3.2 The layout formula

**Theorem** (`pbR_eq_topologicalDemand`; `pb_eq_topologicalDemand` at `R = ∅`;
`registerDemand_eq_topologicalDemand` at `R = outputs`). For every digraph on a finite
type and every `R`, `pbR D R = topologicalDemand D R`; both sides are `0` when no
topological layout exists.

*Lower bound* (`exists_isTopological_of_blackPebblesWithinR`): lay the vertices out in the
order of placement. It is topological (a vertex is placed only when its predecessors are
pebbled). Just after `v_i` is placed, every earlier vertex that is retained still carries
its pebble, and so does every earlier vertex with a successor `u` at step `≥ i`: the
placement of `u` needs it pebbled and a pebble, once removed, never returns; with `v_i`
that is `|preBoundary i| + 1 ≤ K` pebbles. *Upper bound*
(`blackPebblesWithinR_of_isTopological`): place in layout order and drop every unretained
pebble as soon as its last successor is placed; the pebbles on the board when `v_i` goes
down are exactly `preBoundary i` plus `v_i`. This is Kirousis & Papadimitriou's black
strategy of `PebblingGu.lean` (`blackPebblesWithin_layoutOrient`) generalised from a layout
orientation to any topological layout and any retained set — and it is Austrin, Pitassi &
Wu's proof of their Lemma 2.12 (§4), up to the pebble on the vertex being placed.

The boundary at step `i` depends only on the set `S` of the first `i` vertices — it is the
out-boundary `{w ∈ S : w ∈ R or succ(w) ⊄ S}` of the order ideal `S` — so the minimum is a
DP over ideals (`paper1/ss7_register.py::pb_ideal`), the form the checks use.

*Brute force* (`pb_formula_check.py`, log beside it): every labelled dag on `1..6`
vertices (33,867), game search (`pb_game`) against the ideal DP against a brute force over
topological orderings (`pb_layouts`), with `R = ∅` and `R = sinks`: **0 mismatches** in all
four comparisons; 2,000 random dags on 9 vertices (arc probability 0.15–0.7), game
against ideal DP, both conventions: **0 mismatches**, `pb` up to 9. (`garey_johnson/
pb_topological.py`'s 33,867 at `R = ∅` stand.)

### §3.3 The gap to `pw(G_u) + 1` is unbounded: binary out-trees

Row 13: `pbw(D) = pw(G_u) + 1` for every nonempty digraph (`pbw_eq_pathwidth_lengauerU_add_one`)
and a black play is a black-white play, so `pw(G_u) + 1 ≤ pb(D)`
(`pathwidth_lengauerU_add_one_le_pb`, whenever a play exists).

Let `T_h` be the complete binary tree of height `h` with every arc directed from parent to
child (`binaryOutTree h`, `2^{h+1} − 1` vertices). In-degrees are at most one, so `G_u` is
the tree itself (`lengauerU_binaryOutTree`).

| `h` | `n` | `pb(T_h)` | `pw(T_h)` | `pbw` | gap |
|---|---|---|---|---|---|
| 0 | 1 | 1 | 0 | 1 | 0 |
| 1 | 3 | 2 | 1 | 2 | 0 |
| 2 | 7 | 3 | 1 | 2 | 1 |
| 3 | 15 | 4 | 2 | 3 | 1 |
| 4 | 31 | 5 | 2 | 3 | 2 |
| 5 | 63 | 6 | 3 | 4 | 2 |
| 6 | 127 | 7 | 3 | 4 | 3 |

(`binary_tree_gap.py`: `pb` by the ideal DP to `h = 4` — 458,329 rooted subtrees — and by
the out-tree recursion of §3.5 for `h ≥ 5`; `pw` by the subset DP to 15 vertices and by the C
program `pathwidth_solver/cli/pathwidth` with a refutation above, 2 s in all.)

**Theorem** (Lean). `pb(T_h) = h + 1` exactly (`pb_binaryOutTree`: the layout formula with
`topologicalDemand_binaryOutTree = h + 1`, whose `≤` is the depth-first layout) and
`pbw(T_h) = pw(T_h) + 1 ≤ ⌈h/2⌉ + 1` (`pbw_binaryOutTree_le`), so
`pb(T_h) − pbw(T_h) ≥ ⌊h/2⌋` (`pb_sub_pbw_binaryOutTree`) and the gap is unbounded
(`exists_gap_binaryOutTree`: for every `c`, height `2c + 2` has `pbw + c < pb`); in
pathwidth terms `pw(G_u) + 1 + ⌊h/2⌋ ≤ pb` (`pathwidth_lengauerU_add_le_pb_binaryOutTree`).

*The precedence argument* (`exists_preBoundary_binaryOutTree`): every topological layout
of `T_h` has a step with `h` earlier vertices waiting for a successor. Induction: the root
is placed first; of the two subtrees let `B` be the one completed first; the layout
restricted to `B` is a topological layout of `T_{h−1}`, so at some step `i` inside `B` it
has `h − 1` waiting vertices of `B`; at that step the other side (`A` with the root) has a
vertex placed before `i` (the root) and one at or after (its last vertex, which comes after
`B`'s), and it is connected root-first, so some vertex outside `B` placed before `i` has a
successor at or after `i`: `h` in all. *The pathwidth bound* (`pathwidth_binaryTree_le`):
remove the path child–root–child from `T_{h+2}` and four copies of `T_h` remain, so
`pw(T_{h+2}) ≤ pw(T_h) + 1` (`tree_pathwidth_le_pathwidth_compl_path_add_one` of
`TreeBound.lean`), and `pw(T_0) = 0`, `pw(T_1) = 1`. The value `⌈h/2⌉` is sharp (the table;
Ellis, Sudborough & Turner's recursion for trees), but only `≤` is needed and proved.

The retention term is separate and larger: `T_3` with its 8 leaves retained has `pb = 9`
against `4` (`binary_tree_gap.log`); the single-output comparison of
`garey_johnson_complex.md` §3.2 is the right one, and the binary out-tree has `2^h`
outputs, so the family is stated for `pb` (`R = ∅`), where Garey & Johnson's form with
one output added as a common sink would give the same gap up to one.

### §3.4 Where the gap comes from

The pre-placement boundary is a vertex separation taken on the *underlying* graph along a
*topological* layout; `pw(G_u)` is a vertex separation on a *larger* graph along *any*
layout. White pebbles buy the second freedom at the price of the common-successor cliques
(Lengauer's theorem). On an out-tree the cliques are empty and the constraint is "root
first", which forces a vertex to wait while an entire sibling subtree is done — one pebble
per level of binary branching — while the unconstrained layout starts in the middle and
pays one per two levels. The 5-vertex witness of `garey_johnson_complex.md` §3.2
(`0→1, 0→2, 1→4, 2→3`) is the same mechanism at the root.

The ternary out-tree has no gap: `pb = h + 1 = pw + 1` (`pathwidth_ternaryTree` of
`TreeBound.lean` gives `pw = h`; measured at `h = 1, 2`). The in-tree orientation of `T_3`
has `pb = 5` against `pbw = 4`: a gap too, by the sibling cliques in `G_u`.

### §3.5 Is `pb` bounded by a function of `pw(G_u)`?

*Out-forests, on paper.* For an out-tree `T` with root `r` and child subtrees `T₁, …, T_m`
let `g(T) = pb(T) − 1` be the least maximum boundary. Doing the subtrees one after another,
the one of largest `g` last, costs `max(1, g₍₁₎, g₍₂₎ + 1)` (the root waits during every
subtree but the last; `g₍₁₎ ≥ g₍₂₎` the two largest values). The recursion is exact:
`g(T) = max(g₍₁₎, g₍₂₎ + 1)` (`1` with one child, `0` at a leaf) on 4,200 random out-trees
to 14 vertices against the ideal DP (`binary_tree_gap.log`), interleaving never helping.
From the `≤` direction alone: `g(T) ≥ k` forces either a subtree with `g ≥ k` or two with
`g ≥ k − 1`, so by induction `T` contains a subdivision of `T_{k−1}` rooted at a vertex,
hence `pw(T) ≥ pw(T_{k−1}) = ⌈(k−1)/2⌉` and **`pb(T) ≤ 2 pw(T) + 2` for every out-forest**
(`G_u = T`). The binary out-trees attain ratio `2`.

*General dags, measured.* `pb_vs_pwgu.py`: the largest `pb` at each `pw(G_u)` over every
labelled dag to 6 vertices and 20,500 sparse random dags on 7–11 vertices (1.2–2.5 arcs
per vertex):

| `pw(G_u)` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| largest `pb` found | 1 | 3 | 5 | 6 | 7 | 8 | 8 | 8 |
| `2 pw + 1` | 1 | 3 | 5 | 7 | 9 | 11 | 13 | 15 |
| smallest dag with that `pb` | 1 | 5 (`0→1, 0→2, 1→4, 2→3`) | 7 (`0→2, 0→6, 1→2, 1→4, 1→5, 2→3, 2→4, 3→6, 4→5`) | 7 | 9 | 9 | 10 | 9 |

(`pb_vs_pwgu.log`; the larger values of `pw(G_u)` are under-sampled by the sparse draw.)

Every dag on record has `pb ≤ 2 pw(G_u) + 1`, with equality at
`pw(G_u) = 1, 2` (`pb = 3, 5`). Whether `pb ≤ 2 pw(G_u) + O(1)` holds for all dags is open
here; a proof would make PO1 a *parametric* sandwich member (`pw + 1 ≤ pb ≤ 2 pw + c`),
which is not the constant band Section 3's "sandwich" label means. The known results on
black against black-white pebbling (Meyer auf der Heide 1981; Kalyanasundaram & Schnitger
1992) concern the game with recomputation and do not transfer; §4.

### §3.6 The link to the complex

The complex sees PO1 through its best orientation: `min over acyclic orientations of
pb(D) = mpb(G) = pw(G) + 1` (Kirousis & Papadimitriou Thm 3.1, `mpb_eq_pathwidth_add_one`,
row 13), and the layout orientation attains it with the layout formula's own strategy
(`blackPebblesWithin_layoutOrient`). For a *given* dag the precedence constraint is a
genuine second parameter.

### §3.7 A solver bug found on the way

`fixed_parameter_algorithm/pathwidth_fpt.py::compute_pathwidth_fpt` returns `1` on the
complete binary trees of height 4 (31 vertices) and 5 (63 vertices); the exact values are
`2` and `3`, proved by `pathwidth_solver/cli/pathwidth` (refutations in under a second;
the subset DP agrees at height 3). Trees of pathwidth `≥ 2` are not caterpillars, and the
solver's documented first step — iterated removal of degree-1 vertices — reduces any tree
to nothing, which is sound for the greedy *upper* bound only. Not fixed here (the owner's
item list does not include it; `CLAUDE.md` already records the pipeline as giving upper
bounds); every pathwidth in this report above 18 vertices comes from the C program.

## §4 Literature

The literature agent's full record is the dated section `## SS7 and register sufficiency
(2026-11-12)` of `literature/MISSING.md` (G&J's bibliography entry verbatim; the four
sources; three neighbours obtained).

*The four sources.* None is openly served. **Abdel-Wahab (1976)**: G&J's entry reads
"Doctoral Thesis, Dept. of Electrical Engineering, University of Waterloo, Waterloo,
Ontario" — Waterloo, not Toronto; the owner's note is corrected; the thesis exists on
microfiche only (216 leaves) and is not in UWSpace. **Abdel-Wahab & Kameda (1978)**:
closed at INFORMS, no author or repository copy (abstract on record: "It is known that
this problem is in general NP-complete. For the special case where the precedence
constraints can be represented by a series-parallel graph, we present an algorithm …
whose running time does not grow faster than the square of the number of events").
**Sethi (1975)** and **Gilbert, Lengauer & Tarjan (1980)**: SIAM closed; their STOC versions
(1973, 1979) are in ACM's openly served backfile but `dl.acm.org` refuses non-browser
clients, so they are one browser click each for the owner
(`dl.acm.org/doi/pdf/10.1145/800125.804049`, `…/800135.804418`). Garey & Johnson's PO1
entry stands in for Sethi's definition (quoted in §3.1); Lengauer (1981, held) p. 2 and
Kirousis & Papadimitriou (1986, held) p. 2 describe Sethi's game as the progressive black
game and credit him with its NP-completeness.

*Obtained* (open repositories or author pages, into `literature/`):
`1977-Monma-Sidney-Sequencing-Series-Parallel-Precedence-Constraints-TR-Cornell-ORIE-347.pdf`
(G&J's other reference for the series-parallel case; Cornell eCommons; a scan with no
text layer), `2011-Austrin-Pitassi-Wu-Inapproximability-Treewidth-One-Shot-Pebbling-Layout-Problems-arXiv-1109.4910.pdf`
and `2010-Hertel-Pitassi-PSPACE-Completeness-Black-White-Pebbling-SICOMP.pdf`.

*Prior statements.* (a) **MOSP as a case of SS7: we found no prior statement.** Not in
G&J's entries, not in Monma & Sidney (no registers, intervals or layouts anywhere), not in
the abstracts of Abdel-Wahab & Kameda (1978, 1980) or Monma (1980), and no web search on
"open stacks" / "gate matrix layout" against "cumulative cost" / "Abdel-Wahab" / "register
sufficiency" returns a connection. The nearest object in print is Monma & Sidney's `CE_max`
(TR p. 19: transactions with a net change `c_j` and a maximum net increase `m_j`, cost
`max_i (Σ_{j<i} c_{s(j)} + m_{s(i)} − e_{s(i)})`), of which "the maximum cumulative cost
problem (CC_max) [2,3] [is] shown to be [a] special case … in [22]" (p. 20); MOSP is not of
that fixed-per-job form — which customers a pattern opens and closes depends on the
sequence — which is why the embedding needs the precedences. (b) **The layout formula for
register sufficiency is in print**: Austrin, Pitassi & Wu (2011) p. 4 "One-shot pebbling is
also equivalent to a problem known as Register Sufficiency [RAK91]", Table 1 (p. 9) places
one-shot black pebbling as the directed max-vertex layout problem beside pathwidth /
one-shot black-white pebbling / vertex separation, and Lemma 2.12 (p. 9–10) states
`BP1s(D) = Layout(D; V, max)` with `V_i(π) = {u : π(u) ≤ i < π(v) for some arc (u, v)}`
over topological `π`, proved by the two arguments of §3.2; as noted in §0 the count is one
below the pebbles at a placement, so the equality holds with `+ 1`. Bansal & Katzelnick
(2023, arXiv 2311.15639) call register sufficiency "the most well-known directed graph
layout problem with a min-max objective" and leave its approximation open. Neither
compares it with `pw(G_u)` or names a family with a growing gap; **we found no prior
statement of the gap**. Austrin, Pitassi & Wu p. 4 also record that the one-shot problems
are in NP while the unrestricted ones are PSPACE-complete (Gilbert, Lengauer & Tarjan
1980, described in Hertel & Pitassi p. 2623). (c) Series-parallel: Monma & Sidney TR p. 4
(the definition: series and parallel composition, reduction to a chain), p. 18 (the
decomposition-tree algorithm with a preference order on strings, `O(n log n)` comparisons,
after Lawler), pp. 19–20 (the explicit preference order for `CE_max`), Table I p. 24
(`CC_max` under general precedence "NP Hard [1]", i.e. the Abdel-Wahab thesis). The
`O(n²)` of Abdel-Wahab & Kameda (1978) and the `O(n log n)` of their 1980 paper are the
register-allocation line's own algorithms; §2.4 shows they meet MOSP only on the block
instances. (d) Pathwidth and register *allocation* of programs (Bodlaender, Gustedt & Telle
1998) is a different relation (interference graphs, not dag pebbling).

## §5 Lean inventory and axiom audit

Seven new files under `lean/MOSPFormalization/Complex/`, registered in `MOSPFormalization.lean`;
`lake build` of the whole development passes (`reports/scratch/ss7_register_sufficiency/lake_build_full.log`).
No `sorry`, no `axiom`, no `native_decide` in any of them (grep); `#print axioms` on every
declaration, logged one line per declaration, shows nothing beyond `propext`,
`Classical.choice`, `Quot.sound`:

| file | lines | declarations audited | main theorems | audit log |
|---|---|---|---|---|
| `SequencingMaxCost.lean` | 1,016 | 90 | `MOSPInstance.ss7Value_toSS7 M hreq`, `ss7Value_toSS7_eq_pathwidth_add_one`, `withinCost_toSS7_iff`, `exists_linearExtension_of_layout`, `exists_layout_of_linearExtension`, `prefixCost_toSS7`, `toSS7_cost_mem`, `ss7Value_toSS7_eq_one_of_forall_not`, `ss7Value_toSS7_eq_zero_of_isEmpty`; `SS7Instance.ss7Value_relabel`, `isLinearExtension_transGen_iff`, `ss7Value_le_iff`; `compGraph_dual`, `ss7Value_dualWitness = 1`, `ss7Value_dualWitness_dual = 0`, `ss7Value_dual_ne`, `exists_same_compGraph_cost_ne_ss7Value`; `pathwidth_eq_zero_of_forall_not_adj`, `ss7Value_antichain`, `ss7Value_pairsInstance`, `no_local_derived_graph`, `no_local_derived_graph_band` | `sequencing_max_cost_axioms.log` |
| `RegisterSufficiency.lean` | 131 | (definitions) | `BlackMove.LegalR`, `BlackStepR`, `BlackPebblesWithinR`, `pbR`, `outputs`, `registerDemand`, `IsTopological`, `preBoundary`, `layoutDemand`, `topologicalDemand`; `layoutDemand_le_iff` | — |
| `RegisterSufficiencyFormula.lean` | 770 | 45 (with the gap file: 49) | `pbR_eq_topologicalDemand D R`, `pb_eq_topologicalDemand D`, `registerDemand_eq_topologicalDemand D`, `exists_isTopological_of_blackPebblesWithinR`, `blackPebblesWithinR_of_isTopological`, `blackPebblesWithinR_empty_iff`, `pbR_empty`, `BlackPebblesWithinR.mono`, `blackPebblesWithinR_of_subset`, `pbR_le_pbR_of_subset`, `pbw_le_pb_of_exists`, `pathwidth_lengauerU_add_one_le_pb` | `register_sufficiency_formula_axioms.log` |
| `BinaryOutTree.lean` | 105 | (definitions) | `BVert`, `broot`, `binaryOutAdj`, `binaryOutTree`, `binaryTree` | — |
| `BinaryOutTreeWidth.lean` | 421 | 30 | `card_BVert` (`card + 1 = 2^(h+1)`), `binaryOutAdj_pred_unique`, `lengauerU_binaryOutTree`, `binaryTree_connected`, `binaryTree_isAcyclic`, `binaryTree_isTree`, `pathwidth_binaryTree_succ_le`, `pathwidth_binaryTree_le h : pw ≤ (h+1)/2`, `pbw_binaryOutTree_le` | `binary_out_tree_width_axioms.log` |
| `BinaryOutTreeDemand.lean` | 489 | 27 | `root_lt_of_keyTopological`, `exists_adj_across` (the cut lemma), `card_keyCut_succ_ge`, `exists_keyCut_card_ge`, `exists_preBoundary_binaryOutTree`, `layoutDemand_binaryOutTree_ge`, `exists_isTopological_layoutDemand_le` (depth-first), `topologicalDemand_binaryOutTree h = h + 1` | `binary_out_tree_demand_axioms.log` |
| `BinaryOutTreeGap.lean` | 66 | 4 | `pb_binaryOutTree h = h + 1`, `pb_sub_pbw_binaryOutTree : h/2 ≤ pb − pbw`, `exists_gap_binaryOutTree`, `pathwidth_lengauerU_add_le_pb_binaryOutTree` | in `register_sufficiency_formula_axioms.log` |

Two design notes from the provers, for whoever extends these files: `BVert (h+1)` is a
non-reducible definition, so `rw`/`simp` on equalities of `some …` terms at that type fail
("motive is not type-correct"); `BinaryOutTreeDemand.lean` introduces typed constructors
`bnone h`, `bsome j x`, and `BinaryOutTreeWidth.lean` does every such step in term mode.
And the demand file proves everything for an arbitrary key `f : BVert h → ℕ` with
`KeyTopological` and `keyCut`, restricting to a subtree by composition — no counting
lemma for a restricted layout was needed.

## §6 Proposed text, not applied

### §6.1 Section 3, after the master table (one paragraph)

> **Two containers in Garey & Johnson's list.** The 1979 list has no member of the
> complex, but two entries contain it. SS7, *sequencing to minimise maximum cumulative
> cost* (Abdel-Wahab 1976): an opening task at cost `+1` and a closing task at `−1` per
> customer, a task at cost `0` per pattern, `open ≺ pattern ≺ close` and `open ≺ close`,
> and the least maximum prefix sum over linear extensions is the number of open stacks
> (`ss7Value_toSS7`), with costs in the `{−1, 0, 1}` restriction the list records as
> NP-complete — so the list carries open stacks without naming them. SS7 itself has no
> derived graph: its value is not determined by the comparability graph and the costs
> (two tasks suffice), and no graph read off pairs of tasks, or off bounded neighbourhoods
> in the Hasse diagram, is within a constant of it (`no_local_derived_graph`). PO1,
> *register sufficiency* (Sethi 1975), is the one-shot black pebble game with the outputs
> retained; it equals pathwidth with a precedence constraint on the layout — one plus the
> least, over topological orderings, of the largest number of placed vertices still
> waiting for a successor (`pbR_eq_topologicalDemand`) — and exceeds `pw(G_u) + 1` of
> row 13 without bound: on the complete binary out-tree of height `h` it is `h + 1`
> against `⌈h/2⌉ + 1` (`exists_gap_binaryOutTree`). The complex reaches it only through
> the best orientation (Kirousis & Papadimitriou, Theorem 3.1).

### §6.2 Related work (one sentence)

> Garey & Johnson's list of 1979 contains the open-stacks problem as the `{−1, 0, 1}`
> case of SS7 and the one-shot pebble game as PO1, both without a graph; the pathwidth
> vocabulary for either came later (Lengauer 1981; Kirousis & Papadimitriou 1986; Fellows
> & Langston 1989).

### §6.3 `paper1/equivalences.md`

The three rows of §2.5, with a status label **container** added to the five of the master
table's legend: *the problem contains a member as a special case and has no derived graph
of its own (proved)*.

## §7 Regenerate

```
cd /home/al/dev/MOSP
python reports/scratch/ss7_register_sufficiency/ss7_embed_exhaustive.py   # 673 matrices, edge cases     (~10 s)
python reports/scratch/ss7_register_sufficiency/ss7_witnesses.py          # §2 witnesses, N-free check    (~10 s)
python reports/scratch/ss7_register_sufficiency/pb_formula_check.py       # 33,867 dags + 2,000 at 9      (~1 min)
python reports/scratch/ss7_register_sufficiency/binary_tree_gap.py        # the table of §3.3, recursion  (~5 s; C program)
python reports/scratch/ss7_register_sufficiency/pb_vs_pwgu.py             # §3.5 probe                    (~2 min)
python -m pytest tests/test_ss7_register.py -q                             # 16 tests
cd lean && taskset -c 0-3 nice -n 19 lake build                            # the seven files; logs in reports/scratch/ss7_register_sufficiency/*_build.log
```

Axiom audits: `reports/scratch/ss7_register_sufficiency/*_axioms.log` (one line per theorem).
