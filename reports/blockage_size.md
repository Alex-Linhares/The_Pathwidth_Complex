# The size of a blockage: the minimum number of minimal big sets, measured

*2026-11-07, one session. Code `learning/blockage_size.py`, tests
`tests/test_blockage_size.py`, scratch `reports/scratch/blockage_size/`. Nothing
under `solutions/` touched; nothing re-solved from the corpus; pathwidths by the
bitmask subset DP (≤ 18 vertices), treewidths by `learning.treewidth`'s C DP; the
blockage minima by pysat's CaDiCaL (untimed) and Glucose 4 (timed), nice 19, at
most 8 workers.*

## §0. Summary

(filled in below once the runs are in; see §4)

## §1. The measure, decided before measuring

### 1.1 What is fixed by a blockage

Fix a graph on `N` vertices and an order `k`. Write `Sm = {X ⊆ V : |att X| ≤ k}`.
Axiom (i) says `B ⊆ Sm`; axiom (ii) says the *non-members inside `Sm`*,
`U = Sm \ B`, form an up-set of the poset `(Sm, ⊆)`. So `B` is determined by the
⊆-minimal elements of `U`, which we call the **frame** of `B`. `BlockageClass.lean`
says the same thing with an upward-closed predicate `big` on all of `2^V`:
`B = {X ∈ Sm : ¬ big X}`. Two different predicates can give the same `B` (they may
differ off `Sm`), so "the minimal big sets" is ambiguous until `big` is fixed. The
canonical choice is the up-closure of `U` itself, whose minimal elements are the
frame. The brief's alternative — the up-set of *all* non-members, including the
sets with `|att| > k` — is not upward closed (a set with large attachment can sit
below a member) and its minimal elements are the large-attachment sets near the
bottom of the lattice, which say nothing about `B`; it is not a measure of the
blockage and is dropped.

### 1.2 Three sizes

For a blockage `B` of order `k`:

* **size₁(B) = |frame(B)|**, the number of ⊆-minimal elements of `Sm \ B`. It is
  determined by `B`; the frame regenerates `B` as `{X ∈ Sm : no frame set ⊆ X}`.
* **size₂(B)** = the least `r` such that some sets `g₁, …, g_r ⊆ V` (any sets,
  small attachment or not) satisfy `Sm \ B = {X ∈ Sm : some g_i ⊆ X}` — the
  shortest *generator list* for `B`. `size₂ ≤ size₁` (the frame is such a list),
  and the inequality can be strict: a generator with large attachment can sit
  below two frame sets at once (Petersen at order 5: 8 against 15; the cube `Q₃`
  at order 4: 6 against 12). A generator can never be a small-attachment set other
  than a frame set, so every saving comes from large-attachment sets.
* **size₃(B)** = the number of ⊆-maximal members of `B`. Also determined by `B`,
  also regenerating it (`B = {X ∈ Sm : X ⊆ some maximal member}`), the dual
  description.

A fourth candidate — the number of separations of order `≤ k` oriented
(Diestel–Oum's form: a blockage *is* a consistent orientation of all of them) — is
the size of the whole set of small separations, polynomially related to `|Sm|`,
never compact, and is what the generator descriptions are meant to compress. It is
reported only as `|Sm|` beside each number.

### 1.3 Why size₂ (and size₁) is a certificate length, and what checking costs

The certificate for `pw ≥ k` is a generator list `g₁, …, g_r` (for the canonical
certificate, the frame). The verifier forms `B = {X ∈ Sm : no g_i ⊆ X}`; (i) and
(ii) hold by construction, and the whole content is (iii): *every separation
`(X₁, X₂)` of order `≤ k` has exactly one side containing some `g_i`.* That splits
into

* (b) **no separation of order `≤ k` has `g_i ⊆ X₁` and `g_j ⊆ X₂`** — one Menger
  computation per pair `(i, j)` (a vertex cut of size `≤ k` between `g_i` and `g_j`,
  common vertices counted in the cut), polynomial in `r² · poly(N)`;
* (a) **no separation of order `≤ k` splits every generator** (every `g_i` has a
  vertex strictly on each side). The complement of (a) is in NP (guess the
  separation); checking (a) from the generators is a search over the choices of a
  "left" and a "right" vertex in each generator followed by a flow computation —
  `N^{2r} · poly(N)` — polynomial for bounded `r`, not polynomial in `r × poly(N)`.
  For connected generators (a) reduces to a hitting-set statement (a connected set
  split by a separation meets the separator), but the minimal big sets of the
  branch operator, of the cube and of Petersen are disconnected.

So `r` is the *length* of the certificate, and the verifier is polynomial when `r`
is bounded; it is not polynomial in `r` and `N` jointly, which is as it must be —
`pw ≥ k` is coNP-complete (`reports/pathwidth_np_conp.md`), so a polynomial-size
*and* polynomial-time-checkable blockage on every graph would give NP = coNP. The
measurement below asks only the size question. Grohe & Marx's bramble statement has
the same shape: the bramble's number of sets is the size, and its order is NP-hard
to check given the bramble.

One more thing the frame measure does *not* capture: the minor-pullback blockages
of `reports/blockage_class.md` are described by their branch sets (`≤ N` vertices
in all) while their frames are the transversals of the branch sets, a product of
the branch-set sizes. So size₁ and size₂ measure certificates in the *generator
language*; a blockage can have a short description in another language and a long
frame. The conjecture under test is about the generator language (the pathwidth
analogue of a bramble's set count), which is what is measured.

### 1.4 What is measured

For a graph and an order `k`, **`min size_i(B)` over every blockage `B` of order
`k`**, for `i = 1` everywhere, `i = 2` and `i = 3` to 14 and 12 vertices (the
generator model has `3^N` clauses). The minimisers of the three sizes need not be
the same blockage. "Exact" means the SAT model proved `≤ s − 1` unsatisfiable and
exhibited a blockage of size `s`, which the all-pairs axiom checker of
`learning.blockage_class` (no clause in common with the model) re-verified at
`≤ 12` vertices; "bounded" means a blockage of size `ub` was found and `≤ lb − 1`
was refuted before the time limit, with `lb < ub`.

### 1.5 The model, and the brute-force check

Variables `b_X` for `X ∈ Sm`; auxiliaries `e_Z` ("every `Sm`-subset of `Z` is a
member") over all `Z ⊆ V`; indicators `m_X` ("`X` is a minimal non-member").
Constraints: (ii) through `e`; the **step closure** `X ∈ B, v ∉ X, |att X| < k ⇒
X ∪ {v} ∈ B` (BRST Lemma (2.2) for one vertex; multi-vertex steps compose, since
`att(X ∪ {v}) ⊆ att X ∪ {v}`); and the **minimal pairs** `b_X xor b_{X^c}`,
`X^c = (V \ X) ∪ att X`. These imply (iii) for every pair: both sides in `B` is
excluded because `X₁^c ⊆ X₂` would be a member against the minimal pair; neither
side is excluded because `X₂^c ∈ B` and `(X₁ \ X₂^c) ∪ att(X₂^c) ⊆ X₁ ∩ X₂` lets
the step closure climb from `X₂^c` to `X₁`. (The minimal pairs alone are a strict
relaxation: on `P₄` at order 2 they admit a family that violates (iii) on the pair
`({a,b,c}, {b,c,d})`; the step closure is what closes it.) The model has
`|Sm| + 2^N` principal variables and about `4 N 2^N` clauses, and the minimum of
`Σ m_X` is found by binary search on a totalizer.

Checked (`tests/test_blockage_size.py`): against an enumeration of **every family
of subsets** on every graph of the atlas with ≤ 4 vertices, every order 1..N
(`2^16` families per graph and order), and against an enumeration of **every up-set
of `2^V`** (Dedekind's 7,581) on every graph on 5 vertices, every order 1..5: the
minima agree in every case, including "no blockage". On every connected graph to 6
vertices: a blockage exists iff `pw ≥ k`; every minimiser of each of the three
sizes passes the all-pairs axiom checker; the frame recomputed from the family has
the size the model reports; `size₂ ≤ size₁`; the generators found regenerate the
blockage.

### 1.6 Kill criteria, stated before the family run

The conjecture to probe has two halves. In this measure, at the sizes reachable:

* **K-hard** (the "exponential near `pw` on expanders" half is *unsupported*): if
  on every expander-like family with at least three sizes (random cubic 8–18,
  random quartic 10–16, the named cubic/quartic/quintic graphs) the exact
  `min size₁` at order `pw` is `≤ N²` at every size and grows from the smallest
  to the largest size by no more than `(N_max / N_min)²`, the data show nothing
  faster than a quadratic and the half has no support. The criterion is **met** in
  that case; it is **not met** if some family's values exceed `N²` or grow faster
  than that.
* **K-easy** (the "polynomial at order a positive power of `pw`" half): at orders
  `≤ ⌈√pw⌉` the minimum is `≤ N` on every graph tried; a graph needing `> N²` at
  such an order contradicts the half. At `pw ≤ 9` these orders are 1–3 and the
  test is weak; it is reported as such.

Disclosure: the model was developed on Petersen, `K_{5,5}`, the 3×3 and 4×4 grids
and one random cubic graph at 12, 14 and 16 vertices (seed 0), so those six numbers
were seen before the criteria were written; the criteria were fixed before any
other family graph was run.
