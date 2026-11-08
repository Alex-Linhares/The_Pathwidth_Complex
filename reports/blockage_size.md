# The size of a blockage: the minimum number of minimal big sets, measured

*2026-11-07, one session. Code `learning/blockage_size.py`, tests
`tests/test_blockage_size.py`, scratch `reports/scratch/blockage_size/`. Nothing
under `solutions/` touched; nothing re-solved from the corpus; pathwidths by the
bitmask subset DP (≤ 18 vertices), treewidths by `learning.treewidth`'s C DP; the
blockage minima by pysat's CaDiCaL (untimed) and Glucose 4 (timed), nice 19, at
most 8 workers.*

## §0. Summary

**The question.** Pathwidth's exact dual is the blockage of Bienstock,
Robertson, Seymour & Thomas (1991). The owner asked, before any theorem is
attempted, for the shape of one quantity: the *size* of the smallest blockage of
each order on small graphs and on expander-like families — the pathwidth
analogue of Grohe & Marx's bramble-size question (brambles of order near the
treewidth are exponentially large on expanders; polynomial brambles of order
`Ω̃(√tw)` always exist).

**The measure (§1).** A blockage `B` of order `k` is a down-set of the sets with
at most `k` attachments; it is determined by the ⊆-minimal non-members among
them, its **frame**. Three sizes: size₁ = the number of frame sets (the
"minimal big sets" of the brief, with `big` the up-closure of the small-attachment
non-members — the only reading that is upward closed and determined by `B`);
size₂ = the shortest list of *arbitrary* generators `g_i` with
`B = {X : |att X| ≤ k, no g_i ⊆ X}`; size₃ = the number of maximal members.
A generator list is a certificate of `pw ≥ k`: the verifier checks that every
separation of order `≤ k` has exactly one side containing a generator — the
"not both" half is a Menger computation per pair (polynomial in `r² · poly(n)`),
the "at least one" half is a search over separations (`n^{2r} · poly(n)`,
polynomial for bounded `r`, not in `r × poly(n)`). So `r` is a certificate
*length*, with a verifier that is polynomial only for bounded length, which is
as it must be since `pw ≥ k` is coNP-complete. Both size₁ and size₂ were
measured; size₃ is never the shorter one (`≥ size₁` on every graph and order)
and was dropped. Measured: **`min size(B)` over every blockage of order `k`**,
by an exact SAT model (memberships of the small-attachment sets; down-closure,
single-vertex step closure, the minimal pairs `X xor X^c`; proved equivalent to
axioms (i)–(iii) in §1.5), minimised by binary search on a totalizer, and
checked against an enumeration of every family of subsets to 4 vertices and
every up-set of `2^V` to 5 vertices, and against the independent all-pairs
axiom checker to 12 vertices.

**Exhaustive to 9 vertices (§2).** All 273,193 connected graphs, every order
`1..pw`, all three sizes, 3.6 h on 8 workers. At order `pw` the minimum is 1 on
28.5%, `≤ 2` on 78.9% and `≤ 3` on 96.2% of the 261,080 graphs on 9 vertices;
its maximum is 12 at 8 vertices (the cube) and 13 at 9 — about `1.5 n`. Its
mean grows slowly (1.36, 1.49, 1.71, 1.97 at 6–9 vertices). The large frames
are **co-pair frames** (`V` minus a pair). size₂ is shorter than size₁ on a
quarter of the graphs, by a factor up to 4. **Every graph with `pw > tw` needs
at least 3 minimal big sets at order `pw`** (13,548 of 13,548; one set is a
theorem by the sink of an oriented tree decomposition, two is open).

**Families to 22 vertices (§3).**

| graph | n | pw | tw | min size₁ at pw | at pw−1 | at pw−2 | size₂ at pw |
|:--|--:|--:|--:|--:|--:|--:|--:|
| `K_{k,k}`, k = 2..8 | 2k | k | k | **2** | 1 | 1 | 2 |
| grids 3×3, 4×4 | 9, 16 | 3, 4 | 3, 4 | **4**, **3** | 1, 2 | 1, 1 | 3 |
| trees (spider, ternary h2, binary h3) | 7, 13, 15 | 2 | 1 | **3** | 1 | — | 3 |
| the 10-vertex `pw − tw = 2` graph | 10 | 5 | 3 | **3** | 3 | 1 | 3 |
| random cubic, pw 3 / 4 / 5 / 6 | 8–22 | 3–6 | 3–5 | **2** / **3–5** / **4–8** / **9** | 1 / 2 / 3 / 4 | 1 / 1 / 2 / 3 | 2–4 |
| random quartic, quintic | 10–16 | 4–7 | 4–7 | **2–7** | 1–4 | 1–2 | 2–4 |
| Mycielski `M₄` | 11 | 5 | 5 | **6** | 3 | 1 | 5 |
| Petersen | 10 | 5 | 4 | **15** | 5 | 2 | 8 |
| Paley 13 | 13 | 8 | 8 | **15** | 13 | 3 | 9 |
| Heawood | 14 | 6 | 5 | [25, 32] | 6 | 3 | — |
| Möbius–Kantor | 16 | 6 | 5 | [16, 22] | 6 | 3 | — |
| `Q₄` | 16 | 7 | 6 | **26** | 7 | 16 | — |
| Shrikhande | 16 | 9 | 9 | **22** | 9 | 16 | — |
| Clebsch | 16 | 9 | 8 | **32** | 10 | 16 | — |

Bold exact; brackets `[lb, ub]` where the 2-hour CaDiCaL cap killed the run
(sizes `< lb` refuted, `ub` constructed). Random cubic graphs reach `pw 6` only
at 22 vertices, where the model has 4.2 M principal variables and the order-6
minimum took 57 min.

**Verdict (§4).** The kill criteria stated in §1.6 are **met**: no family's
minimum at order `pw` exceeds `n²` or grows faster than quadratically in `n`
(random cubic: 2 at 8 vertices to 8 at 22, against an allowed 7.6×), the record
is Clebsch at `2 n`, and at orders `≤ ⌈√pw⌉` the minimum is `≤ 3` everywhere.
**Every graph tried has a blockage of order `pw` with at most `2 n` minimal
big sets** — Clebsch 32 of 16 is the largest ratio (exact), Heawood is
`≥ 1.8 n` and `≤ 2.3 n` (bracketed), `Q₄` 26 of 16 — so the "exponential on
expanders" half has no support in this measure at these sizes. The shape that *is* visible: the minimum is a
function of the **order**, flat in `n` at fixed `pw` on random regular graphs
and growing ×1.5–2 per unit of `pw` (2, 3–5, 4–8, 5–9, 7 at `pw = 3..7`);
on the vertex-transitive graphs it is 1–3 up to about the treewidth and jumps
in the last two orders (Petersen 2, 5, 15; Clebsch 16, 10, 32). The large
frames are co-small sets `V \ S`, `|S| = 2..4`, one per local configuration.
`size ≈ c · 2^{pw}` and `size ≈ 2 n` both fit every exact number; with `pw ≤ 9`
they cannot be separated. If the first is the law and `pw = Θ(n)` on
expanders, the conjecture's hard half follows — the data show the first factor
to `pw = 9` and cannot see the second. The measure is well-posed, not
canonical: size₂ is a constant factor below size₁, and the minor-pullback
language of `reports/blockage_class.md` is shorter still for clique-minor
blockages; any theorem has to name its language.

**Regenerate:** `python3 -m learning.blockage_size --stage census --max-n 9
--alt-max-n 9 --workers 8`; `--stage named --workers 7 --time-limit 600`;
`--stage big --ns 20 --seeds 0,1`; `--stage big --ns 22 --seeds 0,1,2
--time-limit 1800 --out reports/scratch/blockage_size/big_d3_22.csv`;
`--stage one --only Heawood --order 6 --time-limit 0` (and Möbius–Kantor,
`Q₄`, Paley13 `--kind generators`); `--stage report`;
`python3 -m pytest tests/test_blockage_size.py -q` (8 tests, 13 s).

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

## §2. Exhaustive: every connected graph to 9 vertices

`nice -n 19 python3 -m learning.blockage_size --stage census --max-n 9 --alt-max-n 9 --workers 8`
(3.6 h on 8 workers, almost all of it the 261,080 graphs at 9 vertices;
`reports/scratch/blockage_size/census_n{1..9}.csv`, the 9-vertex file gzipped;
`--stage report` prints the tables). For each of the 273,193 connected graphs
on 1–9 vertices: `pw` (subset DP), `tw` (C DP), and at every order `1..pw` the
exact minimum of size₁, size₂ and size₃ over all blockages of that order, each
minimiser re-verified against the all-pairs axiom checker at ≤ 7 vertices and
the absence of a blockage of order `pw + 1` confirmed on every graph (the
duality, both halves, on all 273,193).

| n | graphs | pw range | max min-size₁ at order pw | mean | share = 1 | max min-size₁ at pw−1 | max size₁ any order | graphs with min-size₁ > n |
|--:|--:|:--|--:|--:|--:|--:|--:|--:|
| 1 | 1 | 0–0 | 0 | 0.00 | 0.000 | 0 | 0 | 0 |
| 2 | 1 | 1–1 | 1 | 1.00 | 1.000 | 0 | 1 | 0 |
| 3 | 2 | 1–2 | 1 | 1.00 | 1.000 | 1 | 1 | 0 |
| 4 | 6 | 1–3 | 2 | 1.17 | 0.833 | 1 | 2 | 0 |
| 5 | 21 | 1–4 | 2 | 1.19 | 0.810 | 1 | 2 | 0 |
| 6 | 112 | 1–5 | 3 | 1.36 | 0.670 | 2 | 3 | 0 |
| 7 | 853 | 1–6 | 4 | 1.49 | 0.564 | 3 | 4 | 0 |
| 8 | 11117 | 1–7 | 12 | 1.71 | 0.423 | 3 | 12 | 2 |
| 9 | 261080 | 1–8 | 13 | 1.97 | 0.285 | 4 | 13 | 16 |

| n | graphs with size₂, size₃ | size₂ = size₁ at every order | size₂ < size₁ | size₃ = size₁ | size₃ < size₁ | size₃ > size₁ | max size₂ at pw | max size₃ at pw |
|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| 2 | 1 | 1 | 0 | 0 | 0 | 1 | 1 | 2 |
| 3 | 2 | 2 | 0 | 0 | 0 | 2 | 1 | 3 |
| 4 | 6 | 6 | 0 | 0 | 0 | 6 | 2 | 4 |
| 5 | 21 | 21 | 0 | 0 | 0 | 21 | 2 | 7 |
| 6 | 112 | 107 | 5 | 0 | 0 | 112 | 3 | 11 |
| 7 | 853 | 782 | 71 | 0 | 0 | 853 | 4 | 21 |
| 8 | 11117 | 9417 | 1700 | 0 | 0 | 11117 | 6 | 37 |
| 9 | 261080 | 196705 | 64375 | 0 | 0 | 261080 | 7 | 81 |

| graph6 | n | m | pw | tw | min size₁ by order 1..pw |
|:--|--:|--:|--:|--:|:--|
| `HCrbbqi` | 9 | 17 | 5 | 5 | [1, 1, 1, 2, 13] |
| `G?zTb_` | 8 | 12 | 4 | 3 | [1, 1, 2, 12] |
| `H?zTbb{` | 9 | 18 | 5 | 4 | [1, 1, 1, 2, 12] |
| `H?zTbbm` | 9 | 18 | 5 | 4 | [1, 1, 2, 2, 12] |
| `H?zTb`}` | 9 | 18 | 5 | 4 | [1, 1, 1, 2, 12] |
| `H?zTbb}` | 9 | 19 | 5 | 4 | [1, 1, 1, 2, 12] |
| `H?zTbb~` | 9 | 20 | 5 | 4 | [1, 1, 1, 2, 12] |
| `H?zTba{` | 9 | 17 | 5 | 4 | [1, 1, 1, 2, 11] |
| `H?zTf_{` | 9 | 17 | 5 | 4 | [1, 1, 1, 2, 11] |
| `HCrb`ry` | 9 | 18 | 5 | 5 | [1, 1, 1, 2, 11] |
| `HCZbeqw` | 9 | 17 | 5 | 4 | [1, 1, 1, 3, 11] |
| `GCrb`o` | 8 | 12 | 4 | 4 | [1, 1, 2, 10] |

| n | pw − tw | graphs | mean min-size₁ at pw | max |
|--:|--:|--:|--:|--:|
| 1 | 0 | 1 | 0.00 | 0 |
| 2 | 0 | 1 | 1.00 | 1 |
| 3 | 0 | 2 | 1.00 | 1 |
| 4 | 0 | 6 | 1.17 | 2 |
| 5 | 0 | 21 | 1.19 | 2 |
| 6 | 0 | 111 | 1.34 | 3 |
| 6 | 1 | 1 | 3.00 | 3 |
| 7 | 0 | 839 | 1.47 | 3 |
| 7 | 1 | 14 | 3.07 | 4 |
| 8 | 0 | 10777 | 1.66 | 10 |
| 8 | 1 | 340 | 3.30 | 12 |
| 9 | 0 | 247887 | 1.89 | 13 |
| 9 | 1 | 13193 | 3.51 | 12 |

**What the census says.**

* **The minimum at order `pw` is small, and its maximum grows like `1.5 n`, not
  faster, to 9 vertices**: 12 at 8 vertices (the cube `Q₃`, `pw 4`, `tw 3`), 13 at
  9 (`HCrbbqi`, 4-regular but for two vertices, `pw = tw = 5`). At 9 vertices
  78.9% of graphs have a blockage of order `pw` with at most 2 minimal big sets,
  96.2% with at most 3, and 16 of 261,080 need more than 9. The mean at order
  `pw` rises slowly with `n` (1.36, 1.49, 1.71, 1.97 at 6, 7, 8, 9).
* **The large frames are co-pair frames.** On the cube every one of the 12
  minimal big sets is `V` minus a pair (`V \ {u, v}`); on the two 9-vertex
  record graphs likewise (13 and 9 pairs, edges and non-edges mixed). These are
  the co-singleton frames of `reports/blockage_class.md` §4 one level up: the
  blockage says "every separation of order ≤ `pw` leaves one side with at most a
  pair outside it".
* **size₂ is shorter than the frame on a quarter of the graphs, by a factor up
  to 4.** `size₂ < size₁` at some order on 64,375 of 261,080 graphs at 9
  vertices (24.7%; 15.3% at 8). The largest `min size₂` at order `pw` is 7
  against 13 for size₁; the cube's 12 co-pairs are 6 generators of 5 vertices,
  and the 4-regular `HCrfbo{` (`pw 5`) needs 9 frame sets but 3 generators —
  three 6-sets with attachment 6, pairwise meeting in 3 vertices, whose
  complements partition `V` into three triples. The saving always comes from
  generators with attachment `> k`, which are never members and never frame sets.
* **size₃ is never the short description**: the number of maximal members is
  `≥ size₁` on every graph and order (`size₃ > size₁` somewhere on every one of
  the 273,193 graphs), up to 81 at 9 vertices. It is dropped from here on.
* **Every graph with `pw > tw` needs at least 3 minimal big sets at order `pw`**
  — on all 13,548 such graphs to 9 vertices (1 + 14 + 340 + 13,193), against
  1.8–16.9% of the `pw = tw` graphs. For one generator this is a theorem: a
  blockage of order `k` whose frame is a single set `F` says that every
  separation of order `≤ k` has exactly one side containing `F`; orienting the
  edges of a tree decomposition of width `< k` towards that side gives a sink
  whose bag contains `F` (the sides at the sink intersect in the bag), so
  `|bag| ≥ k + 1`, `tw ≥ k`. For two generators the same orientation is still
  well-defined (axiom (b) forbids the two generators on opposite sides) but the
  sink bag need not contain either; the data say two never suffice where
  `pw > tw`, and we have no proof. Three is the branch lemma's count (two of
  three branches big: three minimal sets).
* **The frame is concentrated at the top order.** `min size₁` at order `pw − 1`
  is at most 4 on every graph to 9 vertices and `≥ 3` on only 1,274 of 265,693
  graphs with `pw ≥ 3`; the ratio `size₁(pw) / size₁(pw − 1)` is 1 on 33.8% of
  them and up to 6.5. The minimum is not monotone in the order on 1.7% of the
  graphs (e.g. `F~_Q?`: 1, 3, 1 at orders 1, 2, 3), while `min size₂` is
  non-decreasing in the order on every graph.

## §3. Structured families and expander-like graphs

`nice -n 19 python3 -m learning.blockage_size --stage named --workers 7 --time-limit 600`
(68 graphs, 281 rows, 32 min on 7 workers; `reports/scratch/blockage_size/named.csv`);
`--stage big --ns 20 --seeds 0,1` and `--ns 22 --seeds 0,1,2 --time-limit 1800`
(`big_d3.csv`, `big_d3_22.csv`; the 22-vertex model has 4.2 M principal
variables and takes 1–5 min per solve); the four minima the 10-minute Glucose
runs left bracketed were re-run untimed on CaDiCaL under a 2-hour cap
(`--stage one --time-limit 0`, logs under `scratch/blockage_size/long/`; two
closed — `Q₄` 26, `cubic22_s0` 9 — and two were killed by the cap, Heawood at
`[25, 32]` and Möbius–Kantor at `[16, 22]`; the CSVs carry the long-run values).
Pathwidths by the subset DP to 18 vertices and by `pathwidth_solver/cli/pathwidth`
(status `refutation`) above; every minimiser at ≤ 12 vertices re-checked against
the all-pairs axiom checker; size₂ to 14 vertices, size₃ to 12.

### 3.1 The table: minimum size₁ at orders `pw`, `pw − 1`, `pw − 2`, `pw − 3`

Bold is exact (a blockage of that size exists and one smaller was refuted);
brackets `[lb, ub]` mean a blockage of size `ub` was found and sizes `< lb`
refuted when the budget ran out. size₂ is the shortest generator list at order `pw`.

| graph | n | m | pw | tw | pw | pw−1 | pw−2 | pw−3 | size₂ at pw | size₁(pw)/n |
|:--|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| K3 | 3 | 3 | 2 | 2 | **1** | **1** |  |  | 1 | 0.33 |
| P3 | 3 | 2 | 1 | 1 | **1** |  |  |  | 1 | 0.33 |
| C4 | 4 | 4 | 2 | 2 | **2** | **1** |  |  | 2 | 0.50 |
| K2,2 | 4 | 4 | 2 | 2 | **2** | **1** |  |  | 2 | 0.50 |
| K4 | 4 | 6 | 3 | 3 | **1** | **1** | **1** |  | 1 | 0.25 |
| C5 | 5 | 5 | 2 | 2 | **2** | **1** |  |  | 2 | 0.40 |
| K5 | 5 | 10 | 4 | 4 | **1** | **1** | **1** | **1** | 1 | 0.20 |
| Mycielski3 | 5 | 5 | 2 | 2 | **2** | **1** |  |  | 2 | 0.40 |
| C6 | 6 | 6 | 2 | 2 | **2** | **1** |  |  | 2 | 0.33 |
| K3,3 | 6 | 9 | 3 | 3 | **2** | **1** | **1** |  | 2 | 0.33 |
| K6 | 6 | 15 | 5 | 5 | **1** | **1** | **1** | **1** | 1 | 0.17 |
| grid2x3 | 6 | 7 | 2 | 2 | **2** | **1** |  |  | 2 | 0.33 |
| K7 | 7 | 21 | 6 | 6 | **1** | **1** | **1** | **1** | 1 | 0.14 |
| bintree_h2 | 7 | 6 | 1 | 1 | **1** |  |  |  | 1 | 0.14 |
| spider3x2 | 7 | 6 | 2 | 1 | **3** | **1** |  |  | 3 | 0.43 |
| C8 | 8 | 8 | 2 | 2 | **2** | **1** |  |  | 2 | 0.25 |
| K4,4 | 8 | 16 | 4 | 4 | **2** | **1** | **1** | **1** | 2 | 0.25 |
| K8 | 8 | 28 | 7 | 7 | **1** | **1** | **1** | **1** | 1 | 0.12 |
| cubic8_s0 | 8 | 12 | 3 | 3 | **2** | **1** | **1** |  | 2 | 0.25 |
| cubic8_s1 | 8 | 12 | 3 | 3 | **2** | **1** | **1** |  | 2 | 0.25 |
| cubic8_s2 | 8 | 12 | 3 | 3 | **2** | **1** | **1** |  | 2 | 0.25 |
| grid2x4 | 8 | 10 | 2 | 2 | **2** | **1** |  |  | 2 | 0.25 |
| grid3x3 | 9 | 12 | 3 | 3 | **4** | **1** | **1** |  | 3 | 0.44 |
| C10 | 10 | 10 | 2 | 2 | **2** | **1** |  |  | 2 | 0.20 |
| K5,5 | 10 | 25 | 5 | 5 | **2** | **1** | **1** | **1** | 2 | 0.20 |
| Petersen | 10 | 15 | 5 | 4 | **15** | **5** | **2** | **1** | 8 | 1.50 |
| cubic10_s0 | 10 | 15 | 3 | 3 | **2** | **1** | **1** |  | 2 | 0.20 |
| cubic10_s1 | 10 | 15 | 3 | 3 | **2** | **1** | **1** |  | 2 | 0.20 |
| cubic10_s2 | 10 | 15 | 4 | 4 | **5** | **2** | **1** | **1** | 4 | 0.50 |
| grid2x5 | 10 | 13 | 2 | 2 | **2** | **1** |  |  | 2 | 0.20 |
| pwtw2_10 | 10 | 21 | 5 | 3 | **3** | **3** | **1** | **1** | 3 | 0.30 |
| quartic10_s0 | 10 | 20 | 4 | 4 | **2** | **1** | **1** | **1** | 2 | 0.20 |
| quartic10_s1 | 10 | 20 | 5 | 5 | **7** | **2** | **1** | **1** | 3 | 0.70 |
| Mycielski4 | 11 | 20 | 5 | 5 | **6** | **3** | **1** | **1** | 5 | 0.55 |
| K6,6 | 12 | 36 | 6 | 6 | **2** | **1** | **1** | **1** | 2 | 0.17 |
| cubic12_s0 | 12 | 18 | 4 | 4 | **3** | **2** | **1** | **1** | 3 | 0.25 |
| cubic12_s1 | 12 | 18 | 3 | 3 | **2** | **1** | **1** |  | 2 | 0.17 |
| cubic12_s2 | 12 | 18 | 3 | 3 | **2** | **1** | **1** |  | 2 | 0.17 |
| grid3x4 | 12 | 17 | 3 | 3 | **2** | **1** | **1** |  | 2 | 0.17 |
| quartic12_s0 | 12 | 24 | 5 | 5 | **4** | **2** | **1** | **1** | 3 | 0.33 |
| quartic12_s1 | 12 | 24 | 5 | 5 | **5** | **2** | **1** | **1** | 4 | 0.42 |
| quintic12_s0 | 12 | 30 | 6 | 6 | **5** | **2** | **1** | **1** | 3 | 0.42 |
| Paley13 | 13 | 39 | 8 | 8 | **15** | **13** | **3** | **1** | [8, 10] | 1.15 |
| tertree_h2 | 13 | 12 | 2 | 1 | **3** | **1** |  |  | 3 | 0.23 |
| Heawood | 14 | 21 | 6 | 5 | [25, 32] | **6** | **3** | **2** | [1, 60] |  |
| K7,7 | 14 | 49 | 7 | 7 | **2** | **1** | **1** | **1** | 2 | 0.14 |
| cubic14_s0 | 14 | 21 | 4 | 4 | **3** | **2** | **1** | **1** | 3 | 0.21 |
| cubic14_s1 | 14 | 21 | 4 | 4 | **3** | **2** | **1** | **1** | 3 | 0.21 |
| cubic14_s2 | 14 | 21 | 4 | 3 | **5** | **2** | **1** | **1** | 3 | 0.36 |
| quartic14_s0 | 14 | 28 | 5 | 5 | **4** | **2** | **1** | **1** | 2 | 0.29 |
| quartic14_s1 | 14 | 28 | 5 | 5 | **4** | **2** | **1** | **1** | 3 | 0.29 |
| bintree_h3 | 15 | 14 | 2 | 1 | **3** | **1** |  |  |  | 0.20 |
| Clebsch | 16 | 40 | 9 | 8 | **32** | **10** | **16** | **16** |  | 2.00 |
| K8,8 | 16 | 64 | 8 | 8 | **2** | **1** | **1** | **1** |  | 0.12 |
| MoebiusKantor | 16 | 24 | 6 | 5 | [16, 22] | **6** | **3** | **2** |  |  |
| Q4 | 16 | 32 | 7 | 6 | **26** | **7** | **16** | **2** |  | 1.62 |
| Shrikhande | 16 | 48 | 9 | 9 | **22** | **9** | **16** | **3** |  | 1.38 |
| cubic16_s0 | 16 | 24 | 4 | 4 | **3** | **2** | **1** | **1** |  | 0.19 |
| cubic16_s1 | 16 | 24 | 4 | 4 | **5** | **2** | **1** | **1** |  | 0.31 |
| cubic16_s2 | 16 | 24 | 5 | 4 | **8** | **3** | **2** | **1** |  | 0.50 |
| grid2x8 | 16 | 22 | 2 | 2 | **2** | **1** |  |  |  | 0.12 |
| grid4x4 | 16 | 24 | 4 | 4 | **3** | **2** | **1** | **1** |  | 0.19 |
| quartic16_s0 | 16 | 32 | 5 | 5 | **4** | **2** | **1** | **1** |  | 0.25 |
| quartic16_s1 | 16 | 32 | 6 | 6 | **5** | **4** | **2** | **1** |  | 0.31 |
| quintic16_s0 | 16 | 40 | 7 | 7 | **7** | **4** | **2** | **1** |  | 0.44 |
| cubic18_s0 | 18 | 27 | 5 | 4 | **5** | **3** | **2** | **1** |  | 0.28 |
| cubic18_s1 | 18 | 27 | 5 | 5 | **5** | **3** | **2** | **1** |  | 0.28 |
| cubic18_s2 | 18 | 27 | 4 | 4 | **3** | **2** | **1** | **1** |  | 0.17 |

Random regular graphs, grouped by degree and by the order `pw` (the 22-vertex
rows from `--stage big`):

| degree | graph | n | pw | tw | min size₁ at order pw | at pw−1 | size₂ at pw |
|--:|:--|--:|--:|--:|--:|--:|--:|
| 3 | cubic8_s0 | 8 | 3 | 3 | **2** | **1** | 2 |
| 3 | cubic8_s1 | 8 | 3 | 3 | **2** | **1** | 2 |
| 3 | cubic8_s2 | 8 | 3 | 3 | **2** | **1** | 2 |
| 3 | cubic10_s0 | 10 | 3 | 3 | **2** | **1** | 2 |
| 3 | cubic10_s1 | 10 | 3 | 3 | **2** | **1** | 2 |
| 3 | cubic10_s2 | 10 | 4 | 4 | **5** | **2** | 4 |
| 3 | cubic12_s1 | 12 | 3 | 3 | **2** | **1** | 2 |
| 3 | cubic12_s2 | 12 | 3 | 3 | **2** | **1** | 2 |
| 3 | cubic12_s0 | 12 | 4 | 4 | **3** | **2** | 3 |
| 3 | cubic14_s0 | 14 | 4 | 4 | **3** | **2** | 3 |
| 3 | cubic14_s1 | 14 | 4 | 4 | **3** | **2** | 3 |
| 3 | cubic14_s2 | 14 | 4 | 3 | **5** | **2** | 3 |
| 3 | cubic16_s0 | 16 | 4 | 4 | **3** | **2** |  |
| 3 | cubic16_s1 | 16 | 4 | 4 | **5** | **2** |  |
| 3 | cubic16_s2 | 16 | 5 | 4 | **8** | **3** |  |
| 3 | cubic18_s2 | 18 | 4 | 4 | **3** | **2** |  |
| 3 | cubic18_s0 | 18 | 5 | 4 | **5** | **3** |  |
| 3 | cubic18_s1 | 18 | 5 | 5 | **5** | **3** |  |
| 3 | cubic20_s0 | 20 | 4 | 4 | **5** | **2** |  |
| 3 | cubic20_s1 | 20 | 4 | 3 | **3** | **2** |  |
| 3 | cubic22_s1 | 22 | 5 | 4 | **8** | **3** |  |
| 3 | cubic22_s2 | 22 | 5 | 5 | **4** | **3** |  |
| 3 | cubic22_s0 | 22 | 6 | 5 | **9** | **4** |  |
| 4 | quartic10_s0 | 10 | 4 | 4 | **2** | **1** | 2 |
| 4 | quartic10_s1 | 10 | 5 | 5 | **7** | **2** | 3 |
| 4 | quartic12_s0 | 12 | 5 | 5 | **4** | **2** | 3 |
| 4 | quartic12_s1 | 12 | 5 | 5 | **5** | **2** | 4 |
| 4 | quartic14_s0 | 14 | 5 | 5 | **4** | **2** | 2 |
| 4 | quartic14_s1 | 14 | 5 | 5 | **4** | **2** | 3 |
| 4 | quartic16_s0 | 16 | 5 | 5 | **4** | **2** |  |
| 4 | quartic16_s1 | 16 | 6 | 6 | **5** | **4** |  |
| 5 | quintic12_s0 | 12 | 6 | 6 | **5** | **2** | 3 |
| 5 | quintic16_s0 | 16 | 7 | 7 | **7** | **4** |  |

Grouped by `pw`, exact values only, as `(n, min size₁ at order pw)`:

| pw | random cubic / quartic / quintic graphs |
|--:|:--|
| 3 | (8, 2) ×3, (10, 2) ×2, (12, 2) ×2 |
| 4 | (10, 2), (10, 5), (12, 3), (14, 3), (14, 3), (14, 5), (16, 3), (16, 5), (18, 3), (20, 3), (20, 5) |
| 5 | (10, 7), (12, 4), (12, 5), (14, 4), (14, 4), (16, 4), (16, 8), (18, 5), (18, 5), (22, 4), (22, 8) |
| 6 | (12, 5), (16, 5), (22, 9) |
| 7 | (16, 7) |

### 3.2 What the families say

* **Complete bipartite graphs: 2 at every order `pw`, for all `k` from 2 to 8.**
  `K_{k,k}` has `pw = k`, and the two minimal big sets are the two sides each
  with one vertex of the other side added (complements of size `k − 1`): "every
  separation of order ≤ `k` leaves a side that misses at most `k − 1` vertices of
  one class". Constant size at `pw = n / 2`: the densest graphs tried have the
  shortest blockages after the cliques (size 1).
* **Grids, trees, cycles, the `pw − tw = 2` graph: 2–4.** Cycles 2 at order 2 for
  every length; the 3×3 grid 4 (sizes 4, 5, 5, 7), the 4×4 grid 3; the spider,
  the complete ternary tree of height 2 and the complete binary tree of height 3
  exactly 3 (the three branches of the branch lemma, as disconnected minimal
  sets: two of three legs); the 10-vertex `pw − tw = 2` graph 3 at order 5 *and*
  3 at order 4 (three 7-sets whose complements are the three non-hub triples).
* **Random regular graphs: the minimum is a function of the order, not of `n`.**
  At `pw = 4` it is 2–5 from 10 to 20 vertices with no trend; at `pw = 5` it is
  4–8 from 10 to 22; it is 2 at every `pw = 3` graph. Across the orders it grows
  by about a factor 1.5–2 per unit: 2 at 3, 3–5 at 4, 4–8 at 5, 5–9 at 6, 7 at
  7. The frames are co-sets again: the minimal big sets of `cubic16_s2` (`pw 5`)
  are 8 sets of 7–11 vertices, each with attachment exactly 5, connected; of
  `cubic18_s0` 5 sets of 7–9 vertices.
* **The vertex-transitive graphs are where the minimum is large.** Petersen 15
  (`1.5 n`), Paley13 15, Shrikhande 22, Clebsch 32 (`2 n`), `Q₄` 26 (`1.6 n`,
  exact after 47 min of CaDiCaL), and two still bracketed when the 2-hour cap
  killed their runs: Heawood `[25, 32]` of 14 vertices (`≥ 1.8 n`, `≤ 2.3 n`;
  sizes `≤ 24` refuted at 56 min, the `≤ 28` query unanswered) and
  Möbius–Kantor `[16, 22]` of 16 (`≤ 15` refuted at 108 min). In every case the
  frame is a family of **co-small sets**:
  `V` minus a 3-vertex path on Petersen (15 of its 30 such paths), `V` minus a
  triple (13) or a pair (2) on Paley13, `V` minus a 4-set spanning two edges (30)
  or a pair (2) on Clebsch, `V` minus a 4-set on Shrikhande (22); every one
  connected, with attachment `pw − 1` or `pw`. Read as a statement about
  separations: *every separation of order ≤ `pw` has a side whose complement is
  at most a path of three* (Petersen) — the co-singleton frames of
  `reports/blockage_class.md` §4 at one or two more vertices.
* **The size is concentrated at the top one or two orders**, and not monotone in
  the order. Petersen 1, 1, 2, 5, 15; Paley13 1 ×5, 3, 13, 15; Clebsch 1 ×4, 2,
  16, 16, 10, 32; Shrikhande 1 ×5, 3, 16, 9, 22; `Q₄` 1, 1, 1, 2, 16, 7, 26;
  Heawood and Möbius–Kantor 1, 1, 2, 3, 6, then `[25, 32]` and `[16, 22]`. The
  jump sits at or just above the treewidth (Petersen `tw 4`, Clebsch `tw 8`,
  Paley13 `tw 8`): below it a clique or clique-minor frame of one or two sets
  suffices, above it the co-small-set frames take over.
* **size₂ is a constant factor shorter where it differs.** Petersen 8 against
  15, Paley13 9 against 15, `Q₃` 6 against 12, Mycielski's `M₄` 5 against 6;
  equal to size₁ on `K_{k,k}`, grids, trees and 11 of the 19 random regular
  graphs where it was computed (on the other 8 it is 2–4 against 4–7; the
  largest gap `quartic10_s1`, 3 against 7). Nothing in the data has size₂
  growing differently from size₁.

### 3.3 Lower bounds

Every lower bound here is a SAT refutation of "a blockage of order `k` with
`≤ s` minimal big sets exists" — exact where it meets the construction. For the
bracketed cases the refuted side is the lower bound shown. No counting argument
was found that beats the solver: the natural one — each frame set lies on one
side of every separation `(X, X^c)`, so the frame must "cover" the set of small
separations — gives at best a constant on these graphs, because one co-small set
lies on the large side of almost every separation.

## §4. Verdict: the shape of the data

**The kill criteria.** *K-hard* is **met by its letter**: on the random cubic
graphs the exact minimum at order `pw` goes from 2 (8 vertices) to 8 (22
vertices), a factor 4 against the allowed `(22 / 8)² = 7.6`, and no family
exceeds `n²` — the largest ratio to `n` is Clebsch's `32 / 16 = 2.0` (exact),
then Heawood at `≥ 25 / 14 = 1.8` and `≤ 2.3` (bracketed), `Q₄` at
`26 / 16 = 1.6` (exact), Petersen 1.5, Shrikhande 1.4, Paley13 1.15; every
other graph is below `0.7 n`. *K-easy* is **met**: at orders `≤ ⌈√pw⌉ ≤ 3` the
minimum is at most 3 on every graph tried. So in this measure, at these sizes,
**every graph tried has a blockage of order `pw` with at most `2 n` minimal big
sets** (`2.3 n` if Heawood's bracket closes at its top), and the "exponential
on expanders" half has no support.

**What the data show instead**, and why that verdict is weaker than it reads:

1. The minimum at order `pw` is governed by the **order**, not by `n`. On random
   regular graphs it is flat in `n` at fixed `pw` and grows ×1.5–2 per unit of
   `pw` (2, 3–5, 4–8, 5–9, 7 at `pw = 3 … 7`); on the vertex-transitive graphs
   the sequence over the orders ends 5, 15 (Petersen), 13, 15 (Paley13), 10, 32
   (Clebsch), 9, 22 (Shrikhande). A law `size ≈ c · 2^{pw}` is *consistent*
   with every exact number here; so is `size ≈ 2 n` on the vertex-transitive
   graphs. The two cannot be told apart below 22 vertices, where `pw ≤ 9`, and
   random cubic graphs reach `pw 6` only at 22 vertices (where the model has
   `4 M` variables and one minimum is still bracketed after 30 minutes of
   Glucose). **If** the minimum is exponential in the order and the order is a
   positive fraction of `n` on expanders, the conjecture's hard half follows; the
   measurement shows the first factor to `pw = 9` and cannot see the second.
2. The large frames have one shape: **co-small sets** `V \ S` with `|S| = 2, 3,
   4` on the symmetric graphs and co-sets of `n − 7 … n − 11` vertices on the
   random cubic ones. A blockage of this shape says "no separation of order
   ≤ `pw` is balanced". Its size is the number of small sets `S` that have to be
   named — a count of *local* configurations, which on a vertex-transitive graph
   is a multiple of `n` and on an expander with `pw = Θ(n)` would have to name
   sets of size `Θ(n)`, which is where the exponential would come from. That is
   a reading, not a measurement.
3. The measure is well-posed but not canonical: size₂ (any generators) is up to
   4× shorter than size₁ (the frame) to 9 vertices and ~2× on Petersen and
   Paley13, and the minor-pullback language of `reports/blockage_class.md` is
   shorter still for clique-minor blockages. Any statement about "the size of a
   blockage" has to name the language; the frame language is the pathwidth
   analogue of a bramble's set count and is what was measured.
4. Three facts came out clean and could be stated: every graph with `pw > tw`
   to 9 vertices needs at least 3 minimal big sets at order `pw` (13,548 of
   13,548; one is a theorem — a one-set frame forces `tw ≥ k` through the sink
   of an oriented tree decomposition — two is open); `K_{k,k}` has a 2-set
   blockage of order `k` for every `k ≤ 8`; and `min size₂` is non-decreasing
   in the order on all 273,193 graphs while `min size₁` is not.

**What is exact and what is bounded.** Every number in §2 is exact (273,193
graphs, 3 measures, every order; two brute-force enumerations and the all-pairs
checker behind the model). In §3 every value in bold is exact; the four minima
the 10-minute Glucose runs left bracketed were re-run untimed on CaDiCaL under a
2-hour cap: `Q₄` at order 7 closed at **26** (47 min) and `cubic22_s0` at order
6 at **9** (57 min), while Heawood (order 6) and Möbius–Kantor (order 6) were
killed by the cap at `[25, 32]` and `[16, 22]` — their processes are gone and
their logs end without a final line, so these two are brackets, each with the
refuted side as its lower bound; no number is an unverified upper bound. The
treewidths are exact (C DP); the pathwidths exact (subset DP to 18, the C
program's `refutation` status above). Compute: about 29 core-hours for the
census, 4 for the families, 3 for the 22-vertex graphs and 8 for the five long
re-runs; nothing under `solutions/` was touched and nothing from the corpus
was re-solved.

**Literature.** We found no prior statement of the pathwidth analogue of Grohe &
Marx's bramble-size theorem, and no prior measurement of the number of minimal
sets of a blockage; BRST (1991), Diestel & Oum (2019) and Erde (2017) say
nothing about the size of a blockage (`reports/pathwidth_np_conp.md` §0).
