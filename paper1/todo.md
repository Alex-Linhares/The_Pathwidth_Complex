# *The pathwidth complex*: to do

Started 2026-10-09. Check items off as they are done.

## Members of the pathwidth complex still to find (owner, 2026-11-06)

- [ ] **Look for problems that also belong to the pathwidth complex** — problems in
  the literature equal to pathwidth or within a fixed offset or band of it that
  Table 1 and the three members added in paper 1 (wavefront, progressive
  pebbling, vertex search) do not list. The owner can point to some; start from
  Garey & Johnson (1979, now held) for the layout, arrangement and search
  problems, from the vertex-separation / node-search / interval-thickness
  literature of paper 1's Section 2, and from `paper2/complex_members.md`.
  Each candidate gets the Instance / Question form of
  `paper1/problem_transformations.md`, a transformation proved on paper and
  checked by `paper1/complex_check.py` on small instances, and only then a
  Lean statement in `lean/MOSPFormalization/Complex/`.

  **The owner's first candidates, read in Garey & Johnson (2026-11-06; scanned
  book, entries read from rendered pages 198–201 and 228–229):**
  - **GT35 Interval Graph Completion** (p. 198): is there an interval supergraph
    with at most `K` added edges; Garey, Gavril & Johnson 1977, from Optimal
    Linear Arrangement; NP-complete even on line graphs. *Reading*: this is the
    **sum** objective of the family. Pathwidth + 1 is the smallest clique number
    of an interval supergraph (interval thickness, in the complex already); the
    smallest *number of edges* of an interval supergraph is the **profile**
    (Billionnet 1986, to be checked and held), the sum analogue of pathwidth as
    the minimum linear arrangement is of bandwidth. Not a member; a relative to
    state as such, with the exact relation to the complex's interval-thickness
    row written out.
    *Checked 2026-11-06 at the owner's question "Interval Graph Completion =
    MOSP?"*: the two are different objectives over the same family of
    interval supergraphs — fewest added edges (GT35, = profile) against
    smallest clique number (interval thickness = pathwidth + 1 = MOSP). On
    every connected graph of the atlas to 7 vertices and on 48 random sparse
    graphs at 8–9 vertices (exhaustive over orderings) **some ordering is
    optimal for both** — no separating example found yet. A separating
    example is expected on trees (profile-optimal orders are DFS-like, with
    vertex separation about the height, while the pathwidth of a complete
    binary tree is about half the height): **to do**, a complete binary tree
    of height 4 or 5 with an exact profile (Kuo & Chang 1994, polynomial on
    trees, to be held) against its pathwidth. If none exists, that is a
    theorem relating the two rows and worth stating; if one does, it is the
    sentence that separates them.
  - **SR16 Consecutive Ones Matrix Augmentation** (p. 229): change at most `K`
    zeros to ones so that the matrix has the consecutive-ones property; Booth
    1975, Papadimitriou 1976a, from Optimal Linear Arrangement. *Reading*: on a
    MOSP matrix (customers × patterns) a pattern order with every row's ones
    consecutive is exactly an order in which every stack closes as soon as it
    opens; the ones added count, summed over customers, the idle open-stack time
    `Σ_c (last_c − first_c + 1 − |row_c|)`, so this is the **sum** version of
    MOSP where MOSP is the **max over time** of open rows — the matrix form of
    GT35. Not a member; the same relative seen from the matrix side (and the
    matrix side of Billionnet's profile, to be checked). SR14 Consecutive Ones
    Submatrix (p. 228, Booth 1975; from Hamiltonian Path) is the deletion
    variant, to be placed beside it.
  - **GT44 Minimum Cut Linear Arrangement** (p. 201): cutwidth; Stockmeyer
    1974b, Gavril 1977a, from Simple Max Cut. *Reading*: a **band relative on
    bounded degree**, not a member: `pw ≤ cw ≤ Δ · pw` (Chung & Seymour 1989;
    Korach & Solel 1993), exact for `Δ ≤ 3` through the degree-clique expansion
    of `reports/subexp_pathwidth.md` §3.4 (Makedon & Sudborough 1989 to be
    checked for the same statement). The complex already has the negative:
    edge separation as cutwidth is false (`Complex/EdgeSeparation.lean`). The
    owner's "maybe" is right: in the paper as a band row for subcubic graphs,
    or out.
  - **GT42 Optimal Linear Arrangement** (p. 200): `Σ_{uv ∈ E} |f(u) − f(v)| ≤ K`;
    Garey, Johnson & Stockmeyer 1976, from Simple Max Cut; polynomial on trees.
    *Reading*: the sum version of **bandwidth**, two steps from pathwidth (sum
    for max, bandwidth for pathwidth); no fixed offset or band with pathwidth
    is known to us and none is expected (a path has arrangement cost `n − 1` and
    pathwidth 1; a star has cost `Θ(n²)` and pathwidth 1). Out, unless the
    owner knows a relation we do not.
  - Spotted on the same pages, to place: **GT40 Bandwidth** (p. 200; the
    complex has split bandwidth as a band, bandwidth itself is not within a
    band of pathwidth: `pw ≤ bw`, ratio unbounded); **GT36 Path Graph
    Completion** (p. 199, Gavril 1977b, from Interval Graph Completion:
    supergraph an intersection graph of paths in a tree) — the tree-shaped
    cousin of GT35, a sum problem, out; **GT46 Directed Elimination Ordering**
    and **GT47 Elimination Degree Sequence** (p. 201) — the chordal /
    treewidth side, out.

## The parallel tabu step, proved and run on the hardest instances (owner, 2026-11-07)

- [ ] **Prove it.** The neighbours of one tabu step are independent exact calls
      on independent minors, so evaluating them on separate cores is sound: the
      step's outcome (the chosen move, the floor claimed) is the same as the
      sequential step's, and every claim rests on its own refutation. In Lean,
      on top of `Search/MinorTabu.lean`: a parallel step is a set of `Justified`
      claims, one per neighbour, whose union is a `Run.claims`, and
      `tabu_output_le_pathwidth` / `exists_visited_of_le_output` hold unchanged
      — the soundness theorems are stated for any list of visited forests, so the
      parallel step needs only the lemma that evaluation order and concurrency
      do not enter the claims (no shared state between neighbour calls: each is
      a fresh engine run on its own minor with its own memo, as in the split of
      `Search/Split.lean`, where tasks share nothing). State it, check it on the
      small-graph harness, prove it.
- [ ] **Build it.** `minor_tabu.c`: evaluate the sampled neighbours of a step in
      parallel (fork per neighbour with a pipe, or a worker pool over the engine
      with one memo each; the engine's static state means processes, not
      threads, unless audited), `-j cores`; a step then costs the slowest
      neighbour. The chosen minor's climb stays sequential. Measure the steps per
      budget at 1, 8 and 32 cores on two Rome graphs of known width and on one
      open class.
- [ ] **Run it on the hardest open instances**: the residue of the ten-hour
      seeded run (classes still at `width − 1` after their budget), one class at
      a time with all the nice-19 cores the machine can give, several hours
      each, largest-gap-closable first (gap 1); every closure through the
      independent checker before it is folded; the tally into Appendix G's
      status paragraph. The 32-core box here first; a 100-core cloud machine
      changes what is reachable and is the owner's call.

## From the owner's Zotero comments of 2026-11-07 (high priority, before arXiv)

- [ ] **Upper bounds for the 610 Frinhani instances (400–1,000 customers)**: "at a
      bare minimum we should do a tabu search here". They are in the dataset with
      no value at all because exact search is out of reach at that size; run the
      heuristic side (`satisfiability/heuristics.py`: `rule+cs-dfs`, then tabu
      seeded by it) on all 610 under a modest budget, record the witness layouts
      as `solution` provenance (never certified), and update Section 5's dataset
      paragraph ("None of them has a value yet") and the dataset tables.
- [x] Applied 2026-11-07: "settled 25 years later"; "the original Linhares--Yanasse
      table"; "Chu and Stuckey's definite move fails" in the counterexample caption;
      "(our implementation, …)" deleted from Figure 4.2's caption; the 743 sentence
      made precise (one Rome class certified by refutation without a layout on file);
      Chu and Stuckey's search (Algorithm 4.1) and the implementation-check list
      moved to Appendix B with pointers; and the terminology: "the previous
      algorithm" is now "Chu and Stuckey's algorithm" and "our corrected search"
      is "our corrected algorithm" throughout the prose, figure labels included.

## Before posting on arXiv

Done 2026-10-19: the source bundle builds and compiles standalone
(`python -m paper1.latex.make_arxiv`, `latex/arxiv.tar.gz`); the metadata,
categories, licence choice and a 1,783-character abstract are in
`latex/arxiv_metadata.md`; the axiom audit, reference check and paper tests
pass (the hypercube and Mycielski theorems were missing from
`axiom_check.lean`); `pw(M_9) <= 138` and the date are current.


- [x] **Affiliations and emails** for both authors (2026-10-19; Yanasse's in
      English, the owner's choice).
- [x] **The paper's repository**: it is this repository, public at
      github.com/Alex-Linhares/MOSP_trough_SAT, which `latex/sec7_data.tex`
      names; the three `\repofile` paths exist in it, and the README's opening
      points at the paper (2026-10-19). A separate paper repository with its own
      DOI is the IJOC item below, not an arXiv one.
- [ ] **Re-check the novelty claims.**
  - [ ] Read the 14 unread works that cite Chu & Stuckey 2009, listed in
        `literature/MISSING.md` (item 01 of loop0008). De Giovanni et al.
        (2013, *ITOR*) first. *2026-10-19: eight obtained and read (Gange 2019, Visentin 2019,
        Stivala 2010, Chu & Stuckey 2012, Doulabi 2016, Arbib 2012 and 2016,
        De Giovanni 2010); none bears on the rules, and De Giovanni 2010 is a
        fourth work that ran their code without a failure, now cited in
        Appendix B. 2026-10-22: both De Giovanni 2013 papers received from the author
        and read; both ran Chu & Stuckey's code without a failure (six such
        works now). Four remain: Carvalho & Soma 2015, Lima & Carvalho 2017,
        Santos & Carvalho 2018, and the two mislinked ITOR papers. Counts in
        the paper: 66 of 141.*
  - [ ] Keep the wording "we found no prior report", never "first"
        (`prior_art_counterexample.md`).
- [ ] **Decide whether to write to Peter Stuckey** (and Geoffrey Chu) before
      the counterexample and the 34-customer wrong optimum become public.
- [ ] **arXiv endorsement.** The first author has arXiv papers in cs.AI
      (2604.17229, April 2026), so the account exists; endorsement is per
      category, and cs.DS is new to it. Start the submission: the form says at
      once whether cs.DS needs an endorser, and emails the request link. The
      abstract page of any recent cs.DS paper lists who can endorse.
  - Primary category: cs.DS.
  - Cross-lists: math.CO, math.OC, cs.DM, optionally cs.LO.
- [ ] **IJOC's preprint policy.** Confirm that posting on arXiv before or
      during review is allowed. INFORMS's author pages refused scripted access;
      check by hand.

## Before submitting to IJOC

- [ ] **The IJOC LaTeX class and formatting rules**, downloaded by hand from
      INFORMS. The draft uses `article` as a stand-in.
- [ ] **Length.** The draft is 45 pages, about 25 of them body. Decide between:
  - cutting Section 4, as `review_readability_2.md` suggests;
  - moving the appendices into an online supplement.
- [ ] **The repository in IJOC's form:** a code-and-data repository with its own
      DOI, following the template at `github.com/INFORMSJoC/2019.0000`
      (`ijoc_literature.md`).
- [ ] **Cite the relevant IJOC papers** from `ijoc_literature.md`, in particular
      Garcia de la Banda & Stuckey (2007), already held, and the 19 papers to
      obtain listed in `literature/MISSING.md`.

- [ ] **Scaling table for the parallel refutation at 1, 2, 4, 8 and 16 cores** (owner,
      2026-11-06), beside the SageMath comparison but kept out of it (Sage has no
      parallel mode): on the graphs Sage could not finish, our split refutation at
      each core count, wall time and total nodes (the lost memo hits and the waste
      counted). Needs the split driver for graphs: `paper1/solver_fix_split.py`
      works on MOSP instances, so either an adapter that writes a graph as a
      MOSP instance with one pattern per edge (its customer graph is the graph,
      Theorem~thm:mosp) or a graph-side split in `pathwidth_solver/`.
- [ ] **Extend the native split to graphs above 128 vertices.** `cs_split_expand` /
      `cs_split_decide` (`satisfiability/native.py`, `_MAX_CUSTOMERS = 128`) exist only
      for the two-word engine; `decide` has the w4/w8/w16 variants to 1,024. Found
      2026-11-09 when the scaling run on Random-200-200-10-5 (200 vertices) crashed
      and the graph split's open-class queue would have crashed at its first class
      above 128 (most of the 325 are). Until then `graph_split.py` filters n <= 128.
- [ ] **Find the memo optimum** (the default was raised first, owner 2026-11-09): a sweep
      of the memo limit over about ten proved graphs of the kinds on record (Rome, PACE,
      HB, named) at 2^22, 2^24, 2^26 and, with the C table's 2^26-slot cap raised, 2^28,
      recording nodes, time and peak RSS; the questions are whether the knee always sits
      near the refutation's distinct-state count (49M on grafo8793.100; the saving
      saturates there) and whether a fixed default or an adaptive one (double the table
      when it fills) is the better rule. Known so far: 4M x 16 B = 64 MB = this CPU's L3,
      which is why the default is fast per node; a 1.1 GB table is 40% slower per node
      where it saves nothing (Higman–Sims) and 8-11x faster where it does (two Rome
      graphs). A few single-core hours on proved instances: needs the owner's go.
- [x] **Raise the default memo limit** — done 2026-11-09 at the owner's word, to
      64,000,000 in `pathwidth_solver/cli/pathwidth.c` (`MEMO_LIMIT`), `satisfiability/native.py`
      (both entry points) and `satisfiability/customer_search.py`; tests pass; the C table's
      2^26-slot cap is unchanged (the limit then fills it to 95% at most on the graphs
      measured). Was proposed as: from
      4,000,000 to 64,000,000 states in `pathwidth_solver/cli/pathwidth.c`,
      `satisfiability/native.py` (`decide_native`, `split_decide`) and
      `satisfiability/customer_search.py`; 1.1 GB per process at the C table's
      2^26-slot cap (raise the cap too if the limit is to mean anything above 33M).
      Measured 2026-11-09 (Section 5, Table tab:splitscale): grafo8793.100 254 s ->
      33 s, grafo11458.100 3,585 s recorded -> 60 s, Higman–Sims and the PACE Gaifman
      graph unchanged. Then: re-time (not re-prove) a sample of the hard Rome
      refutations and the 125x125 split tasks to say how much of the recorded
      core-hours was the memo.
- [ ] **The memo limit is the sequential search's bottleneck on hard refutations**
      (2026-11-09, `reports/scratch/split_scaling/memo_diag.out`): on grafo8793.100
      (width 10) memo off gives 9.02e8 nodes sequential and split alike (as proved);
      memo on gives 8.42e8 sequential but 1.19e8 for the split's 87 tasks with a
      fresh 4M-entry memo each — the single memo saturates. A sweep of
      `memo_limit` on the sequential run is in `memo_limit.out`. If a larger memo
      recovers the split's count, the paper's "speed-up" must separate the two
      effects (memory and parallelism), and the sequential default should change.
- [ ] **Appendix F: the NP ∩ coNP paragraph and two citations** (from
      `reports/pathwidth_np_conp.md` §7, 2026-11-07): write the six safe
      sentences (pw ≥ k+1 is coNP-complete, so a short certificate on every
      graph gives NP = coNP; the blockage is the fugitive's strategy, BRST (5.1);
      Grohe & Marx 2009 Thm 8 on bramble size and Hatzel et al. 2022; the
      fixed-k obstruction view, Kinnersley & Langston 1994 p. 199; GJNW 2023
      polynomial approximate certificates; "we found no published lower bound
      with an independently checked proof object", PACE validators check
      decompositions only). Cite **Tamaki (SEA 2022, arXiv 2202.07793)** beside
      the minor certificates of Section 5 — he ships treewidth lower bounds as
      minors (≤ 49 vertices) verified by Bouchitté–Todinca — and soften
      Section 5's "we found no prior report of a searched contraction-minor"
      accordingly (searched on *pathwidth* benchmark instances is what remains
      unreported). Bib entries needed: Lengauer 1981, Kashiwabara & Fujisawa
      1979, Grohe & Marx 2009, Hatzel et al. 2022, Kinnersley & Langston 1994,
      Megiddo et al. 1988, Tamaki 2022, Dell et al. 2016/2017; open links in
      `literature/MISSING.md` under "Pathwidth lower bounds and NP ∩ coNP".
- [ ] **`_lower_bound`: the expansion bound runs on every call although the docstring, CLAUDE.md
      and the paper say "off by default"** (found by the integration agent, 2026-11-10): the
      code calls `mosp_lower_bound(instance, max_t=8, time_budget=None)` unconditionally (no
      `if expansion_budget is not None` guard), so the September decision (off: slower on every
      one of the 25 hardest, `reports/expansion_bound.md` §6) is not what runs; it attains the
      floor on 1,329 corpus instances, and the 77.0% tightness and the spectral numbers of
      `reports/spectral_floor_integration.md` were measured with it on. Owner's call: restore
      "off by default" (guard on the budget) or change the record to "on"; either way the
      docstring, CLAUDE.md and Section 5 must agree with the code. Correctness unaffected
      (validated, zero violations); only time.
- [ ] **Formalise the spectral lower bound in Lean** (owner, 2026-11-10). The component
      entering `_lower_bound` and the dataset's `bound:spectral` floors rests on cited
      theorems and the corpus validation only: (i) the prefix-separator argument — a layout
      of vertex separation w gives, at every prefix size t, a separator of at most w vertices
      splitting the rest into parts of sizes t and n − t − w (elementary; state it over
      `LinearLayout`/`vertexSeparation`); (ii) the eigenvalue separator inequality of
      Mohar–Poljak (Helmberg–Mohar–Poljak–Rendl 1995 eq. 21) with the top-degree-sum
      strengthening, and Helmberg et al. Theorem 11 eq. 20 — these need the Laplacian, its
      second-smallest and largest eigenvalues and the Courant–Fischer characterisation;
      Mathlib has `Matrix.IsHermitian` eigenvalues and the Rayleigh quotient (check
      `Matrix.IsHermitian.eigenvalues`, `LinearMap.IsSymmetric.rayleigh`), so the inequality is
      the real work; (iii) the family lifts: pathwidth is monotone under induced subgraphs
      (peel) and minors (`Minor.lean` has the minor half). Target statement:
      `spectralFloor G ≤ pathwidth G` in `lean/MOSPFormalization/SpectralBound.lean`, with
      the Lean value matched to `learning.spectral_bound.spectral_graph_bound` on small
      graphs by `learning/sandwich.py`'s pinning stage. Until then the paper says the
      component is "not formalised", as the clique bound was before 2026-09-27.
      *Status 2026-11-10*: the component is in `_lower_bound` (`satisfiability/mosp_solver.py::_spectral_floor`,
      `BOUND_SOURCES` has `spectral`) and the nine dataset floors are written
      (`reports/spectral_floor_integration.md`); both rest on the cited theorems and on the
      corpus validation (0 of 6,376 certified optima violated, `--stage solver`), not on Lean.
      The checker replays the prefix arithmetic from stated eigenvalues; nothing in Lean
      states Theorems 1–3.
- [x] **Dataset rebuild: three closures on record not yet in the dataset** — done 2026-11-10
      with the spectral floors (`reports/spectral_floor_integration.md` §0): BalancedTree_3_5 is
      `certified:theorem` (the nested branch-lemma certificate replayed by `dataset_check.py`),
      can_292 is `certified:minor` at 22 (`graph_split/can292/results_can292.csv`), NY_13 was
      `certified:minor` already. **Still to do**: Section 5's graph table (`tables/graphs.tex`,
      written by hand) and the prose that quotes open-class counts; and the loop0013 pass-1
      search floors (`13_pass1/pass1.csv`, `ladder_floor`/`search_floor`) are not folded as
      dataset floors — they are not in the run format and their unit convention would need
      pinning first; the dataset's `floor` on the other open classes is the C program's own.
- [ ] **Dataset table drifted from the prose**: regenerating `tables/dataset.tex`
      on 2026-11-07 (after loop0013's pass 2 closed classes) moved PACE 2016
      open 37 -> 36, PACE 2017 open 54 -> 49, Rome open 1 -> 0, minor-certified
      counts up; the regenerated table is committed, the Section 5 prose that
      quotes the open counts has not been re-read against it.
- [x] **The solver claim: head-to-head against SageMath** — done 2026-11-07
      (run 2026-11-06 22:10 to 2026-11-07 09:20, the paired, pinned, CPU-capped
      protocol of `pathwidth_solver/bench/sage_paired.py`, 881 graphs, load 8-84
      at launch): ours proves 768, SageMath 550, every one of the 550 among ours
      with equal widths, **SageMath-only 0**, ours-only 218, neither 113; median
      CPU ratio 34 where SageMath needs >= 1 s, ours slower on none. Section 5
      "Head to head with SageMath", Table `tables/sage_paired.tex` from
      `paper1/data/sage_paired_600s.csv` (`make_tables.py`). The 50-graph
      variance sample (`--sample 50 --seed 0`) ran on the busy machine from
      09:22 (`results/sage_paired_sample50_busy.csv`); ended 10:05: every outcome
      and width the same, node counts identical, CPU times within 0.6-1.6x; in
      the subsection's last paragraph.
- [ ] **Add the configuration table to Section 4**, beside Theorem 4.9, so the
      claim is exact and fair: which configurations fail, which do not, and
      that "answers correctly here" is not soundness (the published better move
      is false as a theorem too).
- [ ] **Hunt for instances that break their published configuration** (better
      move on, old move, memo: the one Chu & Stuckey actually run). Lean will
      not show a failure there unless one exists, so the question is empirical:
      search for small instances on which that configuration reports a wrong
      optimum, starting from the published better move's Lean counterexample
      (Section 4) the way `false_refutation_hunt.py` started from the definite
      move's, with the corrected search, SAT/DRAT and the lattice oracle
      (n <= 15) as referees. If one is found, check it in Lean as Theorem 4.9
      was; if none is, report the size of the search, so the paper can say how
      hard the open question is.
- [ ] **Who runs the definite move alone?** Check Chu (2011), Fink (2012) and
      the code behind Frinhani et al. (2018), reused by Martin, Yanasse & Pinto
      (2022). If any runs it without the better move, the counterexample bears
      on published work directly.

## The contraction-minor lower bound (found 2026-10-11)

The exact pathwidth of a contracted minor is a lower bound
(`reports/pathwidth_lower_bounds_survey.md`). It proves pw(myciel6) >= 38 on a
58-vertex minor in under a second, pw(myciel7) >= 71 (published: 52), and
closes Random-125-125-2-1_0, 2-3_0, 6-1_0 and SP4 in 1-80 s each. The idea is
known for treewidth (Bodlaender, Koster et al.), so the claim is the
measurement and that, for pathwidth, it is not capped by treewidth.

- [ ] **Into the solvers.** A budgeted step in the `pathwidth_solver` descent and in
      the MOSP descent: before refuting UB - 1 on the full graph, contract to
      about n/2 and upward and try to refute UB - 1 there; a refutation ends the
      descent with proof "bound" (or a new provenance, "certified:minor"). Measure
      on every benchmark set: what it closes, what it costs.
- [ ] **myciel7.** Settle 71 against 72 (Coudert et al. 2016 leave it open at
      pw <= 72). If it is new, say so carefully, after the literature check.
- [x] **Lean** (done 2026-10-12, `lean/MOSPFormalization/Minor.lean`, commit
      1c24e5d2f): contracting an edge never increases pathwidth
      (`pathwidth_contractEdge_le`), nor does deleting a vertex or an edge
      (`pathwidth_induce_le`, `pathwidth_mono`); along any legal contraction
      sequence (`pathwidth_minorOf_le`); the certificate theorem
      (`pathwidth_gt_of_minorOf`, and `pathwidth_gt_of_iso_minorOf` for a minor
      on its own labels); and the MOSP form `MOSPInstance.lt_mospValue_of_minorOf`.
      Axioms: the three standard ones. Statements checked first on small graphs
      (`tests/test_lean_minor_statement.py`). Still assumed: that the code's minor
      is isomorphic to `minorOf` for the recorded sequence (tested), and the
      soundness of the refutation on the minor. Proposed paper text, for the
      write-up: Section 5, "Every minor lower bound rests on minor monotonicity
      (Fellows & Langston 1987, Lemma 4.2): contracting an edge, or deleting a
      vertex or an edge, never increases pathwidth, so a refutation of
      pw(H) <= w on a minor H reached by a recorded contraction sequence proves
      pw(G) >= w + 1, and on the MOSP graph that every pattern order opens at
      least w + 2 stacks; both are proved in Lean." Appendix A entry `minor`,
      with \leannames{pathwidth_contractEdge_le, pathwidth_induce_le,
      pathwidth_mono, pathwidth_minorOf_le, pathwidth_gt_of_minorOf,
      MOSPInstance.lt_mospValue_of_minorOf}.
- [ ] **A checkable certificate.** The minor certificate is the contraction
      sequence (checkable by anyone) plus a refutation on the small graph (a
      DRAT proof, or our search certificate of Section 5). Ship both for every
      value certified this way.
- [ ] **Write it up.** A subsection of Section 5 ("A lower bound from minors"),
      the myciel6 passage rewritten (no longer a loss), the corpus values it
      re-certifies cheaply, the cost of 2-3_0 falling from 1,128 core-hours to
      seconds, and an honest line on what remains open (2-2_0: every contraction
      up to 95 vertices still admits 24).
- [ ] **Re-run the dataset's 860 upper-bound-only classes with the minor step.**
      *Running since 2026-10-21 02:50: `reports/scratch/dataset_open/run_unlimited.py`,
      415 classes (every non-certified class within the engine's limit, Frinhani
      excluded), the C program, no time limit, 24 workers at nice 19, cheapest
      first; results fold in from `results_unlimited.csv`. Rebuild with
      `python -m paper1.dataset values`, `write`, `tables` when it ends.*
      They were certified under short budgets (about 2.5 core-hours in all), so
      most are "ran out of time", not "proved hard": PACE 2016/2017 288, Rome
      326 (292 already closed by the minor step), Carvalho & Soma 139,
      Harwell-Boeing 33, colouring 27, named 23, grids 19. Run them with the
      minor step on (default once the solver agent commits), a few cores, a
      generous cap; then rebuild the dataset (`python -m paper1.dataset values`,
      `write`, `tables`) and update the counts in the abstract, Section 5 and
      the conclusion, whose "the graph sets will not close by budget alone" and
      "certified without search only when a lower bound meets its witness"
      need rewriting around the minor bound. Also try the ~150 classes above the 1,024-vertex limit:
      their minors may fall below it, but a minor gives only the lower bound,
      so a class is certified only where a witness layout of the full graph
      (from the dataset's runs, Python heuristics, annealing, or a known family
      layout such as row-by-row for grids) meets it; elsewhere record the
      narrowed interval (as myciel7's 71-72); the 610 large
      Frinhani MOSP instances stay out of reach.
- [ ] **Say it in the paper:** "Comparative pathwidth complex theory is richer than
      studying each problem in isolation." A thesis line for the introduction
      or the conclusion: the transfers in both directions (the corrected search
      from MOSP, the minor bound from pathwidth), the slips found only by
      setting the problems side by side (the false rows, Kirousis &
      Papadimitriou's edge cases), and one dataset for every problem.
- [ ] **A table: hard MOSP instances collapsing from core-days to seconds through
      the pathwidth lower bound.** One row per instance: its optimum, the cost
      of the full refutation that certified it, and the minor certificate
      (minor size, nodes, seconds). What we have now:
      - Random-125-125-2-3_0 = 21: 1,128 core-hours -> a 69-customer minor,
        666,153 nodes, under a second;
      - Random-125-125-2-1_0 = 24: 366.5 core-hours (Table B.1) -> an
        87-customer minor, 30 s (large budget);
      - measured 2026-10-13 at the owner's request (2 cores, 5 min each,
        reports/scratch/minor_table/): 2-5_0 = 20, 368.8 core-hours -> a
        63-customer minor, 0.4 s; 2-4_0 = 24, 154.1 -> 69 customers, 0.3 s;
        4-5_0 = 46, 26.1 -> 99 customers, 82 s; not settled in 5 min: 4-4_0
        (bound 50 of 51), 4-2_0 (55 of 57), 2-2_0 (24 of 25);
      - Random-125-125-6-1_0 = 81 and SP4 = 53: minor bound equals the optimum;
      - Random-125-125-2-2_0 = 25: 2,231 core-hours, not reached by any minor
        up to 95 customers (an honest last row).
      So 5 of Table B.1's 9 values settle in seconds or minutes.
- [ ] **Writing rule: no development history.** When writing about the solver,
      leave out the history of how our algorithm was developed (the bugs, the
      re-certifications, the configurations we tried, the order things were
      found). Focus on two transfers:
      - **MOSP -> pathwidth:** the correction of Chu & Stuckey's search, the
        best exact MOSP algorithm, which is also a pathwidth algorithm;
      - **pathwidth -> MOSP:** the new lower bound from contracted minors, which
        settles MOSP instances that the search needed core-days for.
- [ ] **A light touch, for the reader: Lean versus Kirousis & Papadimitriou.**
      Mention, with humour, that Lean caught two slips in Kirousis &
      Papadimitriou (1985, 1986): their equality ns = vs + 1 fails on graphs
      with no edges (no searcher is needed, so ns = 0 while vs + 1 = 1;
      `edgeless-ns`), and the proof of their Theorem 4.1 has a gap on the star
      K_{1,3} (`kirousisPapadimitriou_claim2_false`), repaired by their own
      Corollary 2.4; the theorem is true. Keep it accurate and affectionate:
      name both authors, call them slips, not "serious errors", and laugh at
      ourselves too, since our own 2002 table has the same edge-case flaw.
      Facts in Appendix B ("Edge cases and a gap in a published proof").
- [ ] **Say it in the paper:** "The complex gets an excellent lower bound from
      pathwidth, and an excellent algorithm from the MOSP side." The thesis of
      the transfer in one line: the minor bound comes from the pathwidth
      literature, the customer search from the open-stacks community, and the
      complex is where they meet. Candidate places: the abstract's close, the
      introduction's findings, and the conclusion's "What transfers".
- [ ] **Compare with Coudert et al. on the rest.** Their win on myciel6 came from
      prefix storage, not bounds (JEA 2016, Sec. 4.3); the remaining difference
      in raw search speed is unexplained. The SageMath head-to-head item above
      should include the solver with the minor step.
- [ ] **Fetch the papers** listed under "Pathwidth lower bounds (2026-10-11)" in
      `literature/MISSING.md` (Bodlaender & Koster 2011 journal version,
      Clautiaux et al., Lucena, Chandran & Subramanian, Mohar & Poljak,
      Fraire-Huacuja et al., Solano & Pioro).

## The introduction: MOSP's other guises (2026-10-17)

- [ ] **Name MOSP's other settings in the introduction**, after the cutting
      industry: among them the scheduling of scenes in film shooting. (The
      humorous opening was considered and dropped by the owner.)
      - **Film shooting / talent scheduling:** Cheng, Diamond & Lin (1993), JOTA
        79(3) 479-492, doi 10.1007/BF00940554; Garcia de la Banda, Stuckey & Chu
        (2011), INFORMS JoC 23(1) 120-137, doi 10.1287/ijoc.1090.0378. Both are
        listed for fetching in `literature/MISSING.md` (browser download).
        Talent scheduling minimizes a weighted *sum* of waiting days, not the
        *maximum* number on hold at once: present it as a close relative of
        MOSP, not the same problem.
      - Other settings: check Yanasse & Senne (2010) and Linhares & Yanasse
        (2002) for further applications; VLSI gate matrix layout is already in.

## Closed formulas for recursive families (high leverage, 2026-10-18)

- [ ] **Plan: `reports/closed_formula_families_plan.md`.** Exact pathwidth of
      small members, guess a formula, prove it by induction on the
      construction, Lean as for grids. First: Mycielski graphs and hypercubes
      (2026-10-18, after the G(n, c/n) pilot).
      *2026-10-31: increment-witness experiment done (plan, "Second
      results"): minor-carried induction works for trees only; hypercubes
      are contraction-critical at odd d (Harper's profile is the induction),
      Mycielski witnesses are non-nesting folds; Q_7 ≤ 43 verified by
      Harper's layout, 42 not refuted in an hour; no recurrence fit survives
      the spare-term rule.*

## Lean the derived random-graph bounds (high priority, 2026-10-17)

`reports/random_graph_pathwidth_survey.md` derives three bounds no paper states
(marked **[derived]** there, unrefereed). Check them, then prove them in Lean.
The deterministic cores are within reach of the existing development
(`VertexSeparation.lean`, `Sandwich.lean`); the probabilistic halves need a G(n, p)
model Mathlib does not have, so they come second, as finite first-moment
inequalities rather than asymptotics.

- [ ] **Brute-force check first** (lesson from the false branch lemma): each
      deterministic core against every graph to 9–10 vertices
      (`learning/pwtw_exhaust.py` has the census), before any Lean.
      *(1)'s core done 2026-10-30: `pw ≥ n − 2 s* − 2` with
      `s* = max_A min(|A| − 1, n − |N[A]|)`, zero violations on all 288,266
      graphs to 9 vertices and all 12,005,168 on 10 (0 violations;
      `reports/scratch/empty_pair/`, survey §1.4). (2) and (3) the same day (`check23.py`): every tree
      to 16 vertices has `pw ≤ ⌊log₃(2N+1)⌋` (all 32,547, zero violations,
      tight at N = 7–12), the complete ternary trees of height 1, 2, 3 have
      pw 1, 2, 3 (C program, refutations), and `pw ≤ n − α` on all 288,266
      graphs to 9 vertices, zero violations. All three cores checked.
      (1)'s core proved in Lean the same day, `EmptyPair.lean`, as a corollary
      of Harper's bound `∀ j ∃ |A| = j, |N[A]| ≤ j + pw` (sorry-free, standard
      axioms); the probabilistic half's *counting* part proved 2026-10-31,
      `FirstMoment.lean`: `P(pw ≤ k) ≤ C(n,t)·C(n−t,t−1)·(1−p)^(t(t−1))` in
      G(n, p), t = ⌈(n−k)/2⌉; the entropy asymptotics done on paper the same
      day (`reports/random_graph_first_moment.md`, Theorems A, A′, A″, B;
      checked by a second agent): `pw ≥ β*(c)·n` whp for `c > 4 ln 2`, with
      the finite form `e^{c/2} n³ e^{−δn}`. Literature: the argument is
      Turner 1986 (bandwidth) and DPST 2001 (vertex separation, crude count);
      the entropy constant, threshold and asymptotics are new; cite both.
      Theorem A and the limit statement are in Lean the same day
      (`FirstMomentAsymptotics.lean`); A′ (the β*(c) characterisation), A″
      and B are not. (3)'s core proved in Lean the
      same day, `IndependenceBound.lean`, `pathwidth ≤ n − indepNum`. (2)'s
      tree bounds proved in Lean the same evening, `TreeBound.lean`, by a prover
      agent with a refuter agent attacking every lemma first (gossip in
      `reports/scratch/tree_bound/gossip.md`): `tree_pathwidth_le_log` (the
      survey's bound), its sharp form `tree_pathwidth_le_treeBound` with
      `treeBound_sharp`, and `pathwidth_ternaryTree`; no counterexample to
      anything, trees exhaustively checked to 26+ vertices. All three
      deterministic cores are now theorems; only the probabilistic halves
      remain, blocked on a G(n, p) model.*
- [ ] **(1) Linear lower bound for average degree c > 4 ln 2 ≈ 2.77.**
      Deterministic core: if vs(G) ≤ k, there are disjoint A, R with
      |A| = |R| ≥ ⌈(n − k)/2⌉ − 1 and no A–R edge (survey §1.4). Then the
      first moment: the expected number of such empty pairs in G(n, c/n)
      vanishes below β*(c)·n, so whp pw ≥ β*(c)·n, beating Perarnau–Serra's
      treewidth bound at every c.
- [ ] **(2) Subcritical c < 1: pw = (1 + o(1)) log₃ log n.** Deterministic
      cores: a tree on N vertices has pw ≤ log₃(2N + 1); the complete ternary
      tree of height h has pw = h (classical, Scheffler; to cite, not claim).
      Probabilistic half: whp every component is a tree or unicyclic of size
      O(log n), and a ternary tree of size Θ(log n) occurs.
- [ ] **(3) Dense, constant p: n − pw = Θ(log n)**, between (2 − o(1)) log_b n
      and (4 + o(1)) log_b n, b = 1/(1 − p), against the published O(√(n/p)).
      Deterministic cores: pw ≤ n − α(G), and the empty-pair lemma of (1).
      Probabilistic half: the independence number and empty-pair first moments.
- [ ] **The large-n theorem first** (medium priority, owner 2026-10-18): the
      route to a real theorem about random graphs at every n is (1)'s
      first moment, "with high probability pw ≥ β*(c)·n", proved by counting,
      not enumeration; the G(n, c/n) measurements (`reports/scratch/gnp_pilot/`)
      test it but cannot prove it. *Pilot done 2026-10-18 and written up
      2026-10-26 in `reports/random_graph_pathwidth_survey.md` §7(d): 6,542
      exact pathwidths, no graph below `β*(c)·n`, fitted slopes 0.08–0.10
      above `β*` at every `c ≥ 3`; the full measurement is priced there.*
- [ ] **Exact E[pw] and Var[pw] of G(n, p) for n ≤ 11** (low priority,
      2026-10-18): exact polynomials in p with integer coefficients, from the
      census of every graph to 11 vertices (`learning/pwtw_exhaust.py`) and
      the count of labelled copies of each class. Computation, not proof.
      In Lean only for n ≤ 5-6, by brute force over the 1,024 / 32,768
      labelled graphs with kernel `decide` (avoid `native_decide`, which
      trusts the compiler), as a small fully verified example.
- [ ] Only after the checks and Lean: decide whether these go in a paper, and
      search once more that none is already published.

## Contributing to SageMath (after the arXiv preprint, 2026-10-16)

SageMath's `vertex_separation` (maintained by David Coudert, first author of the
branch and bound we compare against) is where exact pathwidth users already look.
The Sage hunt (`pathwidth_solver/bench/results/sage_hunt.csv`): of 381 benchmark
graphs, Sage's BAB settled 164 in 600 s; on the 217 it did not, ours proved 104
(loaded machine: to be confirmed by the quiet head-to-head).

- [ ] **Write to David Coudert first**, collegially: the results, the minor bound,
      and whether Sage would welcome the contributions below.
- [ ] **PR 1, small: the contraction-minor lower bound** as a self-contained
      function (Theorem 4.11, Lean: `pathwidth_gt_of_minorOf`), usable by Sage's
      existing BAB at once. Cython, doctests, Sage graph types.
- [ ] **PR 2: our corrected search as a new `algorithm=` option** of
      `vertex_separation`, beside "BAB", "MILP" and "exponential". Port the C engine
      (now called through ctypes) to Cython or a C extension Sage accepts; GPL is
      fine (our code is MIT).
- [ ] **Evidence for the reviewers:** the quiet-machine SageMath head-to-head
      (high-priority item above), and the arXiv preprint to cite.

## Contributing pathwidth to House of Graphs (2026-10-17)

House of Graphs (Coolsaet, D'hondt & Goedgebeur 2022, arXiv:2210.17253;
Devillez, D'hondt & Goedgebeur 2026, arXiv:2603.23070; both in `literature/`)
stores treewidth as an invariant, from a treewidth tester (their ref. [27]), but
**not pathwidth**. The 2026 paper puts treewidth as its second hardest
invariant, timing out on about 20% of graphs (~5,400). They say they prefer fast
compiled implementations.

How contributions work (2026 paper §4.1, §6.1; 2022 paper §6): **users do not
submit invariant values**; the server computes every invariant itself, under
a ~5-minute limit per graph, with invariant programs chosen and reviewed by
hand. They prefer compiled C/C++ with few dependencies and mature, tested
code. The 2022 paper invites "practical and well-tested programs to compute an
interesting graph invariant which is not on the House of Graphs yet".
Contact: Jan Goedgebeur (jan.goedgebeur@kuleuven.be); also Kris Coolsaet
(Ghent), Sven D'hondt, Gauvain Devillez (Mons).

Our evidence (first pass, 2026-10-18, `pathwidth_solver/bench/results/hog_pathwidth.csv`):
all 29,995 graphs at their 5-minute limit, pathwidth proved on 26,432, a
witness layout for every graph, zero conflicts with their treewidth, 1,948
proved where their treewidth timed out. Second pass on the 3,563 running.

- [ ] **A standalone pathwidth program in C** (high priority, today,
      2026-10-18): reads graph6 on stdin, one graph per line; prints the
      pathwidth, whether it is proved (refutation / bound / minor) or an upper
      bound, and a witness layout; a time limit; no Python, no networkx. Port
      the descent of `pathwidth/solve.py`, the bounds of `bounds.py` and the
      minor step of `minor.py` around the existing C engine
      (`closing_search.c`). Must reproduce the Python solver's widths.
- [ ] **Draft the email to Goedgebeur** (high priority, today): the program,
      the first-pass numbers above, the witness file, the paper. Send after
      the arXiv preprint, so they have something to cite.
- [ ] **Offer our values as a cross-check**, not a substitute: the server
      recomputes, and our witnesses let them verify every upper bound.
- [ ] Companion to the SageMath contributions above.

## W4: search for a width-26 layout (2026-10-15)

- [ ] **Try the finding side on W4** (VLSI, 202 nets, dataset class pwc-04432;
      26 <= pw <= 27, i.e. 27 or 28 tracks). The two running attempts
      (`reports/scratch/w4/`) both try to refute 26; after 2.5 days nothing
      found suggests 27 is optimal but proves nothing. A dedicated layout search
      for width 26 (simulated annealing as for myciel7,
      `reports/scratch/minor_certificates/vsanneal.c`, or restricted searches
      from varied orders), one core, an hour or two, when cores are free: a
      width-26 layout settles W4 at 26 (27 tracks); none adds evidence for 27.

## A parameterised bound for our search (high priority, 2026-10-14)

- [ ] **Can our corrected search be proved FPT, or at least XP, in the width k,
      and does it improve on what is known?** Empirically, on the Rome graphs,
      nodes ~ 10^(1.75 + 0.00705 n w) (Section 5, Figure 5.1): exponential in
      n*w, not fixed-parameter. Theory: Bodlaender & Kloks (1996) decide
      pathwidth <= k in linear time with a 2^O(k^3) constant
      (`reports/fpt_theory_practice_gap.md`); later improvements exist (Fuerer
      and others) and must be checked before any claim. Steps:
      1. survey the parameterised pathwidth literature for the current best
         bounds (FPT and XP), with what we hold and what to fetch;
      2. bound our search's state space: its states are vertex sets S with
         |N(S) \ S| <= k, each fixed by its boundary and a choice of the
         components of G - N[S] it contains, which suggests an n^O(k) (XP)
         bound; prove it, and check it on small graphs first;
      3. ask whether the corrected dominance rules (and the minor step) cut
         the state space to f(k) * poly(n), which would be FPT; a new idea
         would be needed, so scope it before investing;
      4. if a theorem results, formalise it in Lean beside Search/ and decide
         whether it belongs in this paper or in paper 2.

## The grid theorem in Lean (high priority, 2026-10-14)

- [x] **Done 2026-10-14** (`lean/MOSPFormalization/Grid.lean`, `pathwidth_grid`, commit cda02ac3b; 1x1 is the one exception, pathwidth 0; in the paper as Appendix A `grid`). **Prove in Lean that an (h, w)-grid has pathwidth min(h, w)** (Ellis &
      Warren 2008, Theorem 4.1, via node search: Lemma 4.1, the sweep, gives
      ns <= min(h, w) + 1; Lemma 4.2 the lower bound). 41 VSPLIB grids (sides
      14-54) are now settled by citing this theorem
      (`reports/scratch/grids_theorem/grids.csv`, each grid checked by
      isomorphism, each witness layout checked); with the Lean proof they rest
      on Lean like the rest of the paper. The upper bound is the row-by-row
      layout; the lower bound is the hard half (Ellis & Warren's search
      argument, or a separator / isoperimetric argument, or the grid minor
      structure). Check the statement on small grids first, as usual. Then give
      the dataset a provenance for it (e.g. `certified:theorem`, citing the Lean
      name) and update Table 5.2's grid row.

## From the owner's annotations (2026-10-13)

- [ ] **Lean: the certificate checker's acceptance condition** (medium priority). The checker
      (Section 5.4) accepts a refutation when every discarded move is justified
      by a checked step and the justifications are acyclic. That this makes the
      certificate a proof is argued on paper only (conclusion, Limits). Formalise
      it beside `lean/MOSPFormalization/Search/`.
- [ ] **Read every citer in full.** Of the 38 works citing the CP paper 24 were
      read in full, and of the 103 citing only the thesis, 32 (Appendix B,
      prior reports). Read the remaining 14 + 71: obtain the open ones, list the
      rest for fetching, and record any mention of the definite move's error.

## A replication notebook

- [ ] **"This entire paper can be read and replicated on a Python (with C calls)
      Jupyter notebook."** One notebook that follows the paper section by section:
  - the worked example of Figure 1.1;
  - the equivalences checked by brute force on small graphs (`complex_check.py`);
  - the census of names (from the cached OpenAlex data);
  - the counterexample and the repaired search (Python reference and the C
    through `native.py`);
  - the 34-customer wrong optimum with both searches, the SAT check and the DRAT
    check;
  - the cost tables, the re-certification records and the dataset checker.

  Every number and figure is regenerated from the recorded data, with the
  expensive runs (the split refutations, the full benchmarks) read from their
  CSVs rather than rerun. It ships in the paper's repository, and the paper
  says so in its "Data, code and proofs" statement.

## Data and proofs

- [x] **The trimmed DRAT proof for the 34-customer instance** (2026-10-11):
      `data/false_refutation/drat/false_refutation_34__k5.core.drat.xz`, 27 MB,
      with its SHA-256 and `check_proof.sh` (rebuilds the CNF, `s VERIFIED` in 35 s).
- [x] **The never-certified MOSP values** (closed 2026-10-12). `Random-125-125-2-3_0`
      = 21 certified 2026-10-09 (k = 20 refuted, 9,665 tasks, 1,128 core-hours);
      `Random-125-125-2-2_0` = 25 certified 2026-10-12 (k = 24 refuted, 17,001
      tasks, 7.38 × 10¹² nodes, 2,231 core-hours). Both provenances upgraded;
      the corpus is 6,376 of 6,376; dataset and paper updated.
- [ ] **Open question: can the published rules fail with the better move
      on?** The 34-customer instance fails only with the better move off.
      Restart `false_refutation_hunt.py` with fitness on the better-move
      configurations if we want the answer.

## Bug: legacy pathwidth_fpt on trees (found 2026-10-18)

- [ ] **`fixed_parameter_algorithm/pathwidth_fpt.compute_pathwidth_fpt` returns
      pathwidth 1 for every tree over 18 vertices** (e.g. `balanced_tree(3, 3)`,
      pathwidth 3). Found by the random-intersection report's agent, not yet
      reproduced or fixed. Below 19 vertices it delegates to the exact DP, so the
      fault is in the branch and bound or its pendant-removal preprocessing
      (removing degree-1 vertices does not preserve pathwidth on trees). Not
      used by `pathwidth_solver/` or any paper result; check what still calls it
      (`customer_inter/`, tests) and add a tree regression test.

## Repository housekeeping

- [ ] **Apply item 09's proposed `CLAUDE.md` blocks** (`solver_fix.md`, "For
      CLAUDE.md"), and record the wrong-optimum instance, Appendix D and the
      DRAT proof in `CLAUDE.md`.
- [ ] **Push** (`git status` before each push).
- [x] **Two new rows in Table 1.1** (2026-10-09): the vertex search of Bienstock,
      Robertson, Seymour & Thomas (1991) and the maximum wavefront of Kumfert &
      Pothen (1997, proved in Lean, `Complex/Wavefront.lean`); Figure 2.1 redrawn.

## Paper 2 (idea, 2026-10-09)

- [ ] **Read the four surveys** in `paper2/` (trees and sparse classes; products
      and grids; intersection and perfect classes; random and extremal results)
      when they arrive, and decide whether there is a paper in "the applied
      mathematics of pathwidth on special graph classes".
