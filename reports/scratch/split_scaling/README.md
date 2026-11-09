# The root split on graphs: speed-up measurements (2026-11-09)

`pathwidth_solver/bench/split_scaling.py`; rows in `pathwidth_solver/bench/results/split_scaling.csv`;
task rows per run under `<id>_p<p>/tasks.csv`. All at nice 19; the machine carried other work (load in the rows).

- **grafo8793.100** (Rome, 100 vertices, width 10): the full series — sequential (memo on) and the same 87-task
  decomposition on 1, 2, 4, 8, 16 workers (`run_sixfold_graph1.out`). Nodes identical at every worker count.
- **grafo11458.100**, **atco_enc2_opt2_10_21 Gaifman graph**, **Higman–Sims**: one run each, 16 workers
  (`run.out`, `run_hs.out`); the one-core reference is the dataset's recorded run (evidence `nodes=, s=`).
- **Random-200-200-10-5** crashed: the native split (`cs_split_expand` / `cs_split_decide`) exists only for the
  two-word engine, at most 128 customers (`satisfiability/native.py`); replaced by Higman–Sims. `graph_split.py`
  now filters at 128 vertices.
- **The memo** (`memo_diag.out`, `memo_limit.out`): memo off, sequential = split = 9.021e8 nodes on grafo8793.100
  (as `Search/Split.lean` says); memo on, sequential 8.42e8 but the 87 tasks with a fresh 4M-entry memo each
  1.19e8 — the single memo saturates on a hard refutation; the memo-limit sweep on the sequential run says how much
  of the split's gain is memory rather than parallelism.
