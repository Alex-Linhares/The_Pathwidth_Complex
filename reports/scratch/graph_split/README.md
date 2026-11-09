# The root split on graphs: the Foster run (2026-11-09 01:45 to 12:05, stopped by the owner)

Driver `pathwidth_solver/bench/graph_split.py` (the adapter: one customer per vertex, one pattern per edge,
so the customer graph is G and a refutation of MOSP <= k proves pw >= k; the split of
`paper1/solver_fix_split.py`, proved sound in `Search/Split.lean`). Target: the dataset's open classes,
smallest first; the first was the Foster graph (90 vertices, cubic, recorded width 20), refuting k = 20.

Stopped after about 10 h 20 min on 16 workers at nice 19: no root subtree of the 90 finished; the 16 opened
had absorbed 7 x 10^11 nodes and every one was split further; about 150 core-hours. Section 5's cost law
(log10 nodes = 1.75 + 0.00705 n w) predicts 10^14.4 nodes for this refutation, about 2,000 core-days, and
at least 10^14 for every other open class; the run's progress is consistent with the law. The owner stopped
it and moved the cores elsewhere. `tasks.csv` holds every expansion and task (resumable with
`--only pwc-15968`); `run.out` the log. No class closed; nothing written to the dataset or `solutions/`.
