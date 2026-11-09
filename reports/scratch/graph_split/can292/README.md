# can_292 (Harwell–Boeing, 292 vertices, 1,124 edges): pathwidth 22, closed 2026-11-09

The dataset recorded an upper bound of 23 (provenance `solution`). The rebuilt program
(`pathwidth_solver/cli/pathwidth`, memo table cap 2 GB, memo limit 64M, default rules) found a
layout of width 22 and refuted 21 on a 146-vertex contraction minor (rule least-c), in 23 s on one
core (`pathwidth_output.txt`: `pathwidth 22 minor`, the layout, the certificate line). It was the one
graph proved among the 34 the stopped one-core rerun of the 70 "neither" graphs reached.

- `instance.txt`: the graph as `n m` + edges (from the benchmark file through `bench/readers.py`).
- `minor.json`: the certificate in the `obstruction-minor-1` format; **verified** by
  `paper1/obstruction_check.py check-minor` (replay, quotient, hashes, floor, and the C re-proof of
  pathwidth(minor) >= 22 in 1.14 s; the rule-free check applies only to minors of <= 80 vertices).
- The layout's vertex separation is 22 by `pathwidth_solver/bench/graph_split.vertex_separation`.

So pw(can_292) = 22. The dataset row (`pwc-04542`) still says `solution 23`; the rebuild is on
`paper1/todo.md` (with BalancedTree_3_5 and the pass-2 closures).
