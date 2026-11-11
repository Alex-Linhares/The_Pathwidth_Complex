"""The C program from the best sweep layout of one cage: -u <closing order> -t 600 -l -v."""
import json, sys
from pathlib import Path
from learning.gaspers_sweep import load_record, run_c, adjacency, vertex_separation
rid, seconds = sys.argv[1], int(sys.argv[2])
src = Path("reports/scratch/gaspers_cages/sweep20k") / f"{rid}_sweep_layout.txt"
layout = [int(x) for x in src.read_text().split()]
r = load_record(rid)
edges = [tuple(e) for e in r["edges"]]
w0 = vertex_separation(adjacency(r["n"], edges), layout)
c = run_c(r["n"], edges, layout, seconds, Path("reports/scratch/gaspers_cages/c600"), rid)
print(json.dumps({"id": rid, "sweep_width": w0, "c_width": c.get("width"), "c_status": c.get("status"),
                  "c_checked": c.get("checked_width"), "seconds": round(c["seconds"], 1), "stderr": c["stderr"].strip()}))
