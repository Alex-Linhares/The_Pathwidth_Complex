# The seeded tabu search over minors on the open dataset classes (2026-11-07)

Driver `pathwidth_solver/bench/minor_tabu_open.py`, program `pathwidth_solver/cli/minor_tabu.c`
(Appendix G of paper 1; the certificates are proved sound in `lean/MOSPFormalization/Search/MinorTabu.lean`).
Every class is seeded from its best minor certificate on record (`obstruction_search/13_pass1/certificates_2/<id>/minor.json`),
floor = the certified level, target = the recorded width; budgets 40 / 80 / 120 CPU minutes by width-minus-floor gap,
8 workers at nice 19; ties random within the band; every neighbour refutation logged.

- `ledger.csv`, `<id>.json`, `<id>.err`: run 1, 03:50 to 10:30, 91 classes, 48 core-hours, **0 closed, 0 raised**.
  42 of the 91 stopped at step 1: their seed minor has more than 120 vertices, the exact-step cap (`-m 120`),
  so the size band was empty (`run1_capped/skipped_by_cap.txt`); they are re-run with the cap lifted
  (`--max-exact 1000`, `ledger_uncapped.csv`, `run_uncapped.out`).
- `claims_summary.csv`: per class, the neighbour refutations logged (level = the floor's or the target's),
  their minor sizes, and the count by size. **243,310 refutations of the floor's level on 26 classes, 0 of the
  target level on any class.** The raw logs `<id>.claims.jsonl` (367 MB; one JSON line per refutation with the
  contraction sequence, replayable by `pathwidth_solver/bench/minor_tabu_claims.py`) and the checkpoints
  `<id>.last` / `<id>.seed` are kept on disk and git-ignored.
- `superseded_tiebreak/`: the first launch (02:00 to 03:50) under the "largest minor" tie-break, 16 classes, not comparable.
- `ledger_uncapped.csv`, `run_uncapped.out`: the re-run of the 42 capped classes with `--max-exact 1000`, 10:37 to
  the owner's stop at about 15:30: 29 finished, 0 closed, 0 raised; the 13 others were interrupted
  (their checkpoints `<id>.last` hold the walks' last state; `--restart` resumes them). Floor-level claims on 14 of
  the 42, none of the target level.
