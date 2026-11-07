"""The size of a blockage, measured: the minimum number of minimal big sets over
every blockage of a given order, on every small connected graph and on a few
structured families.

A blockage of order ``k`` (Bienstock, Robertson, Seymour & Thomas 1991, the ``≤ k``
reading of `lean/MOSPFormalization/Blockage.lean`) is a family ``B`` of vertex sets
with

  (i)   every ``X ∈ B`` has ``|att X| ≤ k`` (``att X`` = vertices of ``X`` with a
        neighbour outside ``X``);
  (ii)  ``X ∈ B``, ``Y ⊆ X``, ``|att Y| ≤ k`` ⇒ ``Y ∈ B``;
  (iii) for every complementary pair (``X₁ ∪ X₂ = V``, ``att X₁ ⊆ X₂``) with
        ``|X₁ ∩ X₂| ≤ k``, exactly one of ``X₁``, ``X₂`` is in ``B``.

Write ``Sm = {X : |att X| ≤ k}``. By (ii) the non-members inside ``Sm`` form an
up-set of the poset ``(Sm, ⊆)``, and ``B`` is determined by its ⊆-minimal
elements, the *frame*. Three sizes of one blockage:

  size₁(B) = |frame|: the number of ⊆-minimal sets of ``Sm \\ B``
             (the ``minimal big sets'' for ``big`` := up-closure of ``Sm \\ B``);
  size₂(B) = the least number of generators ``g₁..g_r`` (any vertex sets) with
             ``Sm \\ B = {X ∈ Sm : some g_i ⊆ X}`` — the shortest generator list;
  size₃(B) = the number of ⊆-maximal members of ``B``.

The module computes ``min_B size(B)`` over all blockages of order ``k`` by an exact
SAT model whose variables are the memberships ``b_X`` (``X ∈ Sm``) and whose
constraints are a system equivalent to (i)–(iii):

  down-closure  (ii), through auxiliaries ``e_Z`` = "every ``Sm``-subset of ``Z``
                is a member" over all ``Z ⊆ V``;
  step closure  ``X ∈ B``, ``v ∉ X``, ``|att X| < k`` ⇒ ``X ∪ {v} ∈ B``
                (BRST Lemma (2.2) in single steps; multi-vertex steps compose);
  minimal pairs ``b_X xor b_{X^c}`` for ``X ∈ Sm``, ``X^c = (V \\ X) ∪ att X``.

(iii) for *every* pair follows: if both sides are in ``B`` then ``X₁^c ⊆ X₂`` is a
member by (ii), against the minimal pair; if neither, ``X₂^c ∈ B`` and
``(X₁ \\ X₂^c) ∪ att X₂^c ⊆ X₁ ∩ X₂`` lets the step closure climb to ``X₁``.
Conversely every blockage satisfies all three (the minimal pairs are pairs; the
step is Lemma (2.2)). The equivalence is also checked against the all-pairs
checker of `learning.blockage_class` and against two brute-force enumerations
(every family to 4 vertices, every up-set to 5) in `tests/test_blockage_size.py`.

Stages (``python3 -m learning.blockage_size --stage ...``):

  census   every connected graph on ≤ ``--max-n`` vertices (atlas to 7, nauty-geng
           above): ``pw``, ``tw``, and the minimum of size₁ (size₂, size₃ when
           ``--alt``) at every order 1..pw;
  named    the named graphs and families: minimum size₁ at orders ``pw``,
           ``pw − 1``, … with a time budget, exact or bracketed, and the frame of
           the order-``pw`` minimiser;
  report   the tables of `reports/blockage_size.md` from the CSVs.

Only the C treewidth DP of `learning.treewidth`, the bitmask pathwidth DP of
`learning.blockage_class` (≤ 18 vertices) and pysat's CaDiCaL are used; nothing
touches `solutions/`.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import os
import random
import sys
import threading
import time
from multiprocessing import Pool
from pathlib import Path

from learning.blockage_class import (  # noqa: F401  (re-exported helpers)
    adj_from_edges, adj_from_nx, att_in, bits, complementary_pairs, is_blockage_in,
    is_connected, pathwidth_exact, popcount, subsets_of,
)

ROOT = Path(__file__).resolve().parent.parent
SCRATCH = ROOT / "reports" / "scratch" / "blockage_size"
SOLVER = "cadical153"
TIMED_SOLVER = "glucose4"


# ----------------------------------------------------------------------------
# attachments on the whole vertex set
# ----------------------------------------------------------------------------


def full_mask(adj: list[int]) -> int:
    return (1 << len(adj)) - 1


def att(adj: list[int], X: int) -> int:
    return att_in(adj, full_mask(adj), X)


def alpha_table(adj: list[int]) -> list[int]:
    """``|att X|`` for every ``X ⊆ V``, indexed by bitmask."""
    n = len(adj)
    full = (1 << n) - 1
    out = [0] * (1 << n)
    for X in range(1 << n):
        outside = full & ~X
        c = 0
        Y = X
        while Y:
            b = Y & -Y
            v = b.bit_length() - 1
            if adj[v] & outside:
                c += 1
            Y ^= b
        out[X] = c
    return out


def small_sets(adj: list[int], k: int, alpha: list[int] | None = None) -> list[int]:
    alpha = alpha_table(adj) if alpha is None else alpha
    return [X for X in range(1 << len(adj)) if alpha[X] <= k]


def frame_of(adj: list[int], k: int, members: set[int], alpha: list[int] | None = None) -> list[int]:
    """The ⊆-minimal sets of ``Sm \\ members`` (recomputed from the family, not from
    the solver's indicator variables)."""
    alpha = alpha_table(adj) if alpha is None else alpha
    non = [X for X in range(1 << len(adj)) if alpha[X] <= k and X not in members]
    nonset = set(non)
    out = []
    for X in non:
        minimal = True
        for Y in subsets_of(X):
            if Y != X and Y in nonset:
                minimal = False
                break
        if minimal:
            out.append(X)
    return out


def maximal_members(adj: list[int], k: int, members: set[int], alpha: list[int] | None = None) -> list[int]:
    alpha = alpha_table(adj) if alpha is None else alpha
    n = len(adj)
    full = (1 << n) - 1
    out = []
    for X in members:
        maximal = True
        rest = full & ~X
        for Y in subsets_of(rest):
            if Y and (X | Y) in members:
                maximal = False
                break
        if maximal:
            out.append(X)
    return out


def generators_cover(adj: list[int], k: int, members: set[int], gens: list[int],
                     alpha: list[int] | None = None) -> bool:
    """``Sm \\ members == {X ∈ Sm : some g ⊆ X}``."""
    alpha = alpha_table(adj) if alpha is None else alpha
    for X in range(1 << len(adj)):
        if alpha[X] > k:
            continue
        covered = any((g & ~X) == 0 for g in gens)
        if covered == (X in members):
            return False
    return True


# ----------------------------------------------------------------------------
# the SAT model
# ----------------------------------------------------------------------------


class BlockageCNF:
    """The exact model of the blockages of order ``k`` of ``adj``, with indicator
    variables for the minimal non-members (``m``), the maximal members (``M``,
    optional) and a generator list (``u``, optional, ``n ≤ 10``)."""

    def __init__(self, adj: list[int], k: int, want_maximal: bool = False,
                 want_generators: bool = False):
        self.adj = adj
        self.k = k
        self.n = n = len(adj)
        self.full = full = (1 << n) - 1
        self.alpha = alpha = alpha_table(adj)
        self.sm = sm = [X for X in range(1 << n) if alpha[X] <= k]
        self.in_sm = in_sm = [a <= k for a in alpha]
        nxt = 1
        self.b = b = {}
        for X in sm:
            b[X] = nxt
            nxt += 1
        self.e = e = list(range(nxt, nxt + (1 << n)))
        nxt += 1 << n
        self.m = m = {}
        for X in sm:
            m[X] = nxt
            nxt += 1
        cl = []
        self.clauses = cl
        # e_Z <-> (Z ∉ Sm ∨ b_Z) ∧ ⋀_{v∈Z} e_{Z\v}
        for Z in range(1 << n):
            long = [e[Z]]
            if in_sm[Z]:
                cl.append([-e[Z], b[Z]])
                long.append(-b[Z])
            for v in bits(Z):
                cl.append([-e[Z], e[Z ^ (1 << v)]])
                long.append(-e[Z ^ (1 << v)])
            cl.append(long)
        for X in sm:
            # (ii): b_X -> e_{X\v}
            for v in bits(X):
                cl.append([-b[X], e[X ^ (1 << v)]])
            # step closure
            if alpha[X] < k:
                rest = full & ~X
                for v in bits(rest):
                    cl.append([-b[X], b[X | (1 << v)]])
            # minimal pair
            Xc = (full & ~X) | att_in(adj, full, X)
            if Xc >= X:
                cl.append([b[X], b[Xc]])
                cl.append([-b[X], -b[Xc]])
            # m_X <-> ¬b_X ∧ ⋀_{v∈X} e_{X\v}
            long = [m[X], b[X]]
            cl.append([-m[X], -b[X]])
            for v in bits(X):
                cl.append([-m[X], e[X ^ (1 << v)]])
                long.append(-e[X ^ (1 << v)])
            cl.append(long)
        self.M = None
        if want_maximal:
            f = list(range(nxt, nxt + (1 << n)))
            nxt += 1 << n
            self.M = M = {}
            for X in sm:
                M[X] = nxt
                nxt += 1
            # f_Z <-> (Z ∉ Sm ∨ ¬b_Z) ∧ ⋀_{v∉Z} f_{Z∪v}
            for Z in range(1 << n):
                long = [f[Z]]
                if in_sm[Z]:
                    cl.append([-f[Z], -b[Z]])
                    long.append(b[Z])
                for v in bits(full & ~Z):
                    cl.append([-f[Z], f[Z | (1 << v)]])
                    long.append(-f[Z | (1 << v)])
                cl.append(long)
            for X in sm:
                long = [M[X], -b[X]]
                cl.append([-M[X], b[X]])
                for v in bits(full & ~X):
                    cl.append([-M[X], f[X | (1 << v)]])
                    long.append(-f[X | (1 << v)])
                cl.append(long)
        self.u = None
        if want_generators:
            if n > 14:
                raise ValueError("the generator model enumerates 3^n pairs; n ≤ 14")
            self.u = u = list(range(nxt, nxt + (1 << n)))
            nxt += 1 << n
            for X in sm:
                long = [b[X]]
                for g in subsets_of(X):
                    long.append(u[g])
                    cl.append([-b[X], -u[g]])
                cl.append(long)
        self.top = nxt - 1

    # -- solving ------------------------------------------------------------

    def members_of(self, model: list[int]) -> set[int]:
        pos = set(l for l in model if l > 0)
        return {X for X in self.sm if self.b[X] in pos}

    def minimise(self, kind: str = "frame", time_limit: float | None = None,
                 solver: str | None = None) -> dict:
        """``min size(B)`` over the blockages of order ``k``; ``kind`` is ``frame``
        (size₁), ``maximal`` (size₃) or ``generators`` (size₂).

        Returns ``status`` ∈ {``none`` (no blockage: ``pw < k``), ``exact``,
        ``bounded``, ``censored``}, ``lb``, ``ub``, ``value`` (when exact), the
        witness ``members`` of the best blockage found and its recomputed
        ``frame``, and the seconds used."""
        from pysat.card import ITotalizer
        from pysat.solvers import Solver

        if kind == "frame":
            lits = [self.m[X] for X in self.sm]
        elif kind == "maximal":
            lits = [self.M[X] for X in self.sm]
        elif kind == "generators":
            lits = [self.u[g] for g in range(1, 1 << self.n)]
        else:
            raise ValueError(kind)
        t0 = time.time()
        deadline = None if time_limit is None else t0 + time_limit
        if solver is None:
            # pysat's CaDiCaL cannot be interrupted; time-limited runs use Glucose 4
            solver = SOLVER if time_limit is None else TIMED_SOLVER

        def solve(s, assumptions=()):
            if deadline is None:
                return s.solve(assumptions=list(assumptions))
            left = deadline - time.time()
            if left <= 0:
                return None
            timer = threading.Timer(left, s.interrupt)
            timer.start()
            try:
                r = s.solve_limited(assumptions=list(assumptions), expect_interrupt=True)
            finally:
                timer.cancel()
            s.clear_interrupt()
            return r

        out = dict(kind=kind, k=self.k, n=self.n, status="censored", lb=1, ub=None,
                   value=None, members=None, frame=None, seconds=0.0, calls=0)
        with Solver(name=solver, bootstrap_with=self.clauses) as s:
            r = solve(s)
            out["calls"] += 1
            if r is False:
                out.update(status="none", lb=None, ub=None)
                out["seconds"] = time.time() - t0
                return out
            if r is None:
                out["seconds"] = time.time() - t0
                return out
            model = s.get_model()
            pos = set(l for l in model if l > 0)
            best = sum(1 for l in lits if l in pos)
            out["members"] = self.members_of(model)
            out["ub"] = best
            lb = 1
            if best > lb:
                tot = ITotalizer(lits=lits, ubound=best - 1, top_id=self.top)
                s.append_formula(tot.cnf.clauses)
                while lb < best:
                    target = (lb + best - 1) // 2      # ask for ≤ target
                    r = solve(s, [-tot.rhs[target]])
                    out["calls"] += 1
                    if r is None:
                        break
                    if r is False:
                        lb = target + 1
                    else:
                        model = s.get_model()
                        pos = set(l for l in model if l > 0)
                        best = sum(1 for l in lits if l in pos)
                        out["members"] = self.members_of(model)
            out["lb"] = lb
            out["ub"] = best
            if lb == best:
                out["status"] = "exact"
                out["value"] = best
            else:
                out["status"] = "bounded"
        out["frame"] = frame_of(self.adj, self.k, out["members"], self.alpha)
        if kind == "generators":
            out["generators"] = [g for g in range(1, 1 << self.n) if self.u[g] in pos]
        out["seconds"] = time.time() - t0
        return out


def min_size(adj: list[int], k: int, kind: str = "frame", time_limit: float | None = None) -> dict:
    cnf = BlockageCNF(adj, k, want_maximal=(kind == "maximal"), want_generators=(kind == "generators"))
    return cnf.minimise(kind, time_limit=time_limit)


# ----------------------------------------------------------------------------
# independent checks: the raw axioms, and brute force
# ----------------------------------------------------------------------------


def is_blockage(adj: list[int], k: int, members: set[int]) -> bool:
    """Axioms (i)–(iii) on every pair, through the all-pairs checker of
    `learning.blockage_class` (no clause of the SAT model is used)."""
    ok, _ = is_blockage_in(adj, full_mask(adj), k, lambda X: X in members)
    return ok


def upsets(n: int):
    """Every up-set of the Boolean lattice on ``n`` points, as a set of bitmasks
    (Dedekind's count: 2, 3, 6, 20, 168, 7581 for n = 0..5)."""
    order = sorted(range(1 << n), key=popcount)
    chosen: set[int] = set()

    def rec(i: int):
        if i == len(order):
            yield set(chosen)
            return
        Z = order[i]
        forced = any((Z ^ (1 << v)) in chosen for v in bits(Z))
        if not forced:
            yield from rec(i + 1)
        chosen.add(Z)
        yield from rec(i + 1)
        chosen.discard(Z)

    yield from rec(0)


def brute_force_min_frame_upsets(adj: list[int], k: int) -> int | None:
    """``min size₁`` over all blockages by enumerating every up-set ``U`` of ``2^V``
    and testing ``B = Sm \\ U`` against the raw axioms (``n ≤ 5``)."""
    n = len(adj)
    alpha = alpha_table(adj)
    sm = set(X for X in range(1 << n) if alpha[X] <= k)
    pairs = list(complementary_pairs(adj, full_mask(adj), k))
    best = None
    for U in upsets(n):
        members = sm - U
        ok = True
        for X1, X2 in pairs:
            if (X1 in members) == (X2 in members):
                ok = False
                break
        if not ok:
            continue
        # (i) and (ii) hold by construction (members ⊆ Sm; U is an up-set)
        size = len(frame_of(adj, k, members, alpha))
        if best is None or size < best:
            best = size
    return best


def brute_force_min_frame_families(adj: list[int], k: int) -> int | None:
    """``min size₁`` by enumerating *every* family of subsets of ``V`` and testing
    the three axioms (``n ≤ 4``: 2^16 families)."""
    n = len(adj)
    alpha = alpha_table(adj)
    pairs = list(complementary_pairs(adj, full_mask(adj), k))
    best = None
    for fam in range(1 << (1 << n)):
        members = {X for X in range(1 << n) if (fam >> X) & 1}
        if any(alpha[X] > k for X in members):
            continue
        ok = True
        for X in members:
            for Y in subsets_of(X):
                if alpha[Y] <= k and Y not in members:
                    ok = False
                    break
            if not ok:
                break
        if not ok:
            continue
        for X1, X2 in pairs:
            if (X1 in members) == (X2 in members):
                ok = False
                break
        if not ok:
            continue
        size = len(frame_of(adj, k, members, alpha))
        if best is None or size < best:
            best = size
    return best


# ----------------------------------------------------------------------------
# graphs
# ----------------------------------------------------------------------------


def graph6_of(adj: list[int]) -> str:
    import networkx as nx

    g = nx.Graph()
    g.add_nodes_from(range(len(adj)))
    for v in range(len(adj)):
        for u in bits(adj[v]):
            if u > v:
                g.add_edge(v, u)
    return nx.to_graph6_bytes(g, header=False).decode().strip()


def adj_of_graph6(text: str) -> list[int]:
    import networkx as nx

    return adj_from_nx(nx.from_graph6_bytes(text.strip().encode()))


def connected_graphs(n: int):
    """Every connected graph on ``n`` vertices: the atlas to 7, nauty-geng above."""
    if n <= 7:
        from networkx.generators.atlas import graph_atlas_g

        for g in graph_atlas_g():
            if g.number_of_nodes() == n:
                adj = adj_from_nx(g)
                if is_connected(adj, full_mask(adj)):
                    yield adj
        return
    import subprocess

    proc = subprocess.run(["nauty-geng", "-cq", str(n)], capture_output=True, text=True, check=True)
    for line in proc.stdout.splitlines():
        if line.strip():
            yield adj_of_graph6(line)


def treewidth_of(adj: list[int]) -> int:
    from learning.treewidth import treewidth_exact

    return treewidth_exact(adj)[0]


def pathwidth_of(adj: list[int]) -> int:
    if len(adj) <= 18:
        return pathwidth_exact(adj)
    import subprocess

    proc = subprocess.run([str(ROOT / "pathwidth_solver" / "cli" / "pathwidth"), "-t", "600"],
                          input=graph6_of(adj) + "\n", capture_output=True, text=True, check=True)
    tok = proc.stdout.split()
    if tok[2] != "proved" and tok[2] != "exact":
        raise RuntimeError(f"pathwidth not proved: {proc.stdout}")
    return int(tok[1])


TEN_VERTEX_PWTW2 = [
    "0 0 1 0 0 0 1 1 0", "0 0 0 0 0 0 1 0 0", "1 0 1 0 0 0 0 0 0", "0 0 1 0 1 1 0 0 0",
    "0 0 0 0 1 1 0 0 1", "0 0 0 0 0 1 0 0 0", "1 0 0 1 0 0 0 0 1", "0 0 1 0 0 0 0 0 0",
    "0 0 0 1 0 0 1 0 0", "0 1 0 0 1 1 1 0 0",
]


def ten_vertex_graph() -> list[int]:
    """The 10-vertex graph with ``pw − tw = 2`` of `reports/ml_nature.md` §21
    (three K4s glued at three hubs, one vertex tied to a non-hub of each): its
    MOSP graph, from the 10 × 9 matrix recorded there."""
    rows = [[int(c) for c in r.split()] for r in TEN_VERTEX_PWTW2]
    n = len(rows)
    adj = [0] * n
    for col in range(len(rows[0])):
        members = [i for i in range(n) if rows[i][col]]
        for i in members:
            for j in members:
                if i != j:
                    adj[i] |= 1 << j
    return adj


def clebsch_graph():
    """The folded 5-cube: Q4 plus the antipodal matching; 5-regular, 16 vertices."""
    import networkx as nx

    g = nx.convert_node_labels_to_integers(nx.hypercube_graph(4), ordering="sorted")
    nodes = sorted(nx.hypercube_graph(4).nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    for v in nodes:
        w = tuple(1 - x for x in v)
        g.add_edge(idx[v], idx[w])
    return g


def shrikhande_graph():
    """Cayley graph of Z4 x Z4 with connection set ±(1,0), ±(0,1), ±(1,1); 6-regular."""
    import networkx as nx

    g = nx.Graph()
    for a in range(4):
        for b in range(4):
            for da, db in ((1, 0), (0, 1), (1, 1)):
                g.add_edge(4 * a + b, 4 * ((a + da) % 4) + (b + db) % 4)
    return g


def named_graphs() -> list[tuple[str, list[int]]]:
    import networkx as nx

    out = []

    def add(name, g):
        out.append((name, adj_from_nx(nx.convert_node_labels_to_integers(g))))

    add("P3", nx.path_graph(3))
    for k in (3, 4, 5, 6, 7, 8):
        add(f"K{k}", nx.complete_graph(k))
    for k in (4, 5, 6, 8, 10):
        add(f"C{k}", nx.cycle_graph(k))
    for k in (3, 4, 5, 8):
        add(f"grid2x{k}", nx.grid_2d_graph(2, k))
    add("grid3x3", nx.grid_2d_graph(3, 3))
    add("grid3x4", nx.grid_2d_graph(3, 4))
    add("grid4x4", nx.grid_2d_graph(4, 4))
    add("spider3x2", nx.from_edgelist([(0, 1), (1, 2), (0, 3), (3, 4), (0, 5), (5, 6)]))
    add("bintree_h2", nx.balanced_tree(2, 2))
    add("bintree_h3", nx.balanced_tree(2, 3))
    add("tertree_h2", nx.balanced_tree(3, 2))
    add("Petersen", nx.petersen_graph())
    add("Mycielski3", nx.mycielski_graph(3))
    add("Mycielski4", nx.mycielski_graph(4))
    for k in (2, 3, 4, 5, 6, 7, 8):
        add(f"K{k},{k}", nx.complete_bipartite_graph(k, k))
    out.append(("pwtw2_10", ten_vertex_graph()))
    add("Heawood", nx.heawood_graph())
    add("MoebiusKantor", nx.moebius_kantor_graph())
    add("Q4", nx.hypercube_graph(4))
    add("Clebsch", clebsch_graph())
    add("Paley13", nx.paley_graph(13).to_undirected())
    add("Shrikhande", shrikhande_graph())
    for n in (8, 10, 12, 14, 16, 18):
        for seed in range(3):
            g = nx.random_regular_graph(3, n, seed=seed)
            if not nx.is_connected(g):
                continue
            add(f"cubic{n}_s{seed}", g)
    for n in (10, 12, 14, 16):
        for seed in range(2):
            g = nx.random_regular_graph(4, n, seed=seed)
            if not nx.is_connected(g):
                continue
            add(f"quartic{n}_s{seed}", g)
    for n in (12, 16):
        g = nx.random_regular_graph(5, n, seed=0)
        if nx.is_connected(g):
            add(f"quintic{n}_s0", g)
    return out


# ----------------------------------------------------------------------------
# the census (≤ 9 vertices)
# ----------------------------------------------------------------------------


def census_row(adj: list[int], alt: bool = False) -> dict:
    n = len(adj)
    pw = pathwidth_exact(adj)
    tw = treewidth_of(adj)
    sizes1, sizes2, sizes3, frames = [], [], [], []
    for k in range(1, pw + 1):
        r = min_size(adj, k, "frame")
        assert r["status"] == "exact", r["status"]
        assert is_blockage(adj, k, r["members"]) if n <= 7 else True
        sizes1.append(r["value"])
        frames.append([list(bits(F)) for F in r["frame"]])
        if alt:
            r2 = min_size(adj, k, "generators")
            r3 = min_size(adj, k, "maximal")
            assert r2["status"] == "exact" and r3["status"] == "exact"
            sizes2.append(r2["value"])
            sizes3.append(r3["value"])
    # no blockage of order pw + 1 (the other half of the duality)
    r = min_size(adj, pw + 1, "frame")
    assert r["status"] == "none", r["status"]
    row = dict(graph6=graph6_of(adj), n=n, m=sum(popcount(a) for a in adj) // 2, pw=pw, tw=tw,
               size1=json.dumps(sizes1), size2=json.dumps(sizes2), size3=json.dumps(sizes3),
               size1_pw=sizes1[-1] if sizes1 else 0,
               frame_pw=json.dumps(frames[-1]) if frames else "[]")
    return row


def _census_job(args):
    g6, alt = args
    return census_row(adj_of_graph6(g6), alt)


def run_census(max_n: int = 8, workers: int = 8, alt_max_n: int = 8, limit: int | None = None,
               log=print) -> None:
    SCRATCH.mkdir(parents=True, exist_ok=True)
    for n in range(1, max_n + 1):
        out = SCRATCH / f"census_n{n}.csv"
        t0 = time.time()
        jobs = [(graph6_of(adj), n <= alt_max_n) for adj in connected_graphs(n)]
        if limit:
            jobs = jobs[:limit]
        if n <= 4 or workers <= 1:
            rows = [_census_job(j) for j in jobs]
        else:
            with Pool(workers, initializer=_nice) as pool:
                rows = list(pool.imap(_census_job, jobs, chunksize=max(1, len(jobs) // (workers * 8))))
        with out.open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)
        log(f"n={n}: {len(rows)} connected graphs, {time.time() - t0:.1f} s -> {out}")


def _nice():
    try:
        os.nice(19)
    except OSError:
        pass


# ----------------------------------------------------------------------------
# named graphs and families
# ----------------------------------------------------------------------------


def named_row(name: str, adj: list[int], time_limit: float, min_order: int | None = None,
              log=print) -> list[dict]:
    n = len(adj)
    pw = pathwidth_of(adj)
    tw = treewidth_of(adj) if n <= 26 else -1
    rows = []
    lo = 1 if min_order is None else max(1, min_order)
    for k in range(pw, lo - 1, -1):
        t0 = time.time()
        r = min_size(adj, k, "frame", time_limit=time_limit)
        checked = ""
        if r["members"] is not None and n <= 12:
            checked = "yes" if is_blockage(adj, k, r["members"]) else "NO"
        alt = {}
        for kind, cap in (("generators", 14), ("maximal", 12)):
            if n <= cap and r["status"] != "censored":
                ra = min_size(adj, k, kind, time_limit=time_limit)
                alt[kind] = (f"{ra['value']}" if ra["status"] == "exact" else
                             f"[{ra['lb']}, {ra['ub']}]" if ra["status"] == "bounded" else "censored")
            else:
                alt[kind] = ""
        rows.append(dict(name=name, n=n, m=sum(popcount(a) for a in adj) // 2, pw=pw, tw=tw, order=k,
                         status=r["status"], lb=r["lb"], ub=r["ub"], value=r["value"],
                         size2=alt["generators"], size3=alt["maximal"],
                         n_small=len(small_sets(adj, k)), calls=r["calls"], seconds=round(r["seconds"], 2),
                         checked=checked,
                         frame=json.dumps([sorted(bits(F)) for F in r["frame"]]) if r["frame"] is not None and len(r["frame"]) <= 64 else "",
                         frame_sizes=json.dumps(sorted(popcount(F) for F in r["frame"])) if r["frame"] is not None else ""))
        log(f"{name} n={n} pw={pw} tw={tw} order={k}: {r['status']} lb={r['lb']} ub={r['ub']} "
            f"|Sm|={rows[-1]['n_small']} {time.time() - t0:.1f}s")
        if r["status"] == "censored":
            break
    return rows


def _named_job(args):
    name, adj, time_limit, min_order = args
    return named_row(name, adj, time_limit, min_order, log=lambda s: None)


def run_named(time_limit: float = 600.0, workers: int = 8, only: str | None = None,
              min_order: int | None = None, out: Path | None = None, log=print) -> None:
    SCRATCH.mkdir(parents=True, exist_ok=True)
    out = SCRATCH / "named.csv" if out is None else out
    jobs = [(name, adj, time_limit, min_order) for name, adj in named_graphs()
            if only is None or name.startswith(only)]
    jobs.sort(key=lambda j: -len(j[1]))
    t0 = time.time()
    if workers <= 1:
        results = [named_row(*j[:3], j[3], log=log) for j in jobs]
    else:
        with Pool(workers, initializer=_nice) as pool:
            results = list(pool.imap_unordered(_named_job, jobs))
    rows = [r for rs in results for r in rs]
    rows.sort(key=lambda r: (r["n"], r["name"], -r["order"]))
    with out.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    for r in rows:
        log(f"{r['name']:14s} n={r['n']:2d} pw={r['pw']} tw={r['tw']} order={r['order']} "
            f"{r['status']:8s} lb={r['lb']} ub={r['ub']} |Sm|={r['n_small']} {r['seconds']}s")
    log(f"{len(rows)} rows, {time.time() - t0:.0f} s -> {out}")


# ----------------------------------------------------------------------------
# report tables
# ----------------------------------------------------------------------------


def census_tables(max_n: int = 9) -> str:
    import pandas as pd

    frames = []
    for n in range(1, max_n + 1):
        p = SCRATCH / f"census_n{n}.csv"
        if not p.exists():
            p = SCRATCH / f"census_n{n}.csv.gz"      # the 9-vertex file is committed gzipped
        if p.exists():
            frames.append(pd.read_csv(p))
    df = pd.concat(frames, ignore_index=True)
    for c in ("size1", "size2", "size3"):
        df[c + "_list"] = df[c].apply(lambda s: json.loads(s) if isinstance(s, str) else [])
    lines = []
    lines.append("| n | graphs | pw range | max min-size₁ at order pw | mean | share = 1 | max min-size₁ at pw−1 | max size₁ any order | graphs with min-size₁ > n |")
    lines.append("|--:|--:|:--|--:|--:|--:|--:|--:|--:|")
    for n, g in df.groupby("n"):
        s_pw = g["size1_pw"]
        s_pw1 = g["size1_list"].apply(lambda l: l[-2] if len(l) >= 2 else 0)
        s_any = g["size1_list"].apply(lambda l: max(l) if l else 0)
        lines.append(f"| {n} | {len(g)} | {g.pw.min()}–{g.pw.max()} | {s_pw.max()} | {s_pw.mean():.2f} | "
                     f"{(s_pw == 1).mean():.3f} | {s_pw1.max()} | {s_any.max()} | {int((s_any > n).sum())} |")
    out = "\n".join(lines)
    # alternatives where available
    alt = df[df["size2_list"].apply(len) > 0]
    if len(alt):
        lines = ["", "| n | graphs with size₂, size₃ | size₂ = size₁ at every order | size₂ < size₁ | size₃ = size₁ | size₃ < size₁ | size₃ > size₁ | max size₂ at pw | max size₃ at pw |",
                 "|--:|--:|--:|--:|--:|--:|--:|--:|--:|"]
        for n, g in alt.groupby("n"):
            eq2 = g.apply(lambda r: r.size1_list == r.size2_list, axis=1)
            lt2 = g.apply(lambda r: any(a < b for a, b in zip(r.size2_list, r.size1_list)), axis=1)
            eq3 = g.apply(lambda r: r.size1_list == r.size3_list, axis=1)
            lt3 = g.apply(lambda r: any(a < b for a, b in zip(r.size3_list, r.size1_list)), axis=1)
            gt3 = g.apply(lambda r: any(a > b for a, b in zip(r.size3_list, r.size1_list)), axis=1)
            m2 = g["size2_list"].apply(lambda l: l[-1] if l else 0).max()
            m3 = g["size3_list"].apply(lambda l: l[-1] if l else 0).max()
            lines.append(f"| {n} | {len(g)} | {eq2.sum()} | {lt2.sum()} | {eq3.sum()} | {lt3.sum()} | {gt3.sum()} | {m2} | {m3} |")
        out += "\n" + "\n".join(lines)
    # the extremes
    top = df.sort_values(["size1_pw", "n"], ascending=[False, True]).head(12)
    lines = ["", "| graph6 | n | m | pw | tw | min size₁ by order 1..pw |", "|:--|--:|--:|--:|--:|:--|"]
    for _, r in top.iterrows():
        lines.append(f"| `{r.graph6}` | {r.n} | {r.m} | {r.pw} | {r.tw} | {r.size1_list} |")
    out += "\n" + "\n".join(lines)
    # by (pw - tw)
    df["gap"] = df.pw - df.tw
    lines = ["", "| n | pw − tw | graphs | mean min-size₁ at pw | max |", "|--:|--:|--:|--:|--:|"]
    for (n, gap), g in df.groupby(["n", "gap"]):
        lines.append(f"| {n} | {gap} | {len(g)} | {g.size1_pw.mean():.2f} | {g.size1_pw.max()} |")
    out += "\n" + "\n".join(lines)
    return out


def named_table(path: Path | None = None) -> str:
    import pandas as pd

    df = pd.read_csv(SCRATCH / "named.csv" if path is None else path)
    lines = ["| graph | n | m | pw | tw | order | min size₁ | min size₂ | min size₃ | status | \\|Sm\\| | s |",
             "|:--|--:|--:|--:|--:|--:|--:|--:|--:|:--|--:|--:|"]
    for _, r in df.iterrows():
        if r.status == "exact":
            val = f"**{int(r.value)}**"
        elif r.status == "bounded":
            val = f"[{int(r.lb)}, {int(r.ub)}]"
        elif r.status == "none":
            val = "none"
        else:
            val = "censored"
        s2 = "" if (isinstance(r.size2, float)) else str(r.size2)
        s3 = "" if (isinstance(r.size3, float)) else str(r.size3)
        lines.append(f"| {r['name']} | {r.n} | {r.m} | {r.pw} | {r.tw} | {r.order} | {val} | {s2} | {s3} | {r.status} | {r.n_small} | {r.seconds} |")
    return "\n".join(lines)


def family_table(path: Path | None = None) -> str:
    """Per graph: n, pw, tw and the minimum size₁ at orders pw, pw−1, pw−2, pw−3
    (exact values in bold, brackets for bounds), with size₂ at order pw."""
    import pandas as pd
    import re

    df = pd.read_csv(SCRATCH / "named.csv" if path is None else path)

    def cell(r):
        if r.status == "exact":
            return f"**{int(r.value)}**"
        if r.status == "bounded":
            return f"[{int(r.lb)}, {int(r.ub)}]"
        return "—"

    lines = ["| graph | n | m | pw | tw | pw | pw−1 | pw−2 | pw−3 | size₂ at pw | size₁(pw)/n |",
             "|:--|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|"]
    for name, g in df.groupby("name", sort=False):
        g = g.sort_values("order", ascending=False)
        pw = int(g.pw.iloc[0])
        by = {int(r.order): r for _, r in g.iterrows()}
        cells = [cell(by[pw - d]) if (pw - d) in by else "" for d in range(4)]
        top = by[pw]
        s2 = "" if isinstance(top.size2, float) else str(top.size2)
        ratio = f"{top.value / top.n:.2f}" if top.status == "exact" else ""
        lines.append(f"| {name} | {top.n} | {top.m} | {pw} | {top.tw} | " + " | ".join(cells) + f" | {s2} | {ratio} |")
    df = df.sort_values(["name", "order"])
    return "\n".join(lines)


# ----------------------------------------------------------------------------


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--stage", choices=["census", "named", "report", "one"], required=True)
    ap.add_argument("--max-n", type=int, default=8)
    ap.add_argument("--alt-max-n", type=int, default=8, help="compute size₂ and size₃ up to this n")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--time-limit", type=float, default=600.0)
    ap.add_argument("--only", default=None)
    ap.add_argument("--min-order", type=int, default=None)
    ap.add_argument("--out", default=None)
    ap.add_argument("--graph6", default=None)
    ap.add_argument("--order", type=int, default=None)
    a = ap.parse_args()
    if a.stage == "census":
        run_census(a.max_n, a.workers, a.alt_max_n, a.limit)
    elif a.stage == "named":
        run_named(a.time_limit, a.workers, a.only, a.min_order, Path(a.out) if a.out else None)
    elif a.stage == "one":
        adj = adj_of_graph6(a.graph6)
        pw = pathwidth_of(adj)
        for k in ([a.order] if a.order else range(pw, 0, -1)):
            r = min_size(adj, k, "frame", time_limit=a.time_limit)
            print(k, r["status"], r["lb"], r["ub"], f"{r['seconds']:.1f}s",
                  [sorted(bits(F)) for F in (r["frame"] or [])][:20])
    else:
        print(census_tables(a.max_n))
        print()
        print(family_table())
        print()
        print(named_table())


if __name__ == "__main__":
    main()
