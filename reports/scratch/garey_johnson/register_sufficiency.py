"""PO1 REGISTER SUFFICIENCY against pathwidth of Lengauer's G_u.

G&J PO1 (p. 272) is the progressive (one-shot) black pebble game on a dag with the
outputs (G&J's in-degree-0 vertices; sinks in the operand -> consumer orientation
used here) retained at the end.  Lengauer (1981) Thm 2 / PebblingGu.lean give the
*black-white* progressive demand pbw(D) = pw(G_u) + 1 for every digraph, with
G_u: u ~ w iff an arc joins them either way or they share an immediate successor.

This script computes, for every labelled dag on n <= 6 vertices (arcs i -> j, i < j)
and a random sample at n = 7, 8:
  pb     the black progressive demand (KP game, no retention)
  pbGJ   the same with every sink retained (G&J PO1)
  pbw    = pw(G_u) + 1 (exact subset DP of fixed_parameter_algorithm/pathwidth.py)
  pwU    = pw(underlying undirected graph) + 1
and reports the maximum gaps and the smallest witnesses.

Regenerate:  cd /home/al/dev/MOSP && python reports/scratch/garey_johnson/register_sufficiency.py
"""
from __future__ import annotations
import itertools, random, sys, time
sys.path.insert(0, "/home/al/dev/MOSP")
import networkx as nx
from fixed_parameter_algorithm.pathwidth import compute_pathwidth


def black_demand(n, pred, retain, K):
    """Can D be pebbled progressively with K black pebbles?  pred[v] = bitmask of
    immediate predecessors; retain = bitmask of vertices that may never be removed."""
    full = (1 << n) - 1
    start = (0, 0)
    seen = {start}
    stack = [start]
    while stack:
        P, D = stack.pop()
        if D == full:
            return True
        # place
        if bin(P).count("1") < K:
            for v in range(n):
                b = 1 << v
                if not (D & b) and (pred[v] & P) == pred[v]:
                    s = (P | b, D | b)
                    if s not in seen:
                        seen.add(s); stack.append(s)
        # remove
        R = P & ~retain
        while R:
            b = R & -R; R ^= b
            s = (P & ~b, D)
            if s not in seen:
                seen.add(s); stack.append(s)
    return False


def demand(n, pred, retain):
    for K in range(1, n + 1):
        if black_demand(n, pred, retain, K):
            return K
    return n


def gu(n, arcs):
    G = nx.Graph(); G.add_nodes_from(range(n))
    succ = [set() for _ in range(n)]
    for u, v in arcs:
        G.add_edge(u, v); succ[u].add(v)
    for x in range(n):
        preds = [u for u in range(n) if x in succ[u]]
        for a, b in itertools.combinations(preds, 2):
            G.add_edge(a, b)
    return G


def analyse(n, arcs):
    pred = [0] * n
    sinks = (1 << n) - 1
    for u, v in arcs:
        pred[v] |= 1 << u
        sinks &= ~(1 << u)
    pb = demand(n, pred, 0)
    pbgj = demand(n, pred, sinks)
    pbw = compute_pathwidth(gu(n, arcs))[0] + 1
    U = nx.Graph(); U.add_nodes_from(range(n)); U.add_edges_from(arcs)
    pwu = compute_pathwidth(U)[0] + 1
    return pb, pbgj, pbw, pwu, bin(sinks).count("1")


def run(n, sample=None, seed=0):
    pairs = list(itertools.combinations(range(n), 2))
    rng = random.Random(seed)
    if sample is None:
        gen = (tuple(p for p, bit in zip(pairs, mask_bits(len(pairs), m)) if bit)
               for m in range(1 << len(pairs)))
        total = 1 << len(pairs)
    else:
        gen = (tuple(p for p in pairs if rng.random() < rng.choice([0.2, 0.35, 0.5, 0.7]))
               for _ in range(sample))
        total = sample
    stats = {"count": 0, "max_pb_minus_pbw": 0, "wit_pb": None,
             "max_pbgj_minus_pbw_onesink": 0, "wit_gj1": None,
             "max_pbgj_minus_pb": 0, "wit_gj": None,
             "max_pbw_minus_pwu": 0, "wit_u": None, "pb_lt_pbw": 0}
    for arcs in gen:
        pb, pbgj, pbw, pwu, ns = analyse(n, arcs)
        stats["count"] += 1
        if pb < pbw:
            stats["pb_lt_pbw"] += 1
        if pb - pbw > stats["max_pb_minus_pbw"]:
            stats["max_pb_minus_pbw"] = pb - pbw; stats["wit_pb"] = (arcs, pb, pbw)
        if ns == 1 and pbgj - pbw > stats["max_pbgj_minus_pbw_onesink"]:
            stats["max_pbgj_minus_pbw_onesink"] = pbgj - pbw; stats["wit_gj1"] = (arcs, pbgj, pbw)
        if pbgj - pb > stats["max_pbgj_minus_pb"]:
            stats["max_pbgj_minus_pb"] = pbgj - pb; stats["wit_gj"] = (arcs, pbgj, pb)
        if pbw - pwu > stats["max_pbw_minus_pwu"]:
            stats["max_pbw_minus_pwu"] = pbw - pwu; stats["wit_u"] = (arcs, pbw, pwu)
    return stats


def mask_bits(k, m):
    return [(m >> i) & 1 for i in range(k)]


if __name__ == "__main__":
    t0 = time.time()
    for n in (2, 3, 4, 5, 6):
        s = run(n)
        print(f"n={n} all {s['count']} labelled dags: "
              f"max pb-pbw={s['max_pb_minus_pbw']} wit={s['wit_pb']}; "
              f"pb<pbw on {s['pb_lt_pbw']}; "
              f"max pbGJ-pbw (one sink)={s['max_pbgj_minus_pbw_onesink']} wit={s['wit_gj1']}; "
              f"max pbGJ-pb={s['max_pbgj_minus_pb']} wit={s['wit_gj']}; "
              f"max pbw-pwU={s['max_pbw_minus_pwu']} wit={s['wit_u']}  [{time.time()-t0:.0f}s]",
              flush=True)
    for n, sample in ((7, 3000), (8, 1000)):
        s = run(n, sample=sample, seed=n)
        print(f"n={n} random {s['count']} dags: "
              f"max pb-pbw={s['max_pb_minus_pbw']} wit={s['wit_pb']}; "
              f"pb<pbw on {s['pb_lt_pbw']}; "
              f"max pbGJ-pbw (one sink)={s['max_pbgj_minus_pbw_onesink']} wit={s['wit_gj1']}; "
              f"max pbGJ-pb={s['max_pbgj_minus_pb']}; "
              f"max pbw-pwU={s['max_pbw_minus_pwu']}  [{time.time()-t0:.0f}s]", flush=True)
