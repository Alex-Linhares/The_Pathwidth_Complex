"""Refuter's own checks for reports/dense_staircase.md. Shares no code with
learning/staircase_moment.py; the pathwidth oracle is the repository's subset DP."""
import itertools, math, sys, random
from fractions import Fraction
sys.path.insert(0, '/home/al/dev/MOSP')
import networkx as nx
from fixed_parameter_algorithm.pathwidth import compute_pathwidth

def pairs(n):
    return list(itertools.combinations(range(n), 2))

def graph_from_bits(n, bits):
    P = pairs(n); adj = [0]*n
    for k,(i,j) in enumerate(P):
        if bits >> k & 1:
            adj[i] |= 1<<j; adj[j] |= 1<<i
    return adj

def nx_graph(n, adj):
    G = nx.Graph(); G.add_nodes_from(range(n))
    for i in range(n):
        for j in range(i+1,n):
            if adj[i]>>j & 1: G.add_edge(i,j)
    return G

def vs_bruteforce(n, adj):
    """min over all layouts of max active suffix: the definition, no DP."""
    best = n
    for perm in itertools.permutations(range(n)):
        w = 0; pre = 0
        for t in range(n):
            pre |= 1<<perm[t]
            # active suffix: vertices not in prefix with a neighbour in prefix
            act = 0
            for v in range(n):
                if not (pre>>v & 1) and adj[v] & pre: act += 1
            w = max(w, act)
            if w >= best: break
        best = min(best, w)
    return best

def matching_exists(cands, m):
    """distinct representatives u_0..u_{m-1} with u_i in cands[i], by augmenting paths."""
    match = {}
    def try_(i, seen):
        for x in cands[i]:
            if x in seen: continue
            seen.add(x)
            if x not in match or try_(match[x], seen):
                match[x] = i; return True
        return False
    return all(try_(i, set()) for i in range(m))

def has_gen_staircase(n, adj, s, strict=False):
    m = s-1
    if m == 0: return True
    if m > n: return False
    for v in itertools.permutations(range(n), m):
        ok = True; cands = []
        vset = set(v)
        for i in range(m):
            forb = 0
            for j in range(m - i):            # i + j < m
                forb |= (1<<v[j]) | adj[v[j]]
            c = [x for x in range(n) if not (forb>>x & 1) and not (strict and x in vset)]
            if len(c) == 0: ok = False; break
            cands.append(c)
        if ok and matching_exists(cands, m): return True
    return False

def bandwidth(n, adj):
    best = n
    for perm in itertools.permutations(range(n)):
        pos = [0]*n
        for k,v in enumerate(perm): pos[v]=k
        b = 0
        for i in range(n):
            for j in range(i+1,n):
                if adj[i]>>j & 1: b = max(b, abs(pos[i]-pos[j]))
        best = min(best, b)
    return best

def c_sum(s, a, b):
    return sum(min(a, s-i) for i in range(1, b+1))
def c_closed(s, a, b):
    if a + b <= s: return a*b
    d = a + b - s
    return a*b - d*(d+1)//2

def check_lemma_all(n):
    N = n*(n-1)//2
    viol = 0; by_e_pw = {}
    for bits in range(1<<N):
        adj = graph_from_bits(n, bits)
        pw, _ = compute_pathwidth(nx_graph(n, adj))
        e = bin(bits).count('1')
        by_e_pw[(e, pw)] = by_e_pw.get((e, pw), 0) + 1
        for s in range(1, n+1):
            if (pw <= n - s) != has_gen_staircase(n, adj, s):
                viol += 1; print('VIOLATION', n, bits, s, pw)
    return viol, by_e_pw

def check_lemma_random(n, trials, seed=1):
    rng = random.Random(seed); viol = 0
    for _ in range(trials):
        p = rng.choice([0.3, 0.5, 0.7])
        bits = sum(1<<k for k in range(n*(n-1)//2) if rng.random() < p)
        adj = graph_from_bits(n, bits)
        pw, _ = compute_pathwidth(nx_graph(n, adj))
        for s in range(1, n+1):
            if (pw <= n - s) != has_gen_staircase(n, adj, s):
                viol += 1; print('VIOLATION', n, bits, s, pw)
    return viol

def check_bw_lemma(n, graphs):
    viol = 0
    for adj in graphs:
        bw = bandwidth(n, adj)
        for s in range(1, n+1):
            if 2*s - 2 <= n and (bw <= n - s) != has_gen_staircase(n, adj, s, strict=True):
                viol += 1
    return viol

def check_block_bound(n, by_e_pw, ps):
    """P(pw <= n - s) <= n^(a+b) q^c(s,a,b), exact rationals, all 0 <= a,b <= s-1."""
    N = n*(n-1)//2; viol = 0; tight = []
    for p in ps:
        q = 1 - p
        for s in range(1, n+1):
            prob = sum(cnt * p**e * q**(N-e) for (e,pw),cnt in by_e_pw.items() if pw <= n - s)
            for a in range(0, s):
                for b in range(0, s):
                    assert c_sum(s,a,b) == c_closed(s,a,b)
                    bound = Fraction(n)**(a+b) * q**c_closed(s,a,b)
                    if prob > bound: viol += 1; print('BLOCK VIOLATION', n, p, s, a, b, prob, bound)
    return viol

def brute_second_moment(n, s, p):
    """E[X_s], E[X_s^2] over every labelled graph, X_s = # ordered strict staircases."""
    m = s-1; N = n*(n-1)//2; q = 1-p
    P = pairs(n); idx = {pr:k for k,pr in enumerate(P)}
    # list every strict staircase placement with its forced-pair bitmask
    placements = []
    for v in itertools.permutations(range(n), m):
        rest = [x for x in range(n) if x not in v]
        for u in itertools.permutations(rest, m):
            F = 0
            for i in range(m):
                for j in range(m-i):
                    a,b = sorted((u[i], v[j])); F |= 1 << idx[(a,b)]
            placements.append(F)
    EX = Fraction(0); EX2 = Fraction(0)
    for bits in range(1<<N):
        w = p**bin(bits).count('1') * q**(N-bin(bits).count('1'))
        X = sum(1 for F in placements if F & bits == 0)
        EX += w*X; EX2 += w*X*X
    # the identity R = E_{S'}[b^{ov(S',S0)}]
    S0 = placements[0]; bb = 1/q
    R_id = sum(bb**bin(F & S0).count('1') for F in placements) / len(placements)
    return EX, EX2, Fraction(len(placements)) * q**(m*(m+1)//2), R_id

if __name__ == '__main__':
    what = sys.argv[1]
    if what == 'lemma':
        for n in range(1, 7):
            viol, by = check_lemma_all(n)
            print(f'n={n}: lemma violations={viol} over {2**(n*(n-1)//2)} graphs')
            if n <= 5:
                # oracle sanity: DP against the definition on every graph
                bad = 0
                for bits in range(1<<(n*(n-1)//2)):
                    adj = graph_from_bits(n, bits)
                    if compute_pathwidth(nx_graph(n, adj))[0] != vs_bruteforce(n, adj): bad += 1
                print(f'   DP vs definition: {bad} disagreements')
            ps = [Fraction(1,2), Fraction(1,3), Fraction(2,3), Fraction(1,10), Fraction(9,10)]
            print(f'   block first-moment violations: {check_block_bound(n, by, ps)}')
            if n <= 5:
                gs = [graph_from_bits(n, b) for b in range(1<<(n*(n-1)//2))]
                print(f'   bandwidth-lemma violations (2s-2<=n): {check_bw_lemma(n, gs)}')
        for n in (7, 8):
            print(f'n={n}: random lemma violations={check_lemma_random(n, 60 if n==7 else 25)}')
    elif what == 'moment':
        for n, s in ((4,2),(5,2),(5,3),(6,2),(6,3),(6,4)):
            for p in (Fraction(1,2), Fraction(1,3)):
                EX, EX2, EXf, R_id = brute_second_moment(n, s, p)
                print(f'n={n} s={s} p={p}: E[X]={float(EX):.6f} formula={float(EXf):.6f} eq={EX==EXf} '
                      f'R={float(EX2/EX**2):.6f} R_identity={float(R_id):.6f} eq={EX2/EX**2==R_id}')
