"""Refuter's own large-n numerics (no code shared with learning/staircase_moment.py)."""
import math, sys
from math import lgamma, log, sqrt
def lfall(n, k):  # ln (n)_k, as a sum of logs (lgamma cancels at n = 1e50)
    if k < 0: raise ValueError
    if k > n: return -math.inf          # (n)_k = 0
    return k*log(n) + sum(math.log1p(-i/n) for i in range(k))
def c(s,a,b):
    return sum(min(a, s-i) for i in range(1,b+1))
def c_closed(s,a,b):
    return a*b if a+b<=s else a*b - (a+b-s)*(a+b-s+1)//2
def ln_block_term(n, q, s, a, b, symmetric=False):
    if not symmetric:
        cnt = lfall(n,a)+lfall(n,b)
    else:
        fv = min(a, s-b); fu = min(b, s-a)
        cnt = lfall(n,a) - lgamma(fv+1) + lfall(n-a, fu) - lgamma(fu+1) + lfall(n-fv-fu, b-fu) - lfall(n-a,fu) + lgamma(fu+1) + lfall(n-a,fu) - lgamma(fu+1)
        # i.e. C(n,fv)(n-fv)_{a-fv} * C(n-a,fu) * (n-fv-fu)_{b-fu}
        cnt = (lfall(n,fv)-lgamma(fv+1)) + lfall(n-fv, a-fv) + (lfall(n-a,fu)-lgamma(fu+1)) + lfall(n-fv-fu, b-fu)
    return cnt + c_closed(s,a,b)*log(q)
def block_min(n, q, s, symmetric=False, step=1):
    best = (math.inf,0,0)
    for a in range(1, s, step):
        for b in range(1, s, step):
            v = ln_block_term(n,q,s,a,b,symmetric)
            if v < best[0]: best = (v,a,b)
    return best
def least_s_below_one(n, q, symmetric=False):
    """least s with min_{a,b} block term < 1 (ln < 0); bracket then scan."""
    s = 2
    while s < n and block_min(n,q,s,symmetric, step=max(1,s//60))[0] >= 0: s = min(n, int(s*1.3)+1)
    lo = int(s/1.3)-1
    for t in range(max(2,lo), s+1):
        if block_min(n,q,t,symmetric, step=max(1,t//200))[0] < 0: return t
    return s
A_STAR = 2+sqrt(2)
if sys.argv[1] == 'thresholds':
    print('ordered count (n^{a+b} style, falling factorials):')
    for p in (0.5, 0.3):
        q = 1-p; lb = log(1/q)
        for n in (30,40,50,60,10**3,10**4,10**5,10**6,10**7):
            L = log(n)/lb
            t = least_s_below_one(n,q); v,a,b = block_min(n,q,t,step=max(1,t//200))
            print(f'p={p} n={n:>9} L={L:7.3f} least s with block<1: {t:4d}  s/L={t/L:.3f} argmin a={a} b={b} a/L={a/L:.3f}  (2+sqrt2)L={A_STAR*L:.2f}')
    print('symmetric count (full rows/columns unordered):')
    for n in (30,40,50,60,10**3,10**4,10**5,10**6,10**7):
        q=0.5; L=math.log2(n)
        t = least_s_below_one(n,q,symmetric=True)
        print(f'p=0.5 n={n:>9} L={L:7.3f} least s with symmetric block<1: {t:4d} s/L={t/L:.3f}  largest s with >=1: {t-1}')
elif sys.argv[1] == 'exponent':
    # g_a(y) against the exact exponent / (L^2 ln b) at huge n
    def g(a,y): return 2*y - y*y + ((2*y-a)**2/2 if 2*y>a else 0.0)
    for n_exp in (7, 50, 300):
        n = 10**n_exp; q=0.5; lb=log(2); L = log(n)/lb
        for a in (3.0, 3.3, 3.414, 3.5, 4.0):
            s = round(a*L)
            for y in (a/2, a-1, 1+sqrt(2)):
                aa = round(y*L)
                ex = (lfall(n,aa)+lfall(n,aa) + c_closed(s,aa,aa)*log(q)) / (L*L*lb)
                print(f'n=1e{n_exp} a={a} y={y:.3f}: exact/(L^2 ln b)={ex:+.4f}  g_a(y)={g(a,y):+.4f}')
    print('min of g_a over y, and a^2/2-2a+1:')
    for a in (3.0, 3.3, 3.414, 3.5, 4.0):
        ys = [i/10000 for i in range(1, int(a*10000)+1)]
        m = min(g(a,y) for y in ys); am = min(ys, key=lambda y: g(a,y))
        print(f'a={a}: min g={m:+.4f} at y={am:.3f} (a-1={a-1:.3f}); -(a^2/2-2a+1)={-(a*a/2-2*a+1):+.4f}')
    print('max of h_a(x)=-x+x^2/4-(x-a)^2/2[x>a] on (0,2a]:')
    def h(a,x): return -x + x*x/4 - ((x-a)**2/2 if x>a else 0.0)
    for a in (3.0, 3.3, 3.414, 3.5, 3.9):
        xs = [i/10000 for i in range(1, int(2*a*10000)+1)]
        M = max(h(a,x) for x in xs); xm = max(xs, key=lambda x: h(a,x))
        print(f'a={a}: max h={M:+.4f} at x={xm:.3f} (2a-2={2*a-2:.3f}); a^2/2-2a+1={a*a/2-2*a+1:+.4f}')
    print('roots of a^2-4a+2:', 2-sqrt(2), 2+sqrt(2))
elif sys.argv[1] == 'ratio':
    # the finite upper sum U and lower sum Lambda, my own code, at astronomically large n
    def lse(vals):
        vals = [v for v in vals if v > -math.inf]
        M = max(vals); return M + log(sum(math.exp(v-M) for v in vals))
    def lnU(n, q, s):
        m = s-1; b = log(1/q); terms=[]
        for ap in range(0, m+1):
            for bp in range(0, m+1):
                j = ap+bp
                t = (lgamma(m+1)-lgamma(ap+1)-lgamma(m-ap+1)) + (lgamma(m+1)-lgamma(bp+1)-lgamma(m-bp+1)) \
                    + lfall(2*m, j) + lfall(n-2*m, 2*m-j) - lfall(n, 2*m) + c_closed(s,ap,bp)*b
                terms.append(t)
        return lse(terms)
    def lnLam(n, q, s):
        m = s-1; b = log(1/q); terms=[]
        for ap in range(0, m+1):
            for bp in range(0, m+1):
                j = ap+bp
                terms.append(lfall(n-2*m, 2*m-j) - lfall(n, 2*m) + c_closed(s,ap,bp)*b)
        return lse(terms)
    q = 0.5
    for n_exp in (7, 30, 100, 300, 1000):
        n = 10**n_exp; L = n_exp*log(10)/log(2)
        for a in (3.0, 3.3, 3.5, 3.9):
            s = round(a*L)
            print(f'n=1e{n_exp} L={L:.1f} a={a} s={s}: ln U={lnU(n,q,s):+.3f}  ln Lambda={lnLam(n,q,s):+.3f}  (a^2/2-2a+1)L^2 ln2={(a*a/2-2*a+1)*L*L*log(2):+.1f}')
