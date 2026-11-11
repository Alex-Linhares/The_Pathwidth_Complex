"""lean_target_check.py -- the middle-regime statements to be proved in Lean (FirstMomentAsymptotics.lean,
section "The middle regime"), checked numerically before any Lean is written (CLAUDE.md rule), 2026-11-11.

Theorem M (finite form), for real c with 1 < c and 4 ln c < c, integer n >= 3 with c <= n, p = c/n,
beta = 1 - 4 ln c / c, a = (1 - beta)/2 = 2 ln c / c, k = floor(beta n), t = (n - k + 1) div 2:

    RHS0   := C(n,t) C(n-t,t-1) (1-p)^(t(t-1))                      (the proved input, 0^0 = 1)
    target := exp( -(4 ln c / c)(ln(2 ln c) - 1) n + 3 ln n + 2 ln c )

and the claim is RHS0 <= target.  Also checked, in the exact form the Lean proof uses:

  (M1)  negMulLog(1 - x) <= x                                      for 0 <= x <= 1
  (M2)  a (c a + 2 ln a - 2) <= delta(beta, c) = c a^2 - 2 phi(a) - phi(1 - 2a)   for 0 <= a <= 1/2, any c
  (M3)  (4 ln c / c)(ln(2 ln c) - 1) <= delta(1 - 4 ln c / c, c)   for c > 1, 4 ln c <= c
  (M4)  exp(-delta n + 3 ln n + c a) <= target                      (what M3 gives after Theorem A)
  (M5)  4 ln c < c                                                  for c >= 9
  (M6)  -A n + 3 ln n + 2 ln c <= -ln c (4 ln(2 ln c) - 9)          for 0 < c <= n, A = (4 ln c/c)(ln(2 ln c) - 1),
                                                                    whenever A c >= 3
Grid: n = 3..300, c on 60 points of (1, n] including n itself (p = 1) and every integer c <= 40,
restricted to 4 ln c < c.  Floats with lgamma (relative error ~1e-12 against slacks of order 1).
Usage: nice -n 19 python3 -I lean_target_check.py
"""
import math
from fractions import Fraction
import numpy as np

def phi(x): return 0.0 if x <= 0 else -x * math.log(x)
def log_binom(n, k):
    if k < 0 or k > n: return -math.inf
    return math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)
def log_rhs0(n, t, p):
    m = t * (t - 1); lb = log_binom(n, t) + log_binom(n - t, t - 1)
    if p >= 1.0: return lb if m == 0 else -math.inf
    return lb + m * math.log1p(-p)
def delta(c, a): return c * a * a - 2 * phi(a) - phi(1 - 2 * a)

viol = {k: 0 for k in ("main", "M1", "M2", "M3", "M4", "M5", "M6")}
checks = 0; tight = []
# M1
for x in np.linspace(0, 1, 100001):
    if phi(1 - x) > x + 1e-12: viol["M1"] += 1
# M2 over a grid of (a, c)
for a in np.linspace(0, 0.5, 2001):
    for c in (0.1, 1, 2, 5, 9, 20, 100, 1000):
        lhs = a * (c * a + (2 * math.log(a) if a > 0 else 0) - 2) if a > 0 else 0.0
        if lhs > delta(c, a) + 1e-12: viol["M2"] += 1
# M5
for c in np.linspace(9, 10000, 100001):
    if not 4 * math.log(c) < c: viol["M5"] += 1
# main, M3, M4, M6
for n in range(3, 301):
    cs = sorted(set(list(np.linspace(1.0001, n, 60)) + [float(j) for j in range(2, min(n, 40) + 1)] + [float(n)]))
    for c in cs:
        lc = math.log(c)
        if not (c > 1 and 4 * lc < c): continue
        beta = 1 - 4 * lc / c; a = 2 * lc / c; p = c / n
        k = math.floor(Fraction(beta) * n); t = (n - k + 1) // 2
        assert 0 < beta < 1 and 0 <= k < n and 1 <= t
        A = (4 * lc / c) * (math.log(2 * lc) - 1)
        target = -A * n + 3 * math.log(n) + 2 * lc
        d = delta(c, a)
        thmA = -d * n + 3 * math.log(n) + c * a
        r0 = log_rhs0(n, t, p)
        checks += 1
        if r0 > target + 1e-9: viol["main"] += 1
        if A > d + 1e-12: viol["M3"] += 1
        if thmA > target + 1e-9: viol["M4"] += 1
        if A * c >= 3 and target > -lc * (4 * math.log(2 * lc) - 9) + 1e-9: viol["M6"] += 1
        tight.append((target - r0, n, c))
tight.sort()
print("grid points (main):", checks)
print("violations:", viol)
print("smallest slack of the main inequality (nats):", [(round(s, 4), n, round(c, 3)) for s, n, c in tight[:5]])
assert all(v == 0 for v in viol.values())
print("OK")
