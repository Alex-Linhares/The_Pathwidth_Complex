"""beta_typ(c) = max_x (1-x)(1-e^{-cx}); the maximiser; asymptotics; the crossover with
Edwards-McDermid's Poisson value; the dense and middle regimes.  reports/random_ordering_bound.md."""
import math, sys
sys.path.insert(0, "/home/al/dev/MOSP")
from scipy.optimize import brentq, minimize_scalar
from learning.edwards_mcdermid import poisson_value

def beta_typ(c):
    r = minimize_scalar(lambda x: -(1 - x) * (1 - math.exp(-c * x)), bounds=(0, 1), method="bounded",
                        options={"xatol": 1e-13})
    return -r.fun, r.x

def xstar(c):
    # first-order condition (1-x) c e^{-cx} = 1 - e^{-cx}
    return brentq(lambda x: (1 - x) * c * math.exp(-c * x) - (1 - math.exp(-c * x)), 1e-12, 1 - 1e-12, xtol=1e-14)

print("c, x*(c) [Brent on FOC], x* [maximiser], beta_typ(c), 1-(ln c+1)/c, c*(1-beta_typ)-(ln c+1), EM Poisson, EM-beta_typ")
for c in [1, 2, 3, 4, 6, 8, 10, 14.42, 20, 30, 50, 100, 1000, 10000]:
    b, xm = beta_typ(c)
    xs = xstar(c)
    em = poisson_value(c)
    print(f"{c:8g} {xs:.6f} {xm:.6f} {b:.6f} {1-(math.log(c)+1)/c:.6f} {c*(1-b)-(math.log(c)+1):+.5f} {em:.6f} {em-b:+.4f}")

c0 = brentq(lambda c: poisson_value(c) - beta_typ(c)[0], 10, 20, xtol=1e-10)
print(f"\ncrossover c0 = {c0:.6f}; beta_typ(c0) = {beta_typ(c0)[0]:.6f}; EM(c0) = {poisson_value(c0):.6f}")
# second-order term: c(1 - beta) - ln c - 1 ~ ?  compare with (ln c - 1)/c * something
print("\nsecond order: c*(1-beta_typ) - ln c - 1, against (ln c)^2/(2c)? and (ln c - 1)/c")
for c in [10, 100, 1000, 10000, 1e5, 1e6]:
    b, _ = beta_typ(c)
    r = c * (1 - b) - math.log(c) - 1
    print(f"{c:10g} {r:+.6e}  (ln c -1)/c = {(math.log(c)-1)/c:.6e}  ratio {r / ((math.log(c)-1)/c):.4f}")

print("\nDense regime, p fixed: n - max_t (n-t)(1-(1-p)^t) against log_b n + log_b ln b + 1/ln b")
for p in [0.1, 0.25, 0.5]:
    b = 1 / (1 - p); lb = math.log(b)
    for n in [30, 60, 100, 1000, 10**4, 10**6]:
        w = max((n - t) * (1 - (1 - p) ** t) for t in range(1, n))
        pred = math.log(n) / lb + math.log(lb) / lb + 1 / lb
        print(f"p={p} n={n:8d}: n - width = {n - w:8.3f}; log_b n = {math.log(n)/lb:8.3f}; log_b n + log_b ln b + 1/ln b = {pred:8.3f}")

print("\nMiddle regime: c(1 - beta_typ)/ln c against Frieze's 2 (n - alpha ~ 2 n ln c / c) and the first moment's 4")
for c in [10, 20, 50, 100, 1000, 10**4, 10**6]:
    b, _ = beta_typ(c)
    print(f"c={c:8g}: c(1-beta_typ)/ln c = {c*(1-b)/math.log(c):.4f}")
