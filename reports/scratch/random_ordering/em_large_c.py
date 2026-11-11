"""beta_star(c) at the table's c; Edwards-McDermid's Poisson value in log space (no underflow) to c = 10^4;
g(d) asymptotics; is EM > beta_typ for every c > 14.42?"""
import math, sys
sys.path.insert(0, "/home/al/dev/MOSP")
from scipy.stats import poisson
from scipy.optimize import minimize_scalar, brentq
from learning.edwards_mcdermid import g
from learning.separator_moment import beta_star_gnp

def beta_typ(c):
    return -minimize_scalar(lambda x: -(1 - x) * (1 - math.exp(-c * x)), bounds=(0, 1), method="bounded",
                            options={"xatol": 1e-13}).fun

def em(c):
    dmax = int(c + 20 * math.sqrt(c) + 50)
    return sum(poisson.pmf(d, c) * float(g(d)) for d in range(3, dmax + 1))

print("c, beta_star, beta_typ, EM")
for c in [3, 6, 10, 14.42, 20, 50, 100]:
    bs = beta_star_gnp(c) if c > 4 * math.log(2) else 0.0
    print(f"{c:8g} {bs:.4f} {beta_typ(c):.4f} {em(c):.4f}")
print("\nlarge c: EM - beta_typ")
for c in [100, 200, 500, 1000, 2000, 5000, 10000]:
    print(f"{c:8g} beta_typ={beta_typ(c):.6f} EM={em(c):.6f} diff={em(c)-beta_typ(c):+.6f}  c(1-EM)={c*(1-em(c)):.3f} c(1-beta_typ)={c*(1-beta_typ(c)):.3f}")
print("\ng(d): d, g(d), 1 - g(d), d(1-g(d))")
for d in [3, 4, 5, 10, 20, 50, 100, 200, 500, 1000]:
    gd = float(g(d))
    print(f"{d:5d} {gd:.6f} {1-gd:.6f} {d*(1-gd):.4f}")
# sign changes of EM - beta_typ on a grid
prev = None; crossings = []
c = 1.0
while c <= 3000:
    d = em(c) - beta_typ(c)
    if prev is not None and (d > 0) != (prev > 0):
        crossings.append(c)
    prev = d; c *= 1.02
print("\nsign changes of EM - beta_typ on a 2% grid from 1 to 3000 near:", [round(x, 2) for x in crossings])
