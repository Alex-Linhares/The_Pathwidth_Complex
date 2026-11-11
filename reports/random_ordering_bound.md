# The random-ordering bound: the width of a fixed ordering of `G(n, p)` as a theorem

*2026-11-11, one session. The proof on paper (§1–§2), the calculus of `β_typ` (§3), the
comparison with Edwards & McDermid and the crossover (§4), the other two regimes (§5), the
numbers (§6), Lean `lean/MOSPFormalization/RandomOrdering.lean` (§7), the paper text
proposed and not applied (§8), literature (§9), regenerate commands (§10). Scratch under
`reports/scratch/random_ordering/`. Nothing re-solved; no solver run; `solutions/`
untouched; about 0.1 core-hours.*

## 0. Summary

**The statement.** For a fixed ordering `v_1, …, v_n` of the vertices of `G(n, p)` — the
identity, say; no randomness in the ordering is needed — the open count at step `t`,
`k_t = |N(S_t) ∖ S_t|` with `S_t = {v_1, …, v_t}`, is the sum over the `n − t` suffix
vertices of the indicators "`v_j` has an edge into `S_t`". The indicator of `v_j` is a
function of the `t` pairs `{v_i v_j : i ≤ t}`, and these `t`-sets are pairwise disjoint
across `j > t` (a pair `v_i v_j` with `i ≤ t < j` determines `j`), so the indicators are
independent and **`k_t ~ Bin(n − t, 1 − (1 − p)^t)`, exactly** (§1, Lemma 1). Hoeffding plus a
union bound over the `n` positions gives, for `c ≤ n/2`,

```
P( pw(G(n, c/n)) > β_typ(c)·n + c² + √(n ln n) ) ≤ 1/n,      β_typ(c) = max_{x ∈ [0,1]} (1 − x)(1 − e^{−cx}),
```

since `pw ≤ vs(identity ordering) = max_t k_t` (§2, Theorem R). So `pw(G(n, c/n)) ≤
(β_typ(c) + ε) n` with high probability for every `ε > 0` — the bound the second-moment
session found as a by-product (`reports/layout_second_moment.md` §2.3) is now a theorem
with an explicit error term, and its finite form is in Lean.

**The calculus (§3).** The maximiser `x*(c)` is unique (the function is strictly concave)
and solves `(1 − x) c e^{−cx} = 1 − e^{−cx}`; in `y = e^{−cx}` the condition is
`y ln y + (c + 1) y = 1`, and then `β_typ(c) = (1 − y*)² / (c y*)`. Asymptotically
`x*(c) = (ln c)/c − (ln c − 1)/c² + …` and

```
β_typ(c) = 1 − (ln c + 1)/c + (ln c)/c² + O(ln² c / c³),
```

the second-order term checked to five digits at `c = 10⁶`. Values: `0.4227, 0.5858, 0.6936,
0.7589, 0.8080, 0.9034, 0.9444` at `c = 3, 6, 10, 14.42, 20, 50, 100`.

**Against Edwards & McDermid (§4).** Their Corollary 5.2 on Poisson(`c`) degrees gives
`0.1826, 0.4575, 0.6558, 0.7589, 0.8255, 0.9300, 0.9650` at the same `c`. The two cross
**once, at `c₀ = 14.421`** (Brent on the difference; one sign change on a 2 % grid from
`c = 1` to `3,000`), and stay apart: their weight function satisfies `1 − g(d) = 3.5/d (1 −
1/d)` to the digits computed (`d ≤ 1,000`), so their bound is `1 − 3.5/c + o(1/c)` against
the random ordering's `1 − (ln c + 1)/c`, and the random ordering wins by the factor
`(ln c + 1)/3.5` in the deficit from `1` for every `c > c₀`. **The upper end of the
fixed-`c` sandwich is Edwards–McDermid for `c < 14.42` and the random ordering for
`c ≥ 14.42**: `[0.554, 0.808]` at `c = 20`, `[0.761, 0.903]` at `50`, `[0.857, 0.944]` at
`100` (floors `β*(c)`), where the published upper line read `0.826`, `0.930`, `0.965`.

**The other regimes (§5).** *Dense, `p` fixed, `b = 1/(1 − p)`:* `n − max_t E[k_t] = log_b n
+ log_b ln b + 1/ln b + o(1)` (the maximiser is `t* = log_b(n ln b)`), and with the
fluctuations `n − vs(identity) ≥ (1 − o(1)) log_b n` whp: coefficient **1** on `log_b n`,
below the independence-number ceiling's `2` and Theorem B's `4` — consistent with the
bracket `[2, 4]` and not inside it; the random ordering is the weakest of the three there.
*Middle, `c → ∞`:* `1 − β_typ(c) = (ln c + 1)/c (1 + o(1))`, so `n − vs(identity) ≈ n ln c /
c`, coefficient **1** against Frieze's `2` (`n − α(G)`) and the first moment's `4`:
Frieze's independence number remains the better upper end asymptotically, and the
ratio `c (1 − β_typ(c)) / ln c` is `1.33, 1.21, 1.07` at `c = 10, 100, 10⁶`. At fixed `c` Frieze's
constant is asymptotic in `c`, so the *explicit* upper line is `min(EM, β_typ)`; on the
320 middle-regime graphs (`n ≤ 60`) the measured `n − α` beats the identity width by
`0.2–2` in every cell and Edwards–McDermid beats both at `c ≤ 15.5` (§6.2).

**Numbers (§6).** The finite theorem evaluated at level `0.05` (the least `w` with
`Σ_t P(Bin(n − t, 1 − (1 − p)^t) > w) ≤ 0.05`) equals the largest identity-ordering width in
the cell `± 1` on all 16 middle-regime cells — tight for what it states — and sits above
`β_typ n` by the `√(n ln n)` term: `0.461 n` against `0.423 n` at `c = 3`, `n = 1,000`. The
identity width is `1.15–1.85 ×` the proved pathwidth on those graphs. Against the fitted
slopes of the sparse pilot (`0.099, 0.268, 0.415` at `c = 3, 6, 10`) the random ordering is
far above (`0.423, 0.586, 0.694`): it is a ceiling, not an estimate.

**Lean (§7).** `RandomOrdering.lean`, 18 theorems, no `sorry`, axioms `propext`,
`Classical.choice`, `Quot.sound` only; `lake build` of the root passes (8,993 jobs). The
independence over disjoint blocks of pairs (`sum_gnpWeight_blocks`, iterating
`sum_gnpWeight_pattern` of `LayoutMoment.lean`), the law of the active suffix
(`sum_gnpWeight_activeSuffix_eq`), **the exact binomial tail at every position**
(`sum_gnpWeight_vertexSepAt_gt`), the union bound (`sum_gnpWeight_vertexSepOfLayout_gt_le`),
**`P(pathwidth > w) ≤ Σ_{i < n} P(Bin(n − i − 1, 1 − (1 − p)^(i + 1)) > w)`**
(`sum_gnpWeight_pathwidth_gt_le`, its complement `sum_gnpWeight_graphsOfPathwidthLe_ge`),
and the generating-function Chernoff bound `binomTail_le_exp`. The asymptotic `β_typ`
statement (Hoeffding's lemma, the two elementary inequalities, the maximum over `t`) is on
paper. **The finite statement was brute-forced before it was stated**: every labelled graph
on `n ≤ 7` vertices (2,097,152 at seven), the identity ordering, four values of `p`, every
position exact in rational arithmetic and the union bound, 672 checks, zero discrepancies.
One repair outside the brief: the root `MOSPFormalization.lean` did not build before this
session — `LayoutMoment.relabel` (2026-11-11) clashed with `SeparatorMoment.relabel`
(loop0011), the previous session having built its module alone — renamed to
`layoutRelabel`; no statement changed.

**Paper (§8), proposed not applied:** a paragraph *A trivial upper bound* for Appendix E
after *Between the two regimes*, the Appendix A row `randomordering`, and a `refs.bib`
entry for Hoeffding (1963), which the bibliography lacks; `EdwardsMcDermid2015` and
`Frieze1990` are present.

**Literature (§9).** No new search this session: the statement "we found no prior
statement of the width of a random ordering as a pathwidth bound on `G(n, p)`" rests on the
second-moment session's search (`reports/layout_second_moment.md` §5, `literature/MISSING.md`,
thirteen papers), and is bounded to it. Hoeffding's inequality is textbook and not in
`literature/`.

---

## 1. The open count at a position is binomial

Fix `n`, `0 ≤ p ≤ 1`, and an ordering `v_1, …, v_n` of the vertex set. Let `G ~ G(n, p)`:
each of the `C(n, 2)` pairs is an edge independently with probability `p`. For `1 ≤ t ≤ n`
write `S_t = {v_1, …, v_t}` and

```
k_t = |N(S_t) ∖ S_t| = Σ_{j > t} X_{j,t},      X_{j,t} = 1[ v_j has a neighbour in S_t ].
```

`k_t` is `vertexSepAt G σ (t − 1)` in the Lean vocabulary (positions are `0`-based there:
the prefix at position `i` has `i + 1` vertices), and `vs(G, σ) = max_t k_t` is
`vertexSepOfLayout G σ`.

**Lemma 1 (independence).** For fixed `t`, the variables `(X_{j,t})_{j > t}` are independent
Bernoulli(`q_t`) with `q_t = 1 − (1 − p)^t`; hence `k_t ~ Bin(n − t, q_t)` and
`E[k_t] = (n − t)(1 − (1 − p)^t) =: μ_t`.

*Proof.* `X_{j,t} = 1 − 1[none of the `t` pairs `{v_i, v_j}`, `i ≤ t`, is an edge]`, so
`P(X_{j,t} = 1) = 1 − (1 − p)^t`, and `X_{j,t}` is a function of the pair set
`F_j = {v_i v_j : i ≤ t}`. For `j ≠ j'` in the suffix, `F_j ∩ F_{j'} = ∅`: a pair
`{v_i, v_j}` with `i ≤ t < j` has exactly one endpoint in the suffix, which names `j`. The
edge indicators of `G(n, p)` are independent across pairs, so functions of pairwise disjoint
pair sets are independent. □

*What "exactly" means here.* The independence is across `j` at a fixed `t`. Across `t` the
counts `k_1, …, k_n` are dependent (they are the open-count chain of
`reports/layout_second_moment.md` §1); nothing below uses more than a union bound over `t`.

In Lean the law is `sum_gnpWeight_vertexSepAt_gt`: for every layout `σ`, position `i` and
`w`, the `G(n, p)` weight of `{vertexSepAt G σ i > w}` **equals**
`binomTail |suffixSet σ i| (1 − (1 − p)^{|prefixSet σ i|}) w`, with
`binomTail m q w = Σ_{w < j ≤ m} C(m, j) q^j (1 − q)^{m − j}`. The route is the one of the
proof: `sum_gnpWeight_blocks` (the weight of "the edges inside each of pairwise disjoint
blocks `F_j` form a pattern of `P_j`" is the product of per-block pattern weights, by
induction on the blocks with `sum_gnpWeight_pattern` of `LayoutMoment.lean` as the step;
`SeparatorMoment.lean` has the same product in edge-set vocabulary, `sum_subsetWeight_blocks`,
and the two were left side by side), then `sum_gnpWeight_activeSuffix_eq` (the weight of
`{activeSuffix G σ i = B}` is `q^{|B|} (1 − q)^{m − |B|}` for `B ⊆ suffixSet σ i`, with the
pattern sets "nonempty" for `v ∈ B` and "empty" otherwise, `sum_nonempty_patterns` giving
`1 − (1 − p)^t`), then the fibre sum over `B` grouped by `|B|` (`Finset.sum_powerset_apply_card`).

## 2. The theorem

**Lemma 2 (tail).** For `λ ≥ 0`, `P(Bin(m, q) > w) ≤ e^{−λw} (1 − q + q e^{λ})^m`
(`binomTail_le_exp`, by `add_pow` after inserting `e^{λ(j − w)} ≥ 1` on `j > w`). With
Hoeffding's lemma `1 − q + q e^{λ} ≤ exp(λ q + λ²/8)` and `w = mq + a`, `λ = 4a/m`:

```
P( Bin(m, q) ≥ mq + a ) ≤ exp(−2a²/m)                                              (Hoeffding 1963).
```

**Theorem R (finite form, Lean).** For `0 ≤ p ≤ 1` and every `w`,

```
P( pw(G(n, p)) > w ) ≤ P( vs(G, σ) > w ) ≤ Σ_{t=1}^{n} P( Bin(n − t, 1 − (1 − p)^t) > w )
```

for any fixed layout `σ` (`sum_gnpWeight_pathwidth_gt_le`, `sum_gnpWeight_vertexSepOfLayout_gt_le`).
*Proof.* `pw(G) ≤ vs(G, σ)` for every layout (`pathwidth_le_vertexSepOfLayout`,
`LayoutToDecomposition.lean`); `vs(G, σ) > w` means `k_t > w` for some `t`; union bound;
Lemma 1. □

**Theorem R (explicit form, on paper).** Let `c ≤ n/2`, `n ≥ 2`, `p = c/n`. Then

```
P( pw(G(n, c/n)) > β_typ(c)·n + c² + √(n ln n) ) ≤ 1/n .
```

*Proof.* By Lemma 2 with `a = √(n ln n)` and `m = n − t ≤ n`,
`P(k_t ≥ μ_t + √(n ln n)) ≤ exp(−2 ln n) = n^{−2}`, and the union over `t ≤ n` costs a
factor `n`. It remains to bound `max_t μ_t`. With `x = t/n`,
`μ_t = n(1 − x)(1 − (1 − c/n)^{xn})`; since `ln(1 − u) ≥ −u − u²` for `0 ≤ u ≤ 1/2`,
`(1 − c/n)^{xn} ≥ exp(−cx − x c²/n) ≥ e^{−cx}(1 − x c²/n)`, so
`1 − (1 − c/n)^{xn} ≤ (1 − e^{−cx}) + c²/n` and `μ_t ≤ n (1 − x)(1 − e^{−cx}) + c² ≤
β_typ(c) n + c²`. □

Hence **`pw(G(n, c/n)) ≤ (β_typ(c) + ε) n` with probability `1 − o(1)` for every `ε > 0`**,
and the additive term is `O(√(n ln n))`: a `C log n` term would not do — at `p = c/n` the
variance of `k_t` at the maximiser is `Θ(n)` (`1 − q_t = e^{−cx*}` is a constant), so the
fluctuation of the identity ordering's width is genuinely of order `√n`. The reverse
inequality `(1 − c/n)^{xn} ≤ e^{−cx}` gives `μ_t ≥ n(1 − x)(1 − e^{−cx})`, so
`max_t μ_t = β_typ(c) n + O(c²)` — the identity ordering's width *is* `β_typ(c) n ± O(√n)`,
not merely at most.

## 3. The calculus of `β_typ(c)`

`f_c(x) = (1 − x)(1 − e^{−cx})` on `[0, 1]`, `f_c(0) = f_c(1) = 0`, `f_c > 0` inside.

**The maximiser.** `f_c'(x) = −(1 − e^{−cx}) + (1 − x) c e^{−cx}` and
`f_c''(x) = −2c e^{−cx} − (1 − x) c² e^{−cx} < 0`: `f_c` is strictly concave, the maximiser
`x*(c) ∈ (0, 1)` is unique and solves

```
(1 − x) c e^{−cx} = 1 − e^{−cx} .
```

In `y = e^{−cx}` (so `x = −(ln y)/c`) the condition reads `(1 + (ln y)/c) c y = 1 − y`, i.e.

```
y ln y + (c + 1) y = 1,        y* ∈ (0, 1) unique,        x* = −(ln y*)/c,
```

and substituting `1 − x* = (1 − y*)/(c y*)` into `f_c(x*) = (1 − x*)(1 − y*)`:

```
β_typ(c) = (1 − y*)² / (c y*) .
```

(Check at `c = 3`: `y* = 0.3417`, `x* = 0.3579`, `β_typ = 0.4227`, the values of
`calculus.py`.)

**Asymptotics.** Write `x = (ln c + a)/c`, so `y = e^{−a}/c`. Then
`c f_c(x) = c − (ln c + a) − e^{−a} + (ln c + a) e^{−a}/c`; the first-order condition in
`a` is `1 − e^{−a} = (1 − ln c − a) e^{−a}/c`, whose root is
`a* = (1 − ln c)/c + O(ln² c / c²)`, whence

```
x*(c) = (ln c)/c − (ln c − 1)/c² + O(ln² c / c³),
β_typ(c) = 1 − (ln c + 1)/c + (ln c)/c² + O(ln² c / c³),
```

the leading term `1 − (ln c + 1)/c` being what the second-moment report stated. The
second-order term is confirmed numerically: `c(1 − β_typ) − ln c − 1` is `−0.2386, −0.0467,
−0.00693, −0.000921, −1.3816 × 10⁻⁵` at `c = 10, 10², 10³, 10⁴, 10⁶`, against `−(ln c)/c =
−1.3816 × 10⁻⁵` at `10⁶` (five digits).

| `c` | 1 | 2 | 3 | 4 | 6 | 8 | 10 | 14.42 | 20 | 30 | 50 | 100 | 1000 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `x*(c)` | 0.4429 | 0.3960 | 0.3579 | 0.3266 | 0.2788 | 0.2441 | 0.2177 | 0.1772 | 0.1448 | 0.1107 | 0.0771 | 0.0457 | 0.0069 |
| `β_typ(c)` | 0.1993 | 0.3304 | 0.4227 | 0.4910 | 0.5858 | 0.6487 | 0.6936 | 0.7589 | 0.8080 | 0.8572 | 0.9034 | 0.9444 | 0.9921 |
| `1 − (ln c + 1)/c` | 0 | 0.1534 | 0.3005 | 0.4034 | 0.5347 | 0.6151 | 0.6697 | 0.7456 | 0.8002 | 0.8533 | 0.9018 | 0.9439 | 0.9921 |

## 4. Against Edwards & McDermid (2015), Corollary 5.2

Their bound on `G(n, c/n)` is `(E_c + o(1)) n` with `E_c = Σ_d P(Poisson(c) = d) g(d)`,
`g(d) = 0` for `d ≤ 2`, `g(3) = 1/6`, `d g(d) = (d − 2) g(d − 1) + g(d − 2) + 1`
(`learning.edwards_mcdermid.poisson_value`; `reports/edwards_mcdermid.md` §0 for what is
verified and formalised of it).

| `c` | 3 | 6 | 10 | **14.42** | 20 | 50 | 100 | 1000 |
|---|---|---|---|---|---|---|---|---|
| `β_typ(c)` | 0.4227 | 0.5858 | 0.6936 | 0.7589 | **0.8080** | **0.9034** | **0.9444** | **0.9921** |
| Edwards–McDermid `E_c` | **0.1826** | **0.4575** | **0.6558** | 0.7589 | 0.8255 | 0.9300 | 0.9650 | 0.9965 |
| `E_c − β_typ(c)` | −0.240 | −0.128 | −0.038 | 0.000 | +0.018 | +0.027 | +0.021 | +0.0044 |

**The crossover is `c₀ = 14.42099`** (`brentq` on `E_c − β_typ(c)` over `[10, 20]`,
`β_typ(c₀) = E_{c₀} = 0.75890`), and it is the only one: on a 2 % geometric grid from `c = 1`
to `3,000` the difference changes sign once, near `14.5`; and asymptotically `1 − g(d) =
3.5/d (1 − 1/d)` to the digits computed (`d(1 − g(d)) = 3.4300, 3.4650, 3.4825, 3.4930,
3.4965` at `d = 50, 100, 200, 500, 1000`), so `1 − E_c = 3.5/c + o(1/c)` while
`1 − β_typ(c) = (ln c + 1)/c + O(ln c / c²)`: the random ordering's deficit from `1` is
larger by the factor `(ln c + 1)/3.5` for every large `c`, i.e. its bound is smaller.
(`3.5` is numerical: the recurrence fixes the `1/d` coefficient of `g` only through its
initial values.) The earlier `poisson_value` underflows above `c ≈ 700` (it starts from
`e^{−c}`); `em_large_c.py` evaluates the same sum through `scipy.stats.poisson.pmf`.

**The upper end of the sandwich at fixed `c`, as it now stands:**

| `c` | floor `β*(c)` (first moment) | best valid floor | upper line before | **upper line now** | which |
|---|---|---|---|---|---|
| 3 | 0.0087 | 0.037 (closed pairs) | 0.1826 | 0.1826 | Edwards–McDermid |
| 6 | 0.1706 | 0.182 (separator) | 0.4575 | 0.4575 | Edwards–McDermid |
| 10 | 0.3371 | 0.345 (separator) | 0.6558 | 0.6558 | Edwards–McDermid |
| 14.42 | 0.4561 | — | 0.7589 | 0.7589 | tie |
| 20 | 0.5535 | — | 0.8255 | **0.8080** | random ordering |
| 50 | 0.7606 | — | 0.9300 | **0.9034** | random ordering |
| 100 | 0.8574 | — | 0.9650 | **0.9444** | random ordering |

(`β*(c)` from `learning.separator_moment.beta_star_gnp`; the best valid floors at `3, 6, 10`
from `reports/separator_moment.md`; the fitted slopes of the pilot are `0.099, 0.268,
0.415` at `c = 3, 6, 10`, near the middle of the interval.)

## 5. The other two regimes

### 5.1 Dense, `p` fixed

Write `b = 1/(1 − p)`. Then `μ_t = (n − t)(1 − b^{−t}) = n − t − (n − t) b^{−t}`, and
`n − max_t μ_t = min_t [t + (n − t) b^{−t}]`. Up to the `−t b^{−t}` term the minimand is
`h(t) = t + n b^{−t}`, `h'(t) = 1 − n b^{−t} ln b = 0` at `t* = log_b(n ln b)`, with
`h(t*) = log_b(n ln b) + 1/ln b`. So

```
n − max_t μ_t = log_b n + log_b ln b + 1/ln b + o(1)
```

(numerically: `20.907` against `20.845` at `p = ½`, `n = 10⁶`; `119.260` against `119.259`
at `p = 0.1`, `n = 10⁶`; `calculus.py`). The fluctuations are small there — `Var(k_{t*}) =
(n − t*) q (1 − q) ≈ n b^{−t*} = 1/ln b = O(1)` — and the whp statement is routine: for
`s = log_b n − log_b(L ln n)`, the positions `t ≥ s` have `k_t ≤ n − t ≤ n − s` trivially,
and for `t < s` the number of *closed* suffix vertices `Z_t ~ Bin(n − t, b^{−t})` has mean at
least `(n − s) b^{−s} ≈ L ln n`, so `P(Z_t < s) ≤ e^{−Ω(L ln n)}` and a union over the
`O(log n)` positions `t < s` is `o(1)` for `L` large. Hence

```
n − vs(identity) ≥ log_b n − log_b ln n − O(1)    whp,    i.e.    n − pw ≥ (1 − o(1)) log_b n .
```

The sandwich on record is `2 log_b n ≲ n − pw ≤ (4 + ε) log_b n` (the lower end
`n − pw ≥ α(G) = (2 + o(1)) log_b n`, the upper end Theorem B). The random ordering gives
the coefficient **1**: consistent with the bracket, weaker than both ends, and not the
upper end at `p` fixed. It is also sharp for the identity ordering itself (the `O(1)`
variance at `t*` gives, by Chebyshev, `n − vs(identity) ≤ log_b n + ω(n)` whp for any
`ω(n) → ∞`), so the optimum ordering gains between `(1 + o(1)) log_b n` and
`(3 + o(1)) log_b n` over a random one in this regime.

### 5.2 Middle, `c = c(n) → ∞`

`1 − β_typ(c) = (ln c + 1)/c · (1 + o(1))`, so the random ordering says `n − pw ≥ (1 + o(1))
n ln c / c` in the sense of `n − vs(identity) = n (ln c + 1)/c (1 + o(1))`. The sandwich on
record is `2 n ln c / c ≲ n − pw ≤ 4 n ln c / c` (Frieze 1990 for `α(G)`, Theorem M). The
random ordering's coefficient is **1**, below Frieze's `2`: Frieze's independence number
remains the better upper end asymptotically; the ratio `c (1 − β_typ(c)) / ln c` is `1.33,
1.28, 1.24, 1.21, 1.14, 1.07` at `c = 10, 20, 50, 100, 10³, 10⁶`. Two caveats, both in the
random ordering's favour at finite `c`: Frieze's `(2 + o(1))` is asymptotic in `c`, with no
explicit constant at a fixed `c` in the papers we hold, so for fixed `c` the explicit upper
line is `min(E_c, β_typ(c))`; and on the 320 middle-regime graphs at `n ≤ 60` the *measured*
`n − α` is better than the identity width by only `0.2–2` stacks per cell (§6.2), at sizes
where `ln c` is a few units.

### 5.3 Summary of the upper ends per regime

| regime | floor | upper end | random ordering's place |
|---|---|---|---|
| sparse, `c < 14.42` fixed | `β*(c)`, separator and closed-pair counts | Edwards–McDermid `E_c` | above Edwards–McDermid; not the end |
| sparse, `c ≥ 14.42` fixed | `β*(c)` | **`β_typ(c)` (this session)** | the end |
| middle, `c → ∞` | `n − 4 n ln c / c` | `n − α(G) ≈ n − 2 n ln c / c` (Frieze) | `n − (1 + o(1)) n ln c / c`, weaker |
| dense, `p` fixed | `n − (4 + ε) log_b n` | `n − α(G) ≈ n − 2 log_b n` | `n − (1 − o(1)) log_b n`, weaker |

## 6. Numbers

### 6.1 The constants

The tables of §3 and §4. Measured slopes for comparison: the sparse pilot's `0.099, 0.268,
0.415` at `c = 3, 6, 10` (`reports/random_graph_first_moment.md`); the middle-regime
`pw/n` of `0.33–0.40` on the `log n` cells, `0.53–0.63` at `n^{0.7}`, `0.63–0.77` at `p = ½`
(`reports/random_graph_middle.md` §4). Against them `β_typ` is a ceiling and not an
estimate: `0.423` against `0.099` at `c = 3`.

### 6.2 The identity-ordering width of the middle-regime graphs

`middle_identity.py` computes, for each of the 320 proved graphs of
`reports/scratch/random_graph_middle/results.csv` (the cells of
`paper1/latex/data/random_graph_middle.csv`; graph6 in the results file), the width of the
identity ordering (the vertex order of the graph6 string, which is the generator's labelling
and independent of the edges) — one loop, no solver — beside `max_t μ_t`, `β_typ(c) n`, and
the cell's other ceilings; `finite_ceiling.py` adds `w_{0.05}`, the least `w` with
`Σ_t P(Bin(n − t, 1 − (1 − p)^t) > w) ≤ 0.05`, which is the Lean theorem evaluated.

| cell | `n` | `c` | pw mean | identity width mean (min–max) | `max_t μ_t` | `β_typ n` | `n − α` | E–M | `w_{0.05}` | best ceiling |
|---|---|---|---|---|---|---|---|---|---|---|
| `√n` | 30 | 5.48 | 9.85 | 18.10 (16–21) | 17.61 | 16.95 | 17.80 | 12.28 | 21 | E–M |
| `2 ln n` | 30 | 6.80 | 11.65 | 19.40 (17–22) | 19.20 | 18.41 | 19.20 | 15.01 | 23 | E–M |
| `n^0.7` | 30 | 10.81 | 16.00 | 23.00 (19–25) | 22.36 | 21.25 | 21.90 | 20.31 | 25 | E–M |
| `p = ½` | 30 | 15.00 | 19.25 | 24.55 (22–27) | 24.38 | 22.96 | 23.65 | 22.97 | 26 | E–M |
| `√n` | 40 | 6.32 | 13.90 | 25.60 (21–29) | 24.63 | 23.91 | 24.60 | 18.74 | 29 | E–M |
| `2 ln n` | 40 | 7.38 | 15.80 | 26.75 (23–32) | 26.09 | 25.26 | 25.90 | 21.47 | 30 | E–M |
| `n^0.7` | 40 | 13.23 | 23.05 | 31.45 (29–34) | 31.01 | 29.78 | 30.25 | 29.46 | 34 | E–M |
| `p = ½` | 40 | 20.00 | 28.15 | 34.55 (33–36) | 33.91 | 32.32 | 33.00 | 33.00 | 36 | E–M / `n − α` |
| `√n` | 50 | 7.07 | 18.55 | 34.40 (30–38) | 31.90 | 31.12 | 31.80 | 26.34 | 37 | E–M |
| `2 ln n` | 50 | 7.82 | 20.20 | 34.60 (31–37) | 33.07 | 32.20 | 32.95 | 28.36 | 38 | E–M |
| `n^0.7` | 50 | 15.46 | 30.55 | 41.50 (38–44) | 39.82 | 38.50 | 39.05 | 38.89 | 43 | E–M |
| `p = ½` | 50 | 25.00 | 37.20 | 43.95 (42–46) | 43.59 | 41.83 | 42.50 | 43.02 | 46 | `n − α` |
| `√n` | 60 | 7.75 | 23.45 | 40.70 (37–45) | 39.36 | 38.51 | 39.30 | 33.83 | 45 | E–M |
| `2 ln n` | 60 | 8.19 | 24.30 | 40.75 (38–44) | 40.10 | 39.21 | 39.65 | 34.86 | 45 | E–M |
| `n^0.7` | 60 | 17.57 | 37.60 | 49.30 (47–52) | 48.75 | 47.37 | 47.55 | 48.05 | 52 | `n − α` |
| `p = ½` | 60 | 30.00 | 46.05 | 53.90 (52–55) | 53.28 | 51.43 | 52.05 | 53.02 | 55 | `n − α` |

Three readings. (i) The identity width sits `0.2–2.5` above `max_t μ_t` in every cell — the
fluctuation and the maximum over `t` — and `w_{0.05}` from the finite theorem equals the
cell's largest identity width `± 1` in all 16 cells: **the theorem is tight for what it
states**, the width of one fixed ordering. (ii) `β_typ(c) n`, the asymptotic constant, is
`1–2.5` below `max_t μ_t` at these `n` because `(1 − c/n)^t ≤ e^{−ct/n}`; the `+ c²` of
Theorem R bounds that excess crudely (`c²` is `30–900` here), so the table reports the
exact `max_t μ_t` beside it. (iii) Among the ceilings, Edwards–McDermid wins at
`c ≤ 15.5` and the measured `n − α` at the three densest cells; the identity ordering is
never the best on these graphs, by `0.2–2` against `n − α` — consistent with §5.2, where it
loses asymptotically to `n − α` by the factor `(ln c + 1)/(2 ln c)`.

### 6.3 The finite theorem at fixed `c`

`w_{0.05}/n` from `finite_ceiling.py`: at `c = 3`, `0.550, 0.517, 0.480, 0.461` for `n = 60,
120, 400, 1,000` against `β_typ(3) = 0.423`; at `c = 6`, `0.700, 0.667, 0.635, 0.619`
against `0.586`; at `c = 10`, `0.783, 0.758, 0.735, 0.721` against `0.694`; at `c = 20`,
`0.883, 0.858, 0.838, 0.828` against `0.808`. The approach is the `√(n ln n)/n` of Theorem
R: `0.038` at `n = 1,000`, `c = 3`, against `√(ln n / n) = 0.083` — the union bound over `t`
is loose by a constant there, as it must be, since only the positions near `t*` matter.

## 7. Lean

`lean/MOSPFormalization/RandomOrdering.lean` (registered in `MOSPFormalization.lean` after
`LayoutMoment`), 18 theorems, no `sorry`; `#print axioms` on the eight named below:
`propext`, `Classical.choice`, `Quot.sound` only
(`reports/scratch/random_ordering/axiom_check.log`); `lake build MOSPFormalization.RandomOrdering`
and the root `lake build` both pass (`full_build.log`, 8,993 jobs).

| statement | Lean |
|---|---|
| `binomTail m q w = Σ_{w < j ≤ m} C(m, j) q^j (1 − q)^(m − j)`, nonnegative for `0 ≤ q ≤ 1` | `binomTail`, `binomTail_nonneg` |
| `binomTail m q w ≤ e^{−λw} (1 − q + q e^λ)^m` for `λ ≥ 0` (Lemma 2, generating-function form) | `binomTail_le_exp` |
| `DeterminedOutside` is inherited by subsets; `univ` is determined outside anything | `DeterminedOutside.mono`, `determinedOutside_univ` |
| **independent blocks**: weight of "edges inside each disjoint `F j` form a pattern of `P j`" `= ∏_j (Σ_{S ∈ P j} p^{|S|} (1 − p)^{|F j| − |S|}) · weight(E)` | `sum_gnpWeight_blocks` |
| the pairs from `v` into `A`: `|·| = |A|` for `v ∉ A`, in `edges ⊤`, pairwise disjoint across `v` | `prefixPairs`, `card_prefixPairs`, `prefixPairs_subset_top`, `prefixPairs_disjoint` |
| `v ∈ activeSuffix G σ i ↔ v` in the suffix and some pair into the prefix is an edge | `mem_activeSuffix_iff_inter` |
| the nonempty patterns on `F` weigh `1 − (1 − p)^{|F|}`; total weight `1` | `sum_nonempty_patterns`, `sum_gnpWeight_univ` |
| **law of the active suffix**: `P(activeSuffix = B) = q^{|B|} (1 − q)^{m − |B|}`, `q = 1 − (1 − p)^t` | `sum_gnpWeight_activeSuffix_eq` |
| **Lemma 1**: `P(vertexSepAt G σ i > w) = binomTail m q w`, exactly | `sum_gnpWeight_vertexSepAt_gt` |
| **union bound**: `P(vertexSepOfLayout G σ > w) ≤ Σ_{i < n} binomTail (n − i − 1) (1 − (1 − p)^{i+1}) w` | `sum_gnpWeight_vertexSepOfLayout_gt_le` |
| **Theorem R**: `P(pathwidth > w) ≤` the same sum; complement `P(pathwidth ≤ w) ≥ 1 − Σ` | `sum_gnpWeight_pathwidth_gt_le`, `sum_gnpWeight_graphsOfPathwidthLe_ge` |

On paper only: Hoeffding's lemma (so the explicit `exp(−2a²/m)`), the two elementary
inequalities bounding `μ_t` by `β_typ(c) n + c²`, the calculus of §3 and the asymptotics.
`FirstMomentAsymptotics.lean` has the analytic tools for a `tendsto` statement; it was not
attempted, since the paper quotes the finite inequality and `β_typ` as a number.

**Brute force before statement.** `brute_check.py`: for `n = 1..7`, every labelled graph
(`2^{C(n,2)}`; `2,097,152` at seven), the identity ordering, `w = 0..n − 1`,
`p ∈ {1/2, 1/3, 3/10, 9/10}`, the graphs are counted by edge count inside each event and
the weight `Σ_e count_e p^e (1 − p)^{C − e}` is formed in exact rationals: the per-position
weight of `{k_t > w}` equals `binomTail` at every `(n, w, t, p)`, and the weight of
`{max_t k_t > w}` is at most the sum; 672 checks, zero discrepancies (`brute_check.log`).

**The root build.** Before this session `lake build` of the root failed:
`MOSPFormalization.lean` imports `LayoutMoment` (added 2026-11-11, `6ea923e99`) and
`SeparatorMoment` (loop0011), and both defined `relabel`; the second-moment session had
built its module alone (`reports/layout_second_moment.md` §6 gives
`lake build MOSPFormalization.LayoutMoment`). `LayoutMoment.relabel` is renamed
`layoutRelabel` (its lemma names `prefixSet_relabel`, `*_comap_relabel`, `layoutRelabel_apply`
keep their meaning; no statement changed); the pairwise import and the root now build. A
second clash was avoided by naming this file's pair sets `prefixPairs`
(`SeparatorMoment.lean` has `starPairs` with the same definition and `card_starPairs`).

## 8. Paper text, proposed and not applied

**Appendix E, after the paragraph *Between the two regimes*** (`paper1/latex/sec9e_appendix_random.tex`,
before `\begin{figure}` of Figure `fig:middle`), verbatim:

```latex
\paragraph{A trivial upper bound.}
The upper end of the sandwich at fixed $c$ has been the degree-sequence bound
of \citet[Corollary~5.2]{EdwardsMcDermid2015}. A bound that needs no structure
at all beats it from $c\approx14.4$ on. Fix any ordering $v_{1},\dots,v_{n}$ of
the vertices, the identity say, and expose $G(n,p)$. At step $t$ the vertex
separation counts the suffix vertices with a neighbour among $v_{1},\dots,v_{t}$;
the indicator of $v_{j}$ depends only on the $t$ pairs $v_{i}v_{j}$, $i\le t$,
and these $t$-sets are disjoint across $j$, so the count is exactly
$\mathrm{Bin}(n-t,\,1-(1-p)^{t})$~\leanref{randomordering}. Hoeffding's
inequality~\citep{Hoeffding1963} and a union bound over the $n$ positions give,
for $p=c/n$ with $c\le n/2$,
\[
  \Pr\bigl[\mathrm{pw}(G(n,c/n))>\beta_{\mathrm{typ}}(c)\,n+c^{2}+\sqrt{n\ln n}\bigr]\le 1/n,
  \qquad
  \beta_{\mathrm{typ}}(c)=\max_{0\le x\le1}(1-x)\bigl(1-e^{-cx}\bigr),
\]
since the pathwidth is at most the vertex separation of any one ordering. The
maximiser is unique and solves $(1-x)\,c\,e^{-cx}=1-e^{-cx}$; in
$y=e^{-cx}$ the condition is $y\ln y+(c+1)y=1$ and
$\beta_{\mathrm{typ}}(c)=(1-y)^{2}/(cy)$; asymptotically
$\beta_{\mathrm{typ}}(c)=1-(\ln c+1)/c+(\ln c)/c^{2}+O(\ln^{2}c/c^{3})$.
Its values are $0.423$, $0.586$, $0.694$ at $c=3,6,10$, above the
degree-sequence bound's $0.183$, $0.458$, $0.656$; the two cross once, at
$c_{0}=14.42$, and from there the random ordering is the better one:
$0.808$ against $0.826$ at $c=20$, $0.903$ against $0.930$ at $50$, $0.944$
against $0.965$ at $100$ (the degree-sequence weights satisfy
$1-g(d)=3.5/d+O(1/d^{2})$ numerically, so that bound is $1-3.5/c+o(1/c)$
against $1-(\ln c+1)/c$). So the provable sandwich on $\mathrm{pw}/n$ at fixed
$c$ has Edwards and McDermid's bound as its upper end for $c<14.42$ and the
width of a random ordering for $c\ge14.42$: $[0.554,0.808]$ at $c=20$,
$[0.761,0.903]$ at $50$, $[0.857,0.944]$ at $100$. In the other two regimes
the same computation is consistent with the brackets above and weaker than
their ends: at $p$ fixed the random ordering's width is
$n-(1+o(1))\log_{b}n$, coefficient $1$ against the $[2,4]$ of the
independence number and Theorem~B; for $c\to\infty$ it is
$n-(1+o(1))\,n\ln c/c$, coefficient $1$ against Frieze's $2$, so the
independence number remains the better upper end there. The finite
inequality, evaluated at level $0.05$ on the 320 graphs of
Figure~\ref{fig:middle}, equals the largest identity-ordering width of each
cell to within one, and the identity ordering is never the best ceiling on
those graphs, losing to $n-\alpha(G)$ by $0.2$ to $2$ per cell. We found no
prior statement of the width of a random ordering as a pathwidth bound on
$G(n,p)$, in the searches recorded for this appendix.
```

**Appendix A, one row** (`paper1/latex/sec9a_appendix_lean.tex`, after `firstmomentM`):

```latex
\leanentry{randomordering}{The paragraph \emph{A trivial upper bound} of Appendix~\ref{app:random}: along any fixed layout the vertex separation at a position with $t$ prefix and $m$ suffix vertices is $\mathrm{Bin}(m,1-(1-p)^{t})$ exactly (the edges at pairwise disjoint blocks of pairs are independent, iterating the independence lemma of the layout moment); hence for $0\le p\le1$ the weighted sum over graphs of pathwidth above $w$ is at most $\sum_{i<n}\Pr[\mathrm{Bin}(n-i-1,1-(1-p)^{i+1})>w]$, with its complement, and the generating-function bound $\Pr[\mathrm{Bin}(m,q)>w]\le e^{-\lambda w}(1-q+qe^{\lambda})^{m}$ for $\lambda\ge0$; the Hoeffding step and the maximum over $t$ are on paper} \leannames{sum_gnpWeight_blocks, sum_gnpWeight_activeSuffix_eq, sum_gnpWeight_vertexSepAt_gt, sum_gnpWeight_vertexSepOfLayout_gt_le, sum_gnpWeight_pathwidth_gt_le, sum_gnpWeight_graphsOfPathwidthLe_ge, binomTail_le_exp} \\
```

**`refs.bib`.** `EdwardsMcDermid2015` and `Frieze1990` are present. `Hoeffding1963` is not;
proposed entry:

```bibtex
@article{Hoeffding1963,
  author  = {Hoeffding, Wassily},
  title   = {Probability inequalities for sums of bounded random variables},
  journal = {Journal of the American Statistical Association},
  volume  = {58}, number = {301}, pages = {13--30}, year = {1963},
  doi     = {10.1080/01621459.1963.10500830}
}
```

(Textbook; not in `literature/`. If the owner prefers a held source, the inequality can be
replaced by the Lean lemma `binomTail_le_exp` with `λ = ln((1 + a/μ))`, which gives the
Chernoff form `(e^{δ}/(1 + δ)^{1 + δ})^{μ}` with no citation, at the cost of a less
familiar exponent.)

Two sentences elsewhere in Appendix E become stale and should be reworded with the
paragraph: "the best published upper bound, the degree-sequence bound of ... so the
provable sandwich on `pw/n` is `[0.037, 0.183]`, `[0.182, 0.458]` and `[0.345, 0.656]`
there" (§*What is checked*, line ~688) stays true at `c = 3, 6, 10` but should say "the
upper end for `c < 14.42`"; and the Table `tab:excess` remark that Edwards–McDermid is "the
best published upper bound we know" is still true as *published*. The main text's
sandwich sentence of the sparse regime (`sec9e`, line ~640, "the measured slopes sit near
the middle of the sandwich between `β*(c)` and it") is unaffected at `c ≤ 10`.

A short paragraph for `CLAUDE.md`, if the owner wants the index entry (proposed, not
applied): *"The random-ordering bound (2026-11-11, `reports/random_ordering_bound.md`): the
width of the identity ordering of `G(n, p)` is `max_t Bin(n − t, 1 − (1 − p)^t)` with the
counts exact at every position; `pw(G(n, c/n)) ≤ β_typ(c) n + c² + √(n ln n)` with
probability `≥ 1 − 1/n`, `β_typ = max_x (1 − x)(1 − e^{−cx}) = 1 − (ln c + 1)/c + (ln c)/c² +
…`; crosses Edwards–McDermid once at `c₀ = 14.421` and is the upper end of the fixed-`c`
sandwich from there (`0.808` vs `0.826` at 20, `0.903` vs `0.930` at 50); coefficient 1
against the `[2, 4]` brackets in the middle and dense regimes, so weaker there.
`RandomOrdering.lean`, 18 theorems, no sorry; brute-forced to `n = 7`. The root `lake build`
was broken by a `relabel` clash between `LayoutMoment` and `SeparatorMoment`, fixed by
renaming."*

## 9. Literature

No search was run this session. The claim that the random ordering's width has not been
stated as a pathwidth bound on `G(n, p)` is the one made in
`reports/layout_second_moment.md` §5 ("no expected width of a random ordering" among the
thirteen papers recorded in `literature/MISSING.md` under "Second moment on layouts"), and
is bounded to that search. What is certainly known and not claimed: the binomial law of the
number of vertices adjacent to a fixed set in `G(n, p)` (elementary); Hoeffding's inequality
(1963); the degree-sequence bound (Edwards & McDermid 2015, `literature/`); Frieze's
independence number (1990, cited, not held); the greedy independent set of `G(n, c/n)`,
whose size `~ n ln(1 + c)/c` would give a fixed-`c` ceiling `1 − ln(1 + c)/c` that loses to
`β_typ(c)` at every `c ≥ 2` (`0.848` against `0.808` at `c = 20`) — stated here from memory
of the differential-equation method and **not checked against a held paper**; it is not
used.

## 10. Regenerate

```bash
cd /home/al/dev/MOSP
# the finite statement, every labelled graph to n = 7, exact rationals (≈ 1 min)
nice -19 python reports/scratch/random_ordering/brute_check.py 7
# beta_typ, x*, asymptotics, the crossover, the dense and middle regimes
nice -19 python reports/scratch/random_ordering/calculus.py
# beta_star at the table's c, Edwards–McDermid in log space to c = 10^4, g(d) asymptotics, sign changes
nice -19 python reports/scratch/random_ordering/em_large_c.py
# the identity width of the 320 middle-regime graphs (no solver)
nice -19 python reports/scratch/random_ordering/middle_identity.py
# the finite theorem at level 0.05 per cell and at fixed c
nice -19 python reports/scratch/random_ordering/finite_ceiling.py
# Lean
cd lean && taskset -c 16-23 lake build MOSPFormalization.RandomOrdering && taskset -c 16-23 lake build
taskset -c 16-23 lake env lean ../reports/scratch/random_ordering/axiom_check.lean
```

## 11. What remains

1. The `tendsto` form in Lean (`P(pw > (β_typ(c) + ε) n) → 0`): Hoeffding's lemma on
   `1 − q + q e^λ` and the bound `μ_t ≤ β_typ(c) n + c²` are the two analytic steps;
   `FirstMomentAsymptotics.lean` has the pattern. Not needed for the paper's table.
2. The width of the *best of `k` random orderings* or of a one-pass greedy ordering would
   lower the ceiling below `β_typ`; the min-of-`k` relabelling study (`reports/ml_nature.md`
   §18) measured the witness side only on MOSP instances. Not attempted; a greedy's width
   on `G(n, c/n)` is a differential-equation computation, not a one-line one.
3. The two sentences of Appendix E flagged in §8, and the paragraph, are for the owner.
