# The pathwidth of `G(n, p)` in the middle regime: `np → ∞`, `p → 0`

*2026-11-11, one session. Theorem M and its proof (§1–§2), the literature (§3, by a search
agent, nothing downloaded), the measurement (§4; `reports/scratch/random_graph_middle/`),
Lean (§5; `lean/MOSPFormalization/FirstMomentAsymptotics.lean`, section "The middle
regime"), the paragraph for Appendix E and the row for Appendix A (§6). Every number is
beside its command in §7.*

## 0. Summary

**The gap.** The first-moment lower bound on the pathwidth of `G(n, p)` was done in two
regimes: `p = c/n` with `c` fixed (Theorem A, `reports/random_graph_first_moment.md`:
`pw ≥ β*(c) n` whp for `c > 4 ln 2`, `1 − β*(c) ~ 4 ln c / c`) and `p` fixed (Theorem B:
`n − pw ≤ (4 + ε) log_{1/(1−p)} n` whp). Between them — average degree `c = np → ∞` with
`p → 0`, as `log n`, `√n`, `n^{0.7}` — there was no statement of ours and no data, although
the finite inequality behind both theorems holds for every `p`
(`weightedSum_graphsOfPathwidthLe_le`, `FirstMoment.lean`).

**The theorem (Theorem M, §1).** For every real `c > 1` with `4 ln c < c` (so for every
`c ≥ 9`) and every integer `n ≥ max(3, c)`,

```
P( pw(G(n, c/n)) ≤ (1 − 4 ln c / c)·n ) ≤ exp( −(4 ln c / c)(ln(2 ln c) − 1)·n + 3 ln n + 2 ln c ),
```

and for `c ≤ n` the exponent is at most `−ln c · (4 ln(2 ln c) − 9)`, which tends to `−∞`
with `c`. Hence **for every sequence `c = c(n) → ∞` with `c ≤ n`,
`n − pw(G(n, c/n)) ≤ 4 n ln c / c` with probability `1 − o(1)`**: the whole range
`np → ∞`, `p ≤ 1`, in one statement, the middle regime and the dense regime alike. It is
Theorem A read with `c = c(n)` — Theorem A's finite form never needed `c` fixed — plus one
new inequality on its rate, `δ(β, c) ≥ a (c a + 2 ln a − 2)` with `a = (1 − β)/2`, which at
`a = 2 ln c / c` is `(4 ln c / c)(ln(2 ln c) − 1)`. The error term is better than the
`(2 + o(1))√(2 ln 2 / c)` the brief expected: that constant is what a `4^n` count of the
pairs gives, and the entropy count already in Theorem A gives `4 ln c / c`, which is
smaller by a factor `√c / ln c`. The honest calculus (§2.1) says the first moment cannot do
better than `(4 ln c − 4 ln ln c + 4 − 4 ln 2 + o(1)) / c` (Theorem A″ of the earlier
report, now read as a statement about `c(n)`), and the constant `4` is the right one for
this method: the upper side is `n − pw ≥ α(G) = (2 + o(1)) n ln c / c` (Frieze 1990), so
**`2 ≤ lim (n − pw) c / (n ln c) ≤ 4`** throughout the middle regime, the same sandwich
`[2, 4]` as in the dense regime with `log_b n` in place of `n ln c / c`.

**How it sits between A and B (§2).** *Against A:* for fixed `c` the exact threshold
`β*(c)` is always above `1 − 4 ln c / c` (`0.857` against `0.816` at `c = 100`, `0.978`
against `0.972` at `10³`); Theorem M is Theorem A's closed form, valid once `c ≥ 9`, and the
closed form of A″'s bracket overtakes it only beyond `c ≈ 230`. *Against B:* at `p` fixed,
`c = pn` gives `n − pw ≤ 4 n ln(pn)/(pn) = (4/p) ln n + O(1)`, against Theorem B's
`(4 + ε) ln n / ln(1/(1 − p))`; since `ln(1/(1 − p)) ≥ p` Theorem B is stronger by the
factor `p / ln(1/(1−p))` (`0.72` at `p = ½`), and the two agree to first order as `p → 0`.
*One statement for all three regimes:* replacing `c = np` by `λ = n ln(1/(1 − p)) ≥ c`
throughout — the proof is identical, with the identity `(1 − p)^m = e^{−λ m / n}` in place
of Lemma 2's `(1 − p)^m ≤ e^{−pm}` — gives Theorem M with `λ` for every `0 < p < 1`, which
at `p` fixed reads `n − pw ≤ 4 log_b n + 4 log_b ln b`: Theorem B's constant `4` with no
`ε` and the second-order term explicit (`−2.1` at `p = ½`). That form is on paper (§2.3);
Lean has the `c` form, which is the brief's.

**The literature (§3).** We found no published statement of `n − pw`, `n − vs` or `n − tw`
of order `n ln c / c`, with or without a constant, when `np → ∞` and `p → 0`. What is in
print: Perarnau & Serra (2014, Thm 1.1 and §3) `tw ≥ n − 3√(ln 3 / 2)·n/√c`, i.e.
`n − O(√(n/p))`, by a `3^n` count — weaker by a factor `√c / ln c`, and they write that
dense treewidth "has not been studied before"; Wang, Liu, Cui & Xu (2011, abstract)
`tw ≥ n − o(n)` for `p ≫ 1/n`, rate not visible; Cheung & Girardet (2020, Lemma 7)
`vs ≥ (1 − δ) n` for `p ≥ n^{−1+ε}`, no rate; Lee, Lee & Oum (2012, Thm 1.1(ii)) rank-width
`n/3 − o(n)` for `1/n ≪ p ≤ ½`, which says `tw ≥ n/3 − o(n)` only; Turner (1986, Thm 2.2)
`bw ≥ (1 − ε) n` for `p ≥ c log n / n`, a bandwidth statement that bounds nothing about
pathwidth. Theorem M implies the pathwidth analogue of each of the first three and is
incomparable with the treewidth ones (a treewidth floor implies a pathwidth floor, not
conversely). Nothing was found between 2020 and 2026 either. "We found no prior statement",
bounded to §3's list.

**The data (§4).** `n ∈ {30, 40, 50, 60}`, `c ∈ {2 ln n, √n, n^{0.7}}` and the dense control
`p = ½`, 20 graphs per cell, every one of the 320 proved by the C program (286 by
refutation, 34 by minor, 167 s in all, the slowest graph 14 s); the sparse control `c = 3`
is the pilot's first 20 graphs per `n`, proved on 2026-10-18 and not re-run. Per cell the
proved pathwidth against the floors and ceilings (all in units of `n`; `k₀.₀₅` is the finite
inequality evaluated exactly, the largest `k` with `P(pw ≤ k) ≤ 0.05`; blank where a floor
is not positive):

| `n` | cell | `c` | pw min / median / max | `k₀.₀₅`+1 | `β*(c) n` | Thm M | `n − α` | deg-seq |
|---|---|---|---|---|---|---|---|---|
| 30 | `c = 3` | 3.0 | 3 / 4.5 / 8 | — | 0.3 | — | 13.9 | 4.9 |
| 30 | `√n` | 5.48 | 9 / 10 / 11 | 6 | 4.3 | — | 17.8 | 12.3 |
| 30 | `2 ln n` | 6.80 | 9 / 11 / 13 | 8 | 6.3 | — | 19.2 | 15.0 |
| 30 | `n^0.7` | 10.81 | 15 / 16 / 18 | 14 | 10.9 | 3.6 | 21.9 | 20.3 |
| 30 | `p = ½` | 15.0 | 16 / 19 / 20 | 18 | 14.1 | 8.3 | 23.7 | 23.0 |
| 40 | `c = 3` | 3.0 | 4 / 6 / 8 | — | 0.3 | — | 18.8 | 7.1 |
| 40 | `√n` | 6.32 | 11 / 14 / 16 | 8 | 7.5 | — | 24.6 | 18.7 |
| 40 | `2 ln n` | 7.38 | 14 / 16 / 18 | 12 | 9.4 | — | 25.9 | 21.5 |
| 40 | `n^0.7` | 13.23 | 21 / 23 / 25 | 20 | 17.2 | 8.8 | 30.3 | 29.5 |
| 40 | `p = ½` | 20.0 | 26 / 28 / 29 | 26 | 22.1 | 16.0 | 33.0 | 33.0 |
| 50 | `c = 3` | 3.0 | 5 / 7.5 / 10 | — | 0.4 | — | 23.3 | 8.8 |
| 50 | `√n` | 7.07 | 16 / 18.5 / 22 | 12 | 11.1 | — | 31.8 | 26.3 |
| 50 | `2 ln n` | 7.82 | 17 / 20 / 23 | 14 | 12.8 | — | 33.0 | 28.4 |
| 50 | `n^0.7` | 15.46 | 29 / 30 / 33 | 26 | 23.9 | 14.6 | 39.1 | 38.9 |
| 50 | `p = ½` | 25.0 | 36 / 37 / 38 | 34 | 30.7 | 24.2 | 42.5 | 43.0 |
| 60 | `c = 3` | 3.0 | 6 / 8.5 / 10 | — | 0.5 | — | 28.4 | 10.3 |
| 60 | `√n` | 7.75 | 22 / 23.5 / 26 | 16 | 15.1 | — | 39.3 | 33.8 |
| 60 | `2 ln n` | 8.19 | 22 / 24 / 26 | 18 | 16.2 | — | 39.7 | 34.9 |
| 60 | `n^0.7` | 17.57 | 36 / 37.5 / 40 | 34 | 31.0 | 20.8 | 47.6 | 48.0 |
| 60 | `p = ½` | 30.0 | 45 / 46 / 47 | 44 | 39.4 | 32.8 | 52.1 | 53.0 |

Three readings. (i) **No proved value is below a deterministic floor**, as it must be,
and the finite inequality evaluated exactly is the strongest floor by far: `k₀.₀₅ + 1`
is within 0–6 of the smallest proved pathwidth in every cell where it is positive
(`44` against a minimum of 45 at `n = 60`, `p = ½`; `34` against `36` at `n^{0.7}`), with one
graph of the 320 below it — `n = 30`, `p = ½`, pathwidth 16 against `k₀.₀₅ = 17`, where
the inequality says `P(pw ≤ 17) ≤ 0.0467` and one such graph in twenty is within the
level. The closed forms are far below it at these `c`: `β*(c) n` by 2–7 and Theorem M's
`(1 − 4 ln c / c) n` by 8–15, because `4 ln c / c` is still `0.45` at `c = 30`. The theorem
is an asymptotic statement; at `n ≤ 60` the finite inequality is what to evaluate. (ii) The
ceilings bracket from above by about as much: `n − α(G)` is the better one at `c ≤ 8` and
the degree-sequence term at `c ≥ 13`, the two crossing near `c = 13`; the Poisson limit of
the degree-sequence term is within `0.7` of its realised mean on every cell. (iii) The
proved `pw / n` rises from `0.14–0.17` at `c = 3` through `0.33–0.40` on the `log n` cells
and `0.53–0.63` at `n^{0.7}` to `0.63–0.77` at `p = ½`. The ratio `(n − pw) c / (n ln c)` of
the cell means is `1.98–2.36`, falling slowly with `c` (`2.3` on the `log n` cells, `2.2`
at `n^{0.7}`, `2.0` at `p = ½`) — numerically inside the sandwich `[2, 4]` of §2.1, but not
yet an asymptotic reading: at `c ≤ 30` the second-order terms `ln ln c`, `ln 2` and `1` are
the size of `ln c` itself (`α(G)`'s formula gives `10.0` at `n = 60`, `c = 30` against a
realised mean of `8.0`). The finite-`n` comparison is the `k₀.₀₅` column, and there the
truth sits at `0.25–0.38` of the way from the floor to the better ceiling on the `n^{0.7}`
and dense cells and at `0.37–0.61` on the `log n` cells. The figure
(`paper1/figures/random_graph_middle.pdf`, `reports/figures/random_graph_middle.png`) shows
the five cells per `n` against the curves `1 − 4 ln c / c` and `β*(c)`.

**Lean (§5).** `FirstMomentAsymptotics.lean`, eleven new theorems, no `sorry`, axioms
`propext`, `Classical.choice`, `Quot.sound` only
(`reports/scratch/random_graph_middle/axiom_check.log`): the rate inequality
`firstMomentRate_ge`, its value at `β = 1 − 4 log c / c` (`firstMomentRate_mid`), Theorem M
in finite form (`firstMoment_pathwidth_le_mid`, hypotheses `1 < c`, `4 log c < c`, `3 ≤ n`,
`c ≤ n`; `firstMoment_pathwidth_le_mid'` with `9 ≤ c`, through `four_mul_log_lt_of_nine_le`),
the exponent bound `middle_exponent_le`, and the limit `tendsto_firstMoment_pathwidth_mid`:
for every sequence `c : ℕ → ℝ` with `c n → ∞` and eventually `c n ≤ n`, the `gnpWeight`-sum
over `graphsOfPathwidthLe ⌊(1 − 4 log (c n) / c n) · n⌋₊` on `Fin n` tends to `0`. The exact
statement was brute-forced before it was written (`lean_target_check.py`: `n = 3..300`,
24,904 grid points, zero violations, smallest slack `2.21` nats). The build is
`lake build MOSPFormalization.FirstMomentAsymptotics` (24 s) and the full library builds.

**What is not done.** The `λ` form (§2.3) and the `L`-family of thresholds (§2.1) are on
paper; the sandwich's lower end `α(G) = (2 + o(1)) n ln c / c` is cited (Frieze 1990, not
held); the paper is not edited — the paragraph and the row are in §6 for the owner. The
appendix's title question in the brief is moot: the owner retitled it "The pathwidth of
random graphs" in `0efa019bf` before this session.

---

## 1. Theorem M and its proof

Notation as in `reports/random_graph_first_moment.md`: `φ(x) = −x ln x`, `H(x, y, z) =
φ(x) + φ(y) + φ(z)`, `a = (1 − β)/2`, `δ(β, c) = c a² − H(a, a, 1 − 2a)`. The starting point
is Theorem A in its finite form, which holds for **every** real `c > 0` and integer
`n ≥ max(3, c)` — nothing in its proof uses that `c` is a constant:

```
P( pw(G(n, c/n)) ≤ ⌊βn⌋ ) ≤ exp( −δ(β, c)·n + 3 ln n + c·a ),     0 < β < 1.        (A)
```

**Lemma M1.** `φ(1 − x) ≤ x` for `0 ≤ x ≤ 1`.
*Proof.* `−ln(1 − x) = ln(1/(1 − x)) ≤ 1/(1 − x) − 1 = x/(1 − x)`, multiply by `1 − x`
(`x = 1`: `φ(0) = 0`). ∎

**Lemma M2 (the rate from below).** For `0 ≤ β ≤ 1` and every `c`,
`δ(β, c) ≥ a (c a + 2 ln a − 2)`.
*Proof.* `δ = c a² − 2φ(a) − φ(1 − 2a) = c a² + 2a ln a − φ(1 − 2a) ≥ c a² + 2a ln a − 2a`
by M1 at `x = 2a`. ∎

**Lemma M3.** For `c > 1` with `4 ln c ≤ c`, at `β = 1 − 4 ln c / c` (so `a = 2 ln c / c`):
`δ(β, c) ≥ (4 ln c / c)(ln(2 ln c) − 1)`.
*Proof.* `c a = 2 ln c` and `ln a = ln(2 ln c) − ln c`, so
`c a + 2 ln a − 2 = 2 ln(2 ln c) − 2`; multiply by `a`. ∎

**Theorem M (finite form).** For real `c > 1` with `4 ln c < c` and integer `n ≥ 3` with
`c ≤ n`, writing `β_M = 1 − 4 ln c / c ∈ (0, 1)`,

```
P( pw(G(n, c/n)) ≤ ⌊β_M n⌋ ) ≤ exp( −(4 ln c / c)(ln(2 ln c) − 1)·n + 3 ln n + 2 ln c ).     (M)
```

*Proof.* (A) at `β = β_M`, with `−δ n ≤ −(4 ln c / c)(ln(2 ln c) − 1) n` by M3 and
`c a = 2 ln c`. ∎

**Lemma M5.** `4 ln c < c` for `c ≥ 9` (the true threshold is `8.613`; the rate factor
`ln(2 ln c) − 1` is positive from `c > e^{e/2} = 3.89`).
*Proof.* `ln c = ln 9 + ln(c/9) ≤ ln 9 + c/9 − 1`, so `4 ln c < c` follows from
`4 ln 9 − 4 < 5c/9`, true at `c = 9` because `ln 9 < 9/4` (`e^{9/4} = e·e·e^{1/4} >
2.718² · 1.25 = 9.23`). ∎

**Lemma M6 (the exponent for `c ≤ n`).** Let `A = (4 ln c / c)(ln(2 ln c) − 1)` and suppose
`A c ≥ 3` (true for `c ≥ 9`: `A c = 4.2` there). Then for `0 < c ≤ n`,

```
−A n + 3 ln n + 2 ln c ≤ −ln c · (4 ln(2 ln c) − 9).
```

*Proof.* `3 ln(n/c) ≤ 3 (n/c − 1) = (3/c)(n − c) ≤ A (n − c)`, so
`−A n + 3 ln n ≤ −A c + 3 ln c`; add `2 ln c` and expand `A c = 4 ln c (ln(2 ln c) − 1)`. ∎

**Theorem M (the limit).** Let `c = c(n) → ∞` with `c(n) ≤ n` for all large `n`. Then
`P( pw(G(n, c/n)) ≤ ⌊(1 − 4 ln c / c) n⌋ ) → 0`; indeed it is at most
`c^{−(4 ln(2 ln c) − 9)}` for all large `n`, uniformly in how `c` grows.
*Proof.* For `n` large, `c ≥ 9`, `A c ≥ 3` and `c ≤ n`, so (M) and M6 give
`P ≤ exp(−ln c (4 ln(2 ln c) − 9)) = c^{−(4 ln(2 ln c) − 9)} → 0`. ∎

The bound is crude where `c ≪ n`: the true exponent of (M) is `−A n`, i.e. `−4 (n/c) ln c
(ln(2 ln c) − 1)`, exponential in `n/c`, and M6 keeps only the `n = c` end of it. It is what
makes a single hypothesis, `c ≤ n`, suffice; a sharper statement for `c = o(n)` reads
`P ≤ exp(−(4 n ln c / c)(ln(2 ln c) − 1)(1 − o(1)))`.

## 2. Where Theorem M sits

### 2.1 The calculus, done honestly: the `L`-family and the constant

Theorem M is one point of a one-parameter family. Put `a = (2/c)(ln c + L)`, i.e.
`1 − β = (4/c)(ln c + L)`. Lemma M2 gives

```
δ ≥ a · (c a + 2 ln a − 2) = (2 (ln c + L)/c) · 2 (L + ln(2 (ln c + L)) − 1),
```

positive iff `L + ln(2 ln c + 2L) > 1`. `L = 0` is Theorem M. The smallest admissible `L`
is `L = 1 − ln(2 ln c) + o(1)`, which gives `1 − β = (4 ln c − 4 ln ln c − 4 ln 2 + 4 + o(1))/c`:
exactly the asymptotic constant of Theorem A″, now read for `c = c(n)`. So the first
moment's floor in the middle regime is

```
n − pw ≤ (4 ln c − 4 ln ln c + 4 − 4 ln 2 + o(1)) · n / c      whp,
```

and the method cannot improve the leading constant `4`: it is `2t ln n`-bits of choice
for the pair against `t²` forbidden edges, the same accounting as in the dense case
(`reports/random_graph_first_moment.md` §2.5). The closed forms compare as follows
(`β`-values; `β*(c)` is the exact root of Theorem A′, the "A″ end" is
`1 − (4 ln c − 4 ln ln c + 4 ln 2 + 4)/c`, the explicit floor of Theorem A″ for `c ≥ 14`):

| `c` | 9 | 14 | 20 | 30 | 50 | 100 | 230 | 1,000 | 10⁴ |
|---|---|---|---|---|---|---|---|---|---|
| `β*(c)` | 0.302 | 0.447 | 0.554 | 0.657 | 0.761 | 0.857 | 0.926 | 0.978 | 0.997 |
| Theorem M, `1 − 4 ln c / c` | 0.024 | 0.246 | 0.401 | 0.547 | 0.687 | 0.816 | 0.905 | 0.972 | 0.996 |
| A″ end | — | 0.040 | 0.282 | 0.484 | 0.661 | 0.809 | 0.905 | 0.973 | 0.997 |

The A″ end overtakes Theorem M exactly when `4 ln ln c > 4 ln 2 + 4`, i.e. `c > e^{2e} =
229.7`; below that the `+4 ln 2 + 4` of the bracket costs more than the `−4 ln ln c` saves.
Either closed form is below `β*(c)` everywhere, which is why §4 compares the data with
`β*(c)` and with the finite inequality itself.

**Against the brief's expected form.** `pw ≥ n (1 − (2 + o(1))√(2 ln 2 / c))` is what one
gets by bounding the pair count by `4^n` (`C(n, t) C(n − t, t − 1) ≤ 2^n · 2^n`) and asking
`c a² > 2 ln 2`. The entropy count replaces `2 ln 2` by `2a ln(1/a) + 2a`, and the
threshold moves from `a ≈ √(2 ln 2 / c)` to `a ≈ 2 ln c / c`: an improvement by the factor
`√c / (√(2 ln 2) · 2 ln c)`, which is `1.5` at `c = 30` and `4.1` at `c = 1,000`. Nothing
new had to be proved for this: Theorem A's count is already the entropy count.

**The sandwich.** `pw ≤ n − α(G)` (`pathwidth_le_card_sub_indepNum`, `IndependenceBound.lean`)
and `α(G(n, p)) = (2n/c)(ln c − ln ln c − ln 2 + 1 + o(1))` whp for `c → ∞`, `c = o(n)`
(Frieze 1990, as quoted by Coja-Oghlan & Efthymiou 2011 eq. (23)), so

```
(2 ln c − 2 ln ln c − 2 ln 2 + 2 + o(1)) n / c  ≤  n − pw  ≤  (4 ln c − 4 ln ln c − 4 ln 2 + 4 + o(1)) n / c,
```

the two ends in the ratio `2 : 1` term by term. The dense sandwich
`(2 − o(1)) log_b n ≤ n − pw ≤ (4 + o(1)) log_b n` of the earlier report is the same
statement at `c = pn` (there `2 ln c / c · n = 2 ln(pn)/p ≈ (2/p) ln n`, and `1/p` against
`1/ln b` is the `λ` refinement of §2.3). Which end is the truth is open in both regimes.

### 2.2 Against Theorems A and B

*Theorem A* (`c` fixed) gives `β*(c)`, the exact first-moment threshold, with rate
`δ(β, c)` for `β < β*(c)`; Theorem M gives the explicit `1 − 4 ln c / c ≤ β*(c)` with the
explicit rate `(4 ln c / c)(ln(2 ln c) − 1) ≤ δ(β_M, c)`. For fixed `c ≥ 9` Theorem M is a
corollary of A with a weaker constant (the table above); for `c → ∞` it is the statement
A never made, because A′ and A″ were proved for a constant `c`. Where each is stronger:
A below `c ≈ 10` (M says nothing below `8.61`, A something from `2.77`), and for the
constant at any fixed `c`; M for growing `c`, where A's `β*(c(n))` is a sequence of
thresholds with no closed form and no uniform rate.

*Theorem B* (`p` fixed): `n − pw ≤ (4 + ε) log_b n` for `n ≥ b^{4/ε}`, `b = 1/(1 − p)`, with
probability `1 − n^{−1 − (ε/2) log_b n}`. Theorem M at `c = pn`: `n − pw ≤ 4 n ln(pn)/(pn) =
(4/p)(ln n + ln p)`, with probability `1 − (pn)^{−(4 ln(2 ln(pn)) − 9)}`. Since
`ln b ≥ p`, B's constant `4/ln b` is the smaller: at `p = ½`, B gives `4 log₂ n = 5.77 ln n`
and M gives `8 ln n` — B is stronger by the factor `p / ln b = 0.72`, and M's decay
`n^{−Θ(ln ln n)}` is slower than B's `n^{−Θ(ln n)}`. As `p → 0` the two constants agree
(`ln b = p + p²/2 + …`). At `n = 60`, `p = ½`: B's `n − 4 log₂ n = 36.4`, M's `32.8`, the
`λ` form below `38.5`, the finite inequality `44`, the truth `45–47`.

*Is there one statement?* The finite inequality (0) is one statement for every `p`, and
Theorem A's finite form (A) is one statement for every `c ≤ n`; Theorem M is the closed
form of (A) for `c ≥ 9`, which covers middle and dense. What it does not cover is the
sparse end `c < 8.61` (there A′ is needed, and nothing is positive below `4 ln 2`), and it
loses B's constant in the dense end. The `λ` form of §2.3 repairs the second.

### 2.3 The `λ` form: one closed form with Theorem B's constant (on paper)

Write `λ = n ln(1/(1 − p)) = −n ln(1 − p)`, so that `(1 − p)^m = e^{−λ m / n}` exactly and
`λ ≥ c = pn`. Theorem A's proof goes through with `λ` for `c` and no Lemma 2 (step (3)
becomes an equality in place of `(1 − p)^m ≤ e^{−pm}`), giving for every `0 ≤ p < 1`,
`0 < β < 1`, `n ≥ 3`:

```
P( pw(G(n, p)) ≤ ⌊βn⌋ ) ≤ exp( −δ(β, λ)·n + 3 ln n + λ·a ),                              (A_λ)
```

and Theorem M with `λ` for `c` under `1 < λ`, `4 ln λ < λ`, `n ≥ 3`, with no condition
`λ ≤ n` in the finite form (that condition only replaced `p ≤ 1`). At `p` fixed,
`λ = n ln b` and the floor reads

```
n − pw ≤ 4 n ln λ / λ = 4 log_b n + 4 log_b(ln b)      whp,
```

Theorem B's `4 log_b n` with `ε = 0` and the second-order term explicit (`4 log_b ln b =
−2.1` at `p = ½`, `−6.3` at `p = 0.1`, `+0.6` at `p = 0.8`), with probability
`1 − λ^{−(4 ln(2 ln λ) − 9)}` when `λ ≤ n`, i.e. `p ≤ 1 − 1/e`; for `p` above that the
limit needs the bound `λ ≤ Kn` and gives `1 − n^{−Θ(ln ln n)}` all the same. This is weaker
than B in the rate (`n^{−Θ(ln ln n)}` against `n^{−Θ(ln n)}`) and stronger in the
threshold (`ε = 0` and an explicit constant term), and it is the single closed form for
all of `np → ∞`. **Not in Lean**: the brief asked for the `c` form, and the `λ` form is the
same 120 lines with one identity in place of one inequality; it is the obvious next step
if the paper wants Theorem B subsumed.

## 3. The literature

By a search agent (WebSearch, WebFetch on arXiv/ar5iv/publisher pages, `pdftotext` on what it
could save), 2026-11-11; nothing downloaded into `literature/`; the heading "Random graphs:
the middle regime (2026-11-11)" of `literature/MISSING.md` records the papers worth
obtaining with links. Turner 1986 is held (`reports/scratch/first_moment/lit/`); Wang et
al. 2011, Frieze 1990 and Shang 2022 were read from abstracts or secondary citations only.

| paper | statement for `np → ∞`, `p → 0` | relation to Theorem M |
|---|---|---|
| Perarnau & Serra 2014, *DAM* 168:119–126, Thm 1.1 and §3 | `td = n − O(√(n/p))` and, by the same proof, `tw`; explicitly `tw > (1 − f(c)) n` for any `f(c) > 3√(ln 3/(2c))`, by a union bound over `≤ 3^n` partitions (Kloks' Lemma 2.1): `n − tw ≤ 2.22 n/√c`. "To our knowledge, the tree-width of a dense random graph has not been studied before." | incomparable as statements (theirs on `tw`, which implies a `pw` floor of the same weaker form); M's error term `4 n ln c / c` is smaller by `√c / (1.8 ln c)`. Their `3^n` replaced by the pair count would give `n − tw ≤ (9/2 + o(1)) n ln c / c` from the same lemma — not written anywhere we found. |
| Wang, Liu, Cui & Xu 2011, COCOA, LNCS 6831:491–499 | abstract: `tw ≥ n − o(n)` for `p ≫ 1/n` (and `tw ≤ tn`, `t < 1`, at `p = c/n`) | M implies the `pw` analogue with the rate; theirs is on `tw`; the theorem's text not seen |
| Cheung & Girardet 2020, *OJDM* 10(1):13–30 (arXiv 1710.10339), Lemma 7, Thm 4.5 | `MINVS ≥ (1 − δ) n − 1` whp for `p = Ω(n^{−c})`, `c < 1`; no rate | implied by M on its range (M gives the rate) |
| Lee, Lee & Oum 2012, *JGT* 70:339–347, Thm 1.1(ii) | rank-width `⌈n/3⌉ − o(n)` for `1/n ≪ p ≤ ½`; hence `tw ≥ n/3 − o(n)` | incomparable, far weaker for `pw` |
| Turner 1986, *SIAM J. Comput.* 15:561–580, Thm 2.2 | `bw ≥ (1 − ε) n` whp for `p ≥ c log n / n` | bandwidth: `pw ≤ bw`, so no implication either way |
| Díaz, Petit, Serna & Trevisan 2001, *DM* 235:245–253 (and Petit's thesis, eq. 3.9) | `vs ≥ (½ − ε) n − 1` on mixing graphs, `c_n ≥ 3(1 + ln 3)/(εγ)²` | weaker (`Ω(n)` with constant `½`) |
| Do, Erde & Kang 2024; Gao 2006, 2012; Edwards & McDermid 2015; Shang 2022; Mareček 2009 | supercritical window; linear `tw` thresholds; an upper bound; heterogeneous models; `Ω(n)` at `p = ½` | nothing on the middle regime |
| Frieze 1990, *DM* 81:171–175 (via Coja-Oghlan & Efthymiou 2011, Bohman & van der Hofstad 2024) | `α = (2n/c)(ln c − ln ln c − ln 2 + 1 ± ε)` whp, `c ≥ c_ε`, `c = o(n)` | the upper side of the sandwich of §2.1 |

Verdict: **not settled in print**. No source states `n − pw` or `n − tw` of order
`n ln c / c` in this regime, the constant `4`, or the sandwich `[2, 4]`; the nearest is
Perarnau–Serra's `n − O(n/√c)`. Nothing found for 2020–2026 (searches on treewidth,
pathwidth, vertex separation, node search number, linear width and cutwidth of random
graphs with growing degree; the nearest hits are local treewidth of `G(n, d/n)` and
separating path systems, different quantities).

## 4. The measurement

`reports/scratch/random_graph_middle/run.py` (`--procs 6`, `nice -n 19`, `-t 600 -l -v`):
`n ∈ {30, 40, 50, 60}` × `c ∈ {2 ln n, √n, n^{0.7}, n/2}` × 20 samples, seeds
`7,000,017 n + 1,013 (f + 1) + 101 s + 42` (distinct from the pilot's scheme, so no graph
on record was re-solved), the graph6 string and the witness layout stored per row. **320
of 320 proved**: 286 `refutation`, 34 `minor`, 0 censored; 166.5 s in all, the slowest
graph 13.9 s (`2 ln n` at `n = 60`), the two `n = 60` `log n` cells 118 s of the total. The
sparse control `c = 3` is **not re-run**: `reports/scratch/gnp_pilot/results.csv` holds
136–137 proved graphs per `n` at `c = 3` from 2026-10-18, and the analysis takes samples
0–19, regenerating each graph from its recorded seed and checking the edge count. Total
compute of this session: under 0.05 core-hours for the run and about one minute for the
analysis (exact `α` by branch and bound on bit masks; the Edwards–McDermid histogram term
through `learning.edwards_mcdermid`).

The table of §0 is `paper1/latex/data/random_graph_middle.csv`, one row per cell with the
columns `pw_min / pw_median / pw_max / pw_mean`, `k05` (so `pw ≥ k05 + 1` with probability
≥ 0.95 by the finite inequality), `beta_star` (`β*(c) n`), `thmM`, `thmM_prime` (the A″
end), `thmB` (`n − 4 log_b n`, dense cells only), `alpha_mean`, `n_minus_alpha_mean`,
`em_hist_mean` (the degree-sequence term per graph), `em_poisson` (its Poisson limit,
within `0.6` of the realised mean on every cell). Theorem B's value at `p = ½` — `10.4,
18.7, 27.4, 36.4` — is formal here: its hypothesis `n ≥ b^{4/ε}` is `n ≥ 2^{4/ε}`, met by
nothing at `n ≤ 60` unless `ε ≥ 0.68`.

The sandwich position `(pw − floor)/(ceiling − floor)` of the cell mean, with
`k₀.₀₅ + 1` as floor and the better ceiling: `0.37–0.61` on the `log n` cells, `0.27–0.35`
at `n^{0.7}`, `0.25–0.38` at `p = ½` — the truth sits nearer the first-moment floor than the
ceilings once `c ≥ 10`, and in the middle of the bracket on the `log n` cells; at `c = 3`
`k₀.₀₅` is empty and the degree-sequence term is the only tight side.

## 5. Lean

`lean/MOSPFormalization/FirstMomentAsymptotics.lean`, section "The middle regime", in the
file's conventions (the probability is the `gnpWeight (c/n)`-sum over
`graphsOfPathwidthLe k` on `Fin n`; `firstMomentRate c β` is `δ(β, c)`):

| name | statement |
|---|---|
| `negMulLog_one_sub_le` | (M1) `φ(1 − x) ≤ x` on `[0, 1]` |
| `firstMomentRate_ge` | (M2) `a (c a + 2 log a − 2) ≤ firstMomentRate c β`, `a = (1 − β)/2`, `0 ≤ β ≤ 1` |
| `firstMomentRate_mid` | (M3) `(4 log c / c)(log(2 log c) − 1) ≤ firstMomentRate c (1 − 4 log c / c)` for `1 < c`, `4 log c ≤ c` |
| `firstMoment_pathwidth_le_mid` | **Theorem M, finite form**: `1 < c`, `4 log c < c`, `3 ≤ n`, `c ≤ n` ⟹ `∑_{pw G ≤ ⌊(1 − 4 log c / c) n⌋₊} gnpWeight (c/n) G ≤ exp(−(4 log c / c)(log(2 log c) − 1) n + 3 log n + 2 log c)` |
| `four_mul_log_lt_of_nine_le` | (M5) `9 ≤ c → 4 log c < c` |
| `firstMoment_pathwidth_le_mid'` | Theorem M with `9 ≤ c` |
| `middle_exponent_le` | (M6) for `0 < c ≤ n` and `3 ≤ 4 log c (log(2 log c) − 1)`: the exponent `≤ −log c (4 log(2 log c) − 9)` |
| `tendsto_log_two_log_atTop`, `tendsto_log_mul_log_log_atTop`, `tendsto_four_log_mul_atTop` | the three limits `→ +∞` |
| `tendsto_firstMoment_pathwidth_mid` | **Theorem M, the limit**: `c : ℕ → ℝ`, `Tendsto c atTop atTop`, `∀ᶠ n, c n ≤ n` ⟹ the probability `→ 0` |

Process, as the earlier files: the exact statements were checked numerically first
(`reports/scratch/random_graph_middle/lean_target_check.py`, log beside it: `n = 3..300`,
`c` on 60 points of `(1, n]` plus every integer to 40, restricted to `4 ln c < c`; 24,904
grid points for the main inequality, zero violations of it or of (M1)–(M6); smallest slack
`2.21` nats at `n = 3`, `c = 1`), then written; no `sorry`; `#print axioms` on all eleven:
`propext`, `Classical.choice`, `Quot.sound` (`axiom_check.lean`, `axiom_check.log`). Build:
`cd lean && taskset -c 16-23 lake build MOSPFormalization.FirstMomentAsymptotics`, 24 s;
the full `lake build` afterwards passes (`full_build.log`, 8,991 jobs).

Two things about the statement. The hypotheses are inequalities (`1 < c`, `4 log c < c`),
with the numeric threshold `9 ≤ c` a separate lemma, so the theorem is exactly as strong as
the calculus; and the limit theorem takes `c` as any sequence with `c n ≤ n` eventually,
so `c n = n` (`p = 1`) and `c n = n/2` are instances — it is the dense regime too, with
M's constant rather than B's.

## 6. For the paper

### 6.1 Appendix E, after "The statement" (for `sec9e_appendix_random.tex`; not applied)

```latex
\paragraph{Between the two regimes.}
Theorem~\ref{thm:firstmoment} does not need $c$ to be a constant: it holds for
every real $c\le n$, so it covers $p=c(n)/n$ with $c(n)\to\infty$, the range
between the sparse case and the dense one, where the average degree grows like
$\log n$ or a power of $n$. What it needs there is a closed form for the
admissible $\beta$, and one inequality gives it: since $\phi(1-2a)\le2a$,
the rate satisfies $\delta(\beta,c)\ge a\,(ca+2\ln a-2)$, which at
$a=2\ln c/c$ is $(4\ln c/c)(\ln(2\ln c)-1)$. Hence, for every real $c\ge9$ and
every integer $n\ge c$,
\[
  \Pr\bigl[\mathrm{pw}(G(n,c/n))\le(1-4\ln c/c)\,n\bigr]
  \;\le\;\exp\!\Bigl(-\tfrac{4\ln c}{c}\bigl(\ln(2\ln c)-1\bigr)n+3\ln n+2\ln c\Bigr)
  \;\le\; c^{-(4\ln(2\ln c)-9)},
\]
the last step for $c\le n$; so whenever $c=c(n)\to\infty$ with $c\le n$, the
pathwidth exceeds $n-4n\ln c/c$ with probability tending to one~\leanref{firstmomentM}.
For $c$ fixed this is weaker than $\beta^{*}(c)$ ($0.816$ against $0.857$ at
$c=100$), and the sharper end of Theorem~\ref{thm:betastar}'s asymptotic form,
$n-(4\ln c-4\ln\ln c+O(1))n/c$, holds for growing $c$ by the same calculation
with $a=(2/c)(\ln c+L)$ in place of $2\ln c/c$. At $p$ fixed it reads
$n-\mathrm{pw}\le(4/p)\ln n+O(1)$, which Theorem~\ref{thm:dense} improves to
$(4+\varepsilon)\log_{1/(1-p)}n$; carrying $-n\ln(1-p)$ through the proof in
place of $np$ gives $4\log_{1/(1-p)}n+O(1)$ with no $\varepsilon$, on paper.
The constant~$4$ is the method's: since $\mathrm{pw}\le n-\alpha(G)$ and
$\alpha(G(n,c/n))=(2+o(1))\,n\ln c/c$ whenever $c\to\infty$ and $c=o(n)$
\citep{Frieze1990}, $n-\mathrm{pw}$ lies between $2n\ln c/c$ and $4n\ln c/c$
throughout, the same bracket as in the dense case. We found no prior statement
of either end for pathwidth, vertex separation or treewidth in this range: the
published forms are $n-O(\sqrt{n/p})$ for treewidth \citep{PerarnauSerra2014},
$n-o(n)$ \citep{WangLiuCuiXu2011} and $(1-o(1))n$ for vertex separation when
$p\ge n^{-1+\varepsilon}$ \citep{CheungGirardet2020}, and
$(1-\varepsilon)n$ for bandwidth when $p\ge c\log n/n$ \citep{Turner1986},
which says nothing about pathwidth. On 320 random graphs with 30 to 60
vertices and $c$ equal to $2\ln n$, $\sqrt n$, $n^{0.7}$ and $n/2$, every one
with its pathwidth proved, the ratio $(n-\mathrm{pw})\,c/(n\ln c)$ lies between
$2.0$ and $2.4$, inside the bracket though at sizes where its second-order
terms are not yet small, and the finite inequality evaluated exactly, the
largest $k$ with $\Pr[\mathrm{pw}\le k]\le0.05$, is within six of the
smallest proved value in every cell where it is positive
(Figure~\ref{fig:middle}).
```

Needs: the dense statement has no theorem environment in the appendix (it is stated in
prose in *What is checked, and what is known*, "almost every $G(n,p)$ with $p$ fixed has
bandwidth at least $n-4\log_{1/(1-p)}n$ … our dense statement implies his"), so
`Theorem~\ref{thm:dense}` must become words ("the dense bound $n-(4+\varepsilon)\log_{1/(1-p)}n$
of this appendix") or the dense statement gets a label; a `Frieze1990` and a
`WangLiuCuiXu2011` entry in `refs.bib` (§3 has the citations; `CheungGirardet2020`,
`PerarnauSerra2014` and `Turner1986` exist); `\leanref{firstmomentM}`; and the figure as
`fig:middle` from `paper1/figures/random_graph_middle.pdf` (caption below).

Figure caption: *The pathwidth of $G(n,c/n)$ with $c$ growing, in units of $n$, on 400
random graphs with their pathwidth proved (ink: median and range of 20 per cell; the
$c=3$ cells are from the sparse pilot). Floors in blue: Theorem~M's $1-4\ln c/c$,
$\beta^{*}(c)$ of Theorem~\ref{thm:betastar}, and the finite inequality of
Theorem~\ref{thm:firstmoment} evaluated exactly (the largest $k$ with
$\Pr[\mathrm{pw}\le k]\le0.05$). Ceilings in orange: $n-\alpha(G)$ and the degree-sequence
term of \citet{EdwardsMcDermid2015}, means per cell.*

### 6.2 Appendix A row (for `sec9a_appendix_lean.tex`; not applied)

```latex
\leanentry{firstmomentM}{The middle regime (the paragraph \emph{Between the two regimes} of Appendix~\ref{app:random}): for $1<c$ with $4\ln c<c$, $n\ge3$ and $c\le n$, the weighted sum over graphs of pathwidth at most $\lfloor(1-4\ln c/c)n\rfloor$ is at most $\exp(-(4\ln c/c)(\ln(2\ln c)-1)n+3\ln n+2\ln c)$; the threshold $c\ge9$ made explicit; the rate bound $\delta\ge a(ca+2\ln a-2)$; and for every sequence $c(n)\to\infty$ with $c(n)\le n$ the sum tends to~$0$} \leannames{firstMoment_pathwidth_le_mid, firstMoment_pathwidth_le_mid', firstMomentRate_ge, tendsto_firstMoment_pathwidth_mid} \\
```

(The appendix's label is `app:random` or whatever the section carries; substitute.)

## 7. Commands and numbers

| number | where | command |
|---|---|---|
| 24,904 grid points, 0 violations, slack 2.21 | §5 | `cd reports/scratch/random_graph_middle && nice -n 19 python3 -I lean_target_check.py` (log `lean_target_check.log`) |
| eleven theorems, three axioms | §5 | `cd lean && lake env lean ../reports/scratch/random_graph_middle/axiom_check.lean` (log `axiom_check.log`) |
| build 24 s | §5 | `cd lean && taskset -c 16-23 lake build MOSPFormalization.FirstMomentAsymptotics` |
| 320 / 320 proved, 286 + 34, 166.5 s, max 13.9 s | §4 | `nice -n 19 python3 reports/scratch/random_graph_middle/run.py --procs 6` (`results.csv`, `run.log`) |
| the table of §0, `k05`, `β* n`, `α`, degree-sequence term | §0, §4 | `python3 paper1/latex/figures/random_graph_middle.py extract` → `paper1/latex/data/random_graph_middle.csv` |
| the figure | §0 | `python3 paper1/latex/figures/random_graph_middle.py draw` → `paper1/figures/random_graph_middle.pdf`, `reports/figures/random_graph_middle.png`; palette `#2a78d6, #eb6834` validated by the dataviz skill's `validate_palette.js` (all checks pass, light mode) |
| `β*(c)`, Theorem M, A″ end at `c = 9…10⁴`; crossover `e^{2e} = 229.7`; `4 ln c < c` from `8.613`; rate `> 0` from `e^{e/2} = 3.89`; `λ` form at `p = ½` | §2 | the inline Python of the session, reproduced by `beta_star` and `thm_m` in the figure script |
| pilot `c = 3` rows: 20 per `n`, all proved 2026-10-18 | §4 | `reports/scratch/gnp_pilot/results.csv`, `c = 3`, `sample < 20` |

Nothing under `solutions/` was touched; no instance on record was re-solved; the compute
of the session is under 0.1 core-hours.
