/* The first moment of narrow layouts of G(n, p), exactly, by the open-count chain
 * (learning/layout_moment.py; reports/layout_second_moment.md).
 *
 * A fixed ordering v_1 .. v_n of G(n, p).  After the first t vertices are placed the
 * open count k_t = |N(S_t) \ S_t| is a Markov chain in (t, k): the vertex placed at
 * step t is open with probability k / (n - t + 1) (the suffix vertices are
 * exchangeable given the history), and each still-closed suffix vertex then opens
 * with probability p, independently, through its fresh edge to v_t.  So
 *
 *   q(n, p, w) = P(every prefix of the identity ordering has at most w open vertices)
 *
 * is a DP over (t, k) with k <= w; E[#orderings of width <= w] = n! q.
 *
 * chain_log_q          log q, long double with a running scale (exact up to rounding).
 * chain_edge_profile   log P(width <= w and e(G) = e) for every e, the same chain with
 *                      the edge count carried (the edges from v_t to the already-open
 *                      suffix vertices are free Bernoulli(p) and are counted too);
 *                      the input to the Jensen lower bound on the second-moment ratio.
 *
 * Build: gcc -O3 -shared -fPIC -o learning/_layout_moment.so learning/layout_moment.c -lm
 * (learning/layout_moment.py builds it on first use).
 */
#include <math.h>
#include <stdlib.h>
#include <string.h>

/* pmf of Bin(m, p) for j = 0..jmax into out (long double); p in [0, 1] */
static void binom_pmf(int m, long double p, int jmax, long double *out)
{
    long double q = 1.0L - p;
    for (int j = 0; j <= jmax; j++) out[j] = 0.0L;
    if (jmax < 0) return;
    if (p <= 0.0L) { out[0] = 1.0L; return; }
    if (q <= 0.0L) { if (m <= jmax) out[m] = 1.0L; return; }
    long double v = powl(q, m);
    out[0] = v;
    long double r = p / q;
    for (int j = 0; j < jmax && j < m; j++) {
        v = v * (long double)(m - j) / (long double)(j + 1) * r;
        out[j + 1] = v;
    }
}

double chain_log_q(int n, double pd, int w)
{
    if (n <= 0) return 0.0;              /* the empty layout has width 0 */
    if (w < 0) return -INFINITY;
    long double p = (long double)pd;
    long double *f = calloc(w + 2, sizeof(long double));
    long double *g = calloc(w + 2, sizeof(long double));
    long double *pmf = calloc(w + 3, sizeof(long double));
    long double logscale = 0.0L;
    f[0] = 1.0L;
    for (int t = 1; t <= n; t++) {
        int suf = n - t + 1;                      /* suffix size before placing v_t */
        memset(g, 0, (w + 2) * sizeof(long double));
        int kmax = w < suf ? w : suf;
        for (int k = 0; k <= kmax; k++) {
            if (f[k] == 0.0L) continue;
            long double a = (long double)k / (long double)suf;   /* P(v_t is open) */
            if (a < 1.0L) {                       /* v_t closed: m0 closed suffix vertices remain */
                int m0 = n - t - k;
                int jmax = w - k; if (jmax > m0) jmax = m0;
                binom_pmf(m0, p, jmax, pmf);
                long double base = (1.0L - a) * f[k];
                for (int j = 0; j <= jmax; j++) g[k + j] += base * pmf[j];
            }
            if (a > 0.0L) {                       /* v_t open: it leaves the suffix */
                int m1 = n - t - k + 1;
                int jmax = w - k + 1; if (jmax > m1) jmax = m1;
                binom_pmf(m1, p, jmax, pmf);
                long double base = a * f[k];
                for (int j = 0; j <= jmax; j++) g[k - 1 + j] += base * pmf[j];
            }
        }
        long double s = 0.0L;
        for (int k = 0; k <= w; k++) s += g[k];
        if (s <= 0.0L) { free(f); free(g); free(pmf); return -INFINITY; }
        for (int k = 0; k <= w; k++) f[k] = g[k] / s;
        logscale += logl(s);
    }
    double out = (double)(logl(f[0]) + logscale);
    free(f); free(g); free(pmf);
    return out;
}

/* out[e] = log P(width <= w and e(G) = e), e = 0..n(n-1)/2; -inf where impossible.
 * Returns 0 on success. */
int chain_edge_profile(int n, double pd, int w, double *out)
{
    int C = n * (n - 1) / 2;
    for (int e = 0; e <= C; e++) out[e] = -INFINITY;
    if (n <= 0) { out[0] = 0.0; return 0; }
    if (w < 0) return 0;
    long double p = (long double)pd;
    size_t W = (size_t)(w + 1), E = (size_t)(C + 1);
    long double *F = calloc(W * E, sizeof(long double));
    long double *G = calloc(W * E, sizeof(long double));
    long double *pj = calloc(w + 3, sizeof(long double));
    long double *pl = calloc(w + 3, sizeof(long double));
    if (!F || !G || !pj || !pl) return 1;
    long double logscale = 0.0L;
    F[0] = 1.0L;
    for (int t = 1; t <= n; t++) {
        int suf = n - t + 1;
        memset(G, 0, W * E * sizeof(long double));
        int kmax = w < suf ? w : suf;
        for (int k = 0; k <= kmax; k++) {
            long double a = (long double)k / (long double)suf;
            for (int O = 0; O <= 1; O++) {
                long double pO = O ? a : 1.0L - a;
                if (pO <= 0.0L) continue;
                int m = n - t - k + O;            /* closed suffix vertices after removing v_t */
                int kept = k - O;                 /* already-open suffix vertices: free edges */
                int jmax = w - kept; if (jmax > m) jmax = m;
                if (jmax < 0) continue;
                binom_pmf(m, p, jmax, pj);
                binom_pmf(kept, p, kept, pl);
                for (int e = 0; e <= C; e++) {
                    long double fe = F[(size_t)k * E + e];
                    if (fe == 0.0L) continue;
                    long double base = pO * fe;
                    for (int j = 0; j <= jmax; j++) {
                        long double bj = base * pj[j];
                        if (bj == 0.0L) continue;
                        size_t row = (size_t)(kept + j) * E;
                        for (int l = 0; l <= kept; l++) {
                            int e2 = e + j + l;
                            if (e2 > C) break;
                            G[row + e2] += bj * pl[l];
                        }
                    }
                }
            }
        }
        long double s = 0.0L;
        for (size_t i = 0; i < W * E; i++) s += G[i];
        if (s <= 0.0L) { free(F); free(G); free(pj); free(pl); return 0; }
        for (size_t i = 0; i < W * E; i++) F[i] = G[i] / s;
        logscale += logl(s);
    }
    for (int e = 0; e <= C; e++) {
        long double v = F[e];                     /* k = 0 at t = n */
        out[e] = v > 0.0L ? (double)(logl(v) + logscale) : -INFINITY;
    }
    free(F); free(G); free(pj); free(pl);
    return 0;
}
