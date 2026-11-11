/* Exact moments of the number of narrow layouts over every labelled graph on n <= 10
 * vertices, by isomorphism classes (nauty-geng + nauty-countg --a for |Aut|).
 *
 * For each class representative G: X_w(G) = #orderings of width <= w for every w
 * (subset DP: paths through the subsets S with |N(S) \ S| <= w), and the class carries
 * n!/|Aut(G)| labelled graphs with the same e(G) and X_w.  Accumulates
 *   T1[e][w] = sum over labelled graphs with e edges of X_w(G),
 *   T2[e][w] = sum of X_w(G)^2,
 * in 128-bit integers, so that for any p
 *   E[X_w] = sum_e p^e (1-p)^(C-e) T1[e][w],   E[X_w^2] = sum_e p^e (1-p)^(C-e) T2[e][w].
 *
 * Usage: layout_moment_enum n graphs.g6 aut.txt > table.csv
 *        (graphs.g6: one graph6 per line, aut.txt: one |Aut| per line, same order)
 * Build: gcc -O3 -march=native -o <bin> learning/layout_moment_enum.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef __int128 i128;

static void print_i128(i128 v)
{
    char buf[64]; int i = 63; buf[i] = 0;
    if (v == 0) { putchar('0'); return; }
    int neg = v < 0; if (neg) v = -v;
    while (v > 0) { buf[--i] = '0' + (int)(v % 10); v /= 10; }
    if (neg) buf[--i] = '-';
    fputs(buf + i, stdout);
}

/* graph6 for n <= 62: adjacency as bitmasks */
static int parse_g6(const char *s, unsigned *adj, int n)
{
    if ((int)(s[0] - 63) != n) return 1;
    for (int i = 0; i < n; i++) adj[i] = 0;
    int bit = 0; const char *c = s + 1; int edges = 0;
    for (int j = 1; j < n; j++)
        for (int i = 0; i < j; i++) {
            int ch = c[bit / 6] - 63;
            int b = (ch >> (5 - bit % 6)) & 1;
            if (b) { adj[i] |= 1u << j; adj[j] |= 1u << i; edges++; }
            bit++;
        }
    return 0;
}

int main(int argc, char **argv)
{
    if (argc < 4) { fprintf(stderr, "usage: n graphs.g6 aut.txt\n"); return 2; }
    int n = atoi(argv[1]);
    if (n < 1 || n > 12) { fprintf(stderr, "n must be 1..12\n"); return 2; }
    FILE *fg = fopen(argv[2], "r"), *fa = fopen(argv[3], "r");
    if (!fg || !fa) { fprintf(stderr, "cannot open inputs\n"); return 2; }
    int C = n * (n - 1) / 2;
    unsigned full = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
    size_t NS = (size_t)1 << n;
    int *open = malloc(NS * sizeof(int));
    unsigned long long *cnt = malloc(NS * sizeof(unsigned long long));
    i128 *T1 = calloc((size_t)(C + 1) * n, sizeof(i128));
    i128 *T2 = calloc((size_t)(C + 1) * n, sizeof(i128));
    unsigned long long nfact = 1; for (int i = 2; i <= n; i++) nfact *= i;
    unsigned adj[64];
    char line[256]; char aline[64];
    unsigned long long graphs = 0;
    while (fgets(line, sizeof line, fg)) {
        if (!fgets(aline, sizeof aline, fa)) { fprintf(stderr, "aut file short\n"); return 3; }
        unsigned long long aut = strtoull(aline, NULL, 10);
        if (parse_g6(line, adj, n)) { fprintf(stderr, "bad graph6 line\n"); return 3; }
        int e = 0; for (int i = 0; i < n; i++) e += __builtin_popcount(adj[i]); e /= 2;
        unsigned long long orbit = nfact / aut;
        /* open counts of every subset */
        open[0] = 0;
        for (size_t S = 1; S < NS; S++) {
            int v = __builtin_ctzll(S);
            size_t S0 = S & (S - 1);
            unsigned nb = 0;
            /* N(S) = N(S0) | adj[v]; recompute from scratch via low-bit recursion is cheap */
            for (size_t T = S; T; T &= T - 1) nb |= adj[__builtin_ctzll(T)];
            (void)v; (void)S0;
            open[S] = __builtin_popcount(nb & ~(unsigned)S & full);
        }
        for (int w = 0; w < n; w++) {
            cnt[0] = 1;
            for (size_t S = 1; S < NS; S++) {
                if (open[S] > w) { cnt[S] = 0; continue; }
                unsigned long long c = 0;
                for (size_t T = S; T; T &= T - 1) c += cnt[S & ~((size_t)1 << __builtin_ctzll(T))];
                cnt[S] = c;
            }
            i128 x = (i128)cnt[NS - 1];
            T1[(size_t)e * n + w] += (i128)orbit * x;
            T2[(size_t)e * n + w] += (i128)orbit * x * x;
        }
        graphs++;
    }
    fprintf(stderr, "classes %llu\n", graphs);
    printf("e,w,T1,T2\n");
    for (int e = 0; e <= C; e++)
        for (int w = 0; w < n; w++) {
            printf("%d,%d,", e, w); print_i128(T1[(size_t)e * n + w]); putchar(',');
            print_i128(T2[(size_t)e * n + w]); putchar('\n');
        }
    return 0;
}
