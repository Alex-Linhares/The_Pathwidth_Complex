/* minor_tabu -- a tabu search over contraction minors for a pathwidth lower bound.
 *
 * The dual side of pathwidth is searched bottom-up: the state is a forest F of
 * edges of G, whose components are the branch sets of a minor H = G / F; the
 * objective is a lower bound on pw(G) certified by H.  Two bounds are used:
 *   proxy  = contraction degeneracy of H (MMD+, a treewidth bound, so
 *            proxy <= tw(H) <= pw(H) <= pw(G)), cheap, used to rank every
 *            neighbour at every step;
 *   exact  = pw(H) >= k proved by the search engine refuting k on H under a
 *            node budget, run on the chosen minor at every step while H has at
 *            most `max_exact` vertices; a refutation of k on H proves
 *            pw(G) >= k + 1 (minor monotonicity).
 * Moves: add an edge of G joining two different branch sets (one more
 * contraction) or remove an edge of F (one contraction undone; the branch set
 * splits into two connected halves).  Every neighbour is evaluated by the proxy
 * each step (all of them while the move count is at most `sample`, else a
 * random sample of that many), the best non-tabu one is taken, the reverse of
 * the last `tabu` moves is tabu, and a move that improves the best floor is
 * always allowed (aspiration).  Deadline in seconds; the best certificate is
 * printed as JSON on stdout at the end (and whenever `-p` is given, at every
 * improvement): the floor, the proof kind, the minor's size, and the
 * contraction sequence as (v,u) pairs replayable by pathwidth's checker.
 *
 *   minor_tabu [-t seconds] [-w target] [-L floor] [-c tabu] [-b nodes] [-m max_exact]
 *              [-S sample] [-s seed] [-p] < graph.g6
 *
 * Reuses pathwidth.c's graph, engine wrapper and bounds by inclusion. MIT licence.
 */
#define main pathwidth_main
#include "pathwidth.c"
#undef main

#include <time.h>

typedef struct {
    int n, m;          /* vertices, edges of G */
    int *eu, *ev;      /* edge endpoints */
    char *in_forest;   /* 1 if edge i is contracted */
    int *rep;          /* union-find representative per vertex, rebuilt on demand */
} state;

static unsigned long long rng_state = 88172645463325252ULL;
static unsigned long long rnd(void) { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state; }

static int uf_find(int *rep, int x) { while (rep[x] != x) { rep[x] = rep[rep[x]]; x = rep[x]; } return x; }

/* Build the minor H = G / F: returns H over 0..h-1, index[v] = H-vertex of v. */
static graph build_minor(const graph *g, const state *s, int *index_out) {
    int n = g->n, nw = g->nw;
    int *rep = xmalloc(sizeof(int) * (size_t) n);
    for (int v = 0; v < n; v++) rep[v] = v;
    for (int i = 0; i < s->m; i++) if (s->in_forest[i]) {
        int a = uf_find(rep, s->eu[i]), b = uf_find(rep, s->ev[i]);
        if (a != b) rep[a] = b;
    }
    int *index = xmalloc(sizeof(int) * (size_t) n);
    int h = 0;
    for (int v = 0; v < n; v++) index[v] = -1;
    for (int v = 0; v < n; v++) { int r = uf_find(rep, v); if (index[r] < 0) index[r] = h++; }
    for (int v = 0; v < n; v++) index[v] = index[uf_find(rep, v)];
    graph H = graph_new(h);
    for (int v = 0; v < n; v++) {
        uint64_t *r = row(&H, index[v]);
        bs_set(r, index[v]);
        BS_FOR(u, row(g, v), nw) bs_set(r, index[u]);
    }
    for (int i = 0; i < h; i++) bs_set(row(&H, i), i);
    free(rep);
    if (index_out) memcpy(index_out, index, sizeof(int) * (size_t) n);
    free(index);
    return H;
}

static int forest_would_cycle(const state *s, int edge) {
    /* adding `edge`: cycle iff endpoints already share a branch set */
    int n = s->n;
    int *rep = xmalloc(sizeof(int) * (size_t) n);
    for (int v = 0; v < n; v++) rep[v] = v;
    for (int i = 0; i < s->m; i++) if (s->in_forest[i]) {
        int a = uf_find(rep, s->eu[i]), b = uf_find(rep, s->ev[i]);
        if (a != b) rep[a] = b;
    }
    int cyc = uf_find(rep, s->eu[edge]) == uf_find(rep, s->ev[edge]);
    free(rep);
    return cyc;
}

static int proxy_of(const graph *g, const state *s, int *h_out) {
    graph H = build_minor(g, s, NULL);
    int p = contraction_degeneracy(&H);
    if (h_out) *h_out = H.n;
    graph_free(&H);
    return p;
}

/* Print the contraction sequence for the forest as (v, u) pairs in G's labels,
 * each a current edge at the time it is applied (parent-pointer order). */
static void print_sequence(const state *s) {
    int n = s->n;
    int *rep = xmalloc(sizeof(int) * (size_t) n);
    for (int v = 0; v < n; v++) rep[v] = v;
    printf("[");
    int first = 1;
    for (int i = 0; i < s->m; i++) if (s->in_forest[i]) {
        int a = uf_find(rep, s->eu[i]), b = uf_find(rep, s->ev[i]);
        if (a == b) continue;
        printf("%s[%d,%d]", first ? "" : ",", a, b);   /* contract a into b: both are current representatives, adjacent in the current minor */
        first = 0;
        rep[a] = b;
    }
    printf("]");
    free(rep);
}

int main(int argc, char **argv) {
    double budget = 1800.0;
    int target = -1, floor_known = 0, tabu_len = 7, max_exact = 90, sample = 400, verbose_improve = 0;
    double lo_frac = 0.4, hi_frac = 0.9, nb_seconds = 2.0;
    const char *seed_file = NULL;
    int seed_h = -1;                      /* the seed minor's size; ties prefer minors near it */   /* the walk stays on minors with between lo and hi of the vertices */
    long long exact_nodes = 300000, nb_nodes = 20000;   /* node budget: the chosen minor's climb; each neighbour's test */
    unsigned long long seed = 1;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-t") && i + 1 < argc) budget = atof(argv[++i]);
        else if (!strcmp(argv[i], "-w") && i + 1 < argc) target = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-L") && i + 1 < argc) floor_known = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-c") && i + 1 < argc) tabu_len = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-b") && i + 1 < argc) exact_nodes = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-m") && i + 1 < argc) max_exact = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-S") && i + 1 < argc) sample = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-s") && i + 1 < argc) seed = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "-p")) verbose_improve = 1;
        else if (!strcmp(argv[i], "-nb") && i + 1 < argc) nb_nodes = atoll(argv[++i]);
        else if (!strcmp(argv[i], "-nt") && i + 1 < argc) nb_seconds = atof(argv[++i]);
        else if (!strcmp(argv[i], "-seed") && i + 1 < argc) seed_file = argv[++i];
        else if (!strcmp(argv[i], "-lo") && i + 1 < argc) lo_frac = atof(argv[++i]);
        else if (!strcmp(argv[i], "-hi") && i + 1 < argc) hi_frac = atof(argv[++i]);
        else { fprintf(stderr, "unknown option %s\n", argv[i]); return 2; }
    }
    rng_state ^= seed * 0x9E3779B97F4A7C15ULL; if (!rng_state) rng_state = 1;

    /* read one graph6 line */
    char *line = NULL; size_t cap = 0; ssize_t len = getline(&line, &cap, stdin);
    if (len <= 0) fatal("no graph6 on stdin");
    while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r')) line[--len] = 0;
    graph g; const char *err = NULL;
    if (parse_graph6(line, (size_t) len, &g, &err)) { fprintf(stderr, "graph6: %s\n", err); return 2; }
    int n = g.n, nw = g.nw;
    if (n > 1024) fatal("more than 1024 vertices");

    state s; s.n = n; s.m = 0;
    for (int v = 0; v < n; v++) BS_FOR(u, row(&g, v), nw) if (u > v) s.m++;
    s.eu = xmalloc(sizeof(int) * (size_t) (s.m ? s.m : 1)); s.ev = xmalloc(sizeof(int) * (size_t) (s.m ? s.m : 1));
    s.in_forest = xcalloc((size_t) (s.m ? s.m : 1), 1); s.rep = NULL;
    int k = 0;
    for (int v = 0; v < n; v++) BS_FOR(u, row(&g, v), nw) if (u > v) { s.eu[k] = v; s.ev[k] = u; k++; }

    double t0 = now(), deadline = t0 + budget;
    int floor = floor_known;                      /* best certified lower bound on pw(G) */
    int floor_whole = lower_bound(&g);            /* G's own degree/contraction floor */
    if (floor_whole > floor) floor = floor_whole;
    int best_proxy = contraction_degeneracy(&g);
    char *best_forest = xmalloc((size_t) (s.m ? s.m : 1)); memcpy(best_forest, s.in_forest, (size_t) s.m);
    int best_h = n; const char *best_kind = "contraction_degeneracy";
    long long best_nodes = 0;
    int *tabu = xmalloc(sizeof(int) * (size_t) (tabu_len > 0 ? tabu_len : 1)); int tabu_pos = 0;
    for (int i = 0; i < tabu_len; i++) tabu[i] = -1;
    int *order = xmalloc(sizeof(int) * (size_t) n);
    long long steps = 0, exact_calls = 0, exact_total_nodes = 0;
    int cur_proxy = best_proxy, cur_h = n;

    fprintf(stderr, "minor_tabu: n=%d m=%d floor=%d (whole-graph bounds %d) target=%d tabu=%d budget=%.0fs\n",
            n, s.m, floor, floor_whole, target, tabu_len, budget);
    /* exact step on G itself first, when it is small enough */
    if (n <= max_exact && n >= 2) {
        while (now() < deadline && (target < 0 || floor < target)) {
            long long nodes = 0; double dl = now() + 60.0; if (dl > deadline) dl = deadline;
            int ans = decide(&g, floor + 1, 0, exact_nodes, dl, order, &nodes);
            exact_calls++; exact_total_nodes += nodes;
            if (ans == UNSAT) { floor++; best_kind = "refutation"; best_h = n; best_nodes = nodes; memcpy(best_forest, s.in_forest, (size_t) s.m);
                if (verbose_improve) fprintf(stderr, "%8.1fs start: floor %d by refutation of %d on the whole graph (%lld nodes)\n", now() - t0, floor, floor - 1, nodes); }
            else break;
        }
    }

    int lo_n = (int) (lo_frac * n), hi_n = (int) (hi_frac * n);
    if (lo_n < 2) lo_n = 2;
    if (hi_n < lo_n) hi_n = lo_n;
    if (hi_n > max_exact) hi_n = max_exact;          /* every minor visited can get the exact step */
    if (lo_n > hi_n) lo_n = hi_n;
    {   /* the seed sequence (a certificate's contractions) if given, else greedy min-degree contractions down to hi_n */
        int *seq = xmalloc(sizeof(int) * 2 * (size_t) (n ? n : 1));
        int len = 0;
        if (seed_file) {
            FILE *f = fopen(seed_file, "r"); if (!f) fatal("cannot open the seed file");
            int a, b;
            while (fscanf(f, "%d %d", &a, &b) == 2) { if (len < n) { seq[2 * len] = a; seq[2 * len + 1] = b; len++; } }
            fclose(f);
            fprintf(stderr, "seed: %d contractions read\n", len);
        } else len = contraction_sequence(&g, hi_n, RULE_MIN_D, seq);
        for (int t = 0; t < len; t++) {
            int v = seq[2 * t], u = seq[2 * t + 1];
            if (u < 0) continue;
            /* the pair (v,u) is an edge of the current minor; find an edge of G between their branch sets */
            int *rep = xmalloc(sizeof(int) * (size_t) n);
            for (int x = 0; x < n; x++) rep[x] = x;
            for (int i = 0; i < s.m; i++) if (s.in_forest[i]) { int a = uf_find(rep, s.eu[i]), b = uf_find(rep, s.ev[i]); if (a != b) rep[a] = b; }
            int rv = uf_find(rep, v), ru = uf_find(rep, u);
            for (int i = 0; i < s.m; i++) if (!s.in_forest[i] && ((uf_find(rep, s.eu[i]) == rv && uf_find(rep, s.ev[i]) == ru) || (uf_find(rep, s.eu[i]) == ru && uf_find(rep, s.ev[i]) == rv))) { s.in_forest[i] = 1; break; }
            free(rep);
        }
        free(seq);
        cur_proxy = proxy_of(&g, &s, &cur_h);
        if (seed_file) {   /* stay near the seed's size: it is where the obstruction survived */
            lo_n = cur_h - n / 10; hi_n = cur_h + n / 7;
            if (lo_n < 2) lo_n = 2; if (hi_n > n) hi_n = n; if (hi_n > max_exact) hi_n = max_exact; if (lo_n > hi_n) lo_n = hi_n;
        }
        if (cur_proxy > best_proxy) best_proxy = cur_proxy;
        if (cur_proxy > floor) { floor = cur_proxy; best_kind = "contraction_degeneracy"; best_h = cur_h; memcpy(best_forest, s.in_forest, (size_t) s.m); }
        if (seed_file && best_kind != NULL && strcmp(best_kind, "refutation") != 0 && floor == floor_known) {
            /* nothing improved on the given floor: report the seed's minor as the certificate behind it */
            best_kind = "seed"; best_h = cur_h; memcpy(best_forest, s.in_forest, (size_t) s.m);
        }
        seed_h = cur_h;
        fprintf(stderr, "band [%d, %d] vertices; start minor %d vertices, proxy %d\n", lo_n, hi_n, cur_h, cur_proxy);
    }
    while (now() < deadline && (target < 0 || floor < target)) {
        steps++;
        /* ---- enumerate moves: index i in [0, m): toggle edge i ---- */
        int nmoves = s.m;
        int *cand = xmalloc(sizeof(int) * (size_t) (nmoves ? nmoves : 1)); int nc = 0;
        for (int i = 0; i < nmoves; i++) {
            /* a forest-preserving addition shrinks the minor by one; a removal grows it by one */
            int h_after = s.in_forest[i] ? cur_h + 1 : cur_h - 1;
            if (h_after < lo_n || h_after > hi_n) continue;
            if (!s.in_forest[i] && forest_would_cycle(&s, i)) continue;   /* only forest-preserving additions */
            cand[nc++] = i;
        }
        if (nc == 0) { free(cand); fprintf(stderr, "no move keeps the minor inside the band [%d, %d]; stopping\n", lo_n, hi_n); break; }
        /* sample if too many */
        if (nc > sample) { for (int i = 0; i < sample; i++) { int j = i + (int) (rnd() % (unsigned long long) (nc - i)); int t = cand[i]; cand[i] = cand[j]; cand[j] = t; } nc = sample; }
        int best_move = -1, best_val = -1, best_val_h = 0, ties = 0;
        for (int c = 0; c < nc; c++) {
            int i = cand[c];
            int is_tabu = 0;
            for (int t = 0; t < tabu_len; t++) if (tabu[t] == i) { is_tabu = 1; break; }
            s.in_forest[i] ^= 1;
            graph Hc = build_minor(&g, &s, NULL);
            s.in_forest[i] ^= 1;
            int h = Hc.n;
            if (h < lo_n || h > hi_n) { graph_free(&Hc); continue; }
            /* the neighbour's value: does it refute the current floor within a small budget (the dual objective),
             * then its contraction degeneracy, then the smaller minor */
            int proxy = contraction_degeneracy(&Hc);
            int refutes = 0;    /* 2: refutes the target level; 1: still refutes the floor's level (keeps the known obstruction); 0: neither */
            if (now() < deadline) {
                long long nd = 0; double dl = now() + nb_seconds; if (dl > deadline) dl = deadline;
                int ans = decide(&Hc, floor + 1, 0, nb_nodes, dl, order, &nd);
                exact_calls++; exact_total_nodes += nd;
                if (ans == UNSAT) refutes = 2;
                else if (floor >= 1) {
                    nd = 0; dl = now() + nb_seconds; if (dl > deadline) dl = deadline;
                    ans = decide(&Hc, floor, 0, nb_nodes, dl, order, &nd);
                    exact_calls++; exact_total_nodes += nd;
                    if (ans == UNSAT) refutes = 1;
                }
            }
            graph_free(&Hc);
            int val = refutes * 100000 + proxy;
            int aspire = refutes == 2;
            if (is_tabu && !aspire) continue;
            /* ties: when seeded, the minor whose size is nearest the seed's (where the obstruction is known to survive);
             * otherwise the smaller minor (cheaper exact step) */
            int dist_new = seed_h >= 0 ? abs(h - seed_h) : h, dist_best = seed_h >= 0 ? abs(best_val_h - seed_h) : best_val_h;
            int better = val > best_val || (val == best_val && dist_new < dist_best);
            if (better) { best_move = i; best_val = val; best_val_h = h; ties = 1; }
            else if (val == best_val && h == best_val_h && (rnd() % (unsigned long long) (++ties)) == 0) best_move = i;
        }
        /* every sampled neighbour was tabu (and none refuted the target): take a random non-tabu in-band move instead */
        if (best_move < 0) {
            for (int tries = 0; tries < 50 && best_move < 0; tries++) {
                int i = cand[rnd() % (unsigned long long) nc], is_tabu = 0;
                for (int t = 0; t < tabu_len; t++) if (tabu[t] == i) { is_tabu = 1; break; }
                if (!is_tabu) { best_move = i; best_val = cur_proxy; best_val_h = s.in_forest[i] ? cur_h + 1 : cur_h - 1; }
            }
        }
        free(cand);
        if (best_move < 0) break;
        s.in_forest[best_move] ^= 1;
        tabu[tabu_pos] = best_move; tabu_pos = (tabu_pos + 1) % (tabu_len > 0 ? tabu_len : 1);
        cur_proxy = best_val % 100000; cur_h = best_val_h;
        if (cur_proxy > best_proxy) { best_proxy = cur_proxy; }
        if (cur_proxy > floor) {
            floor = cur_proxy; best_kind = "contraction_degeneracy"; best_h = cur_h; memcpy(best_forest, s.in_forest, (size_t) s.m);
            if (verbose_improve) fprintf(stderr, "%8.1fs step %lld floor %d by %s on %d vertices\n", now() - t0, steps, floor, best_kind, best_h);
        }
        /* ---- exact step on the chosen minor ---- */
        if (cur_h <= max_exact && cur_h >= 2) {
            graph H = build_minor(&g, &s, NULL);
            while (now() < deadline && (target < 0 || floor < target)) {
                long long nodes = 0;
                double dl = deadline; double per = now() + 60.0; if (per < dl) dl = per;
                int ans = decide(&H, floor + 1, 0, exact_nodes, dl, order, &nodes);   /* k = w + 1 open stacks refutes width w = floor: pw(H) > floor */
                exact_calls++; exact_total_nodes += nodes;
                if (ans == UNSAT) {
                    floor = floor + 1; best_kind = "refutation"; best_h = H.n; best_nodes = nodes;   /* refuted width floor (old value) on H */ memcpy(best_forest, s.in_forest, (size_t) s.m);
                    if (verbose_improve) fprintf(stderr, "%8.1fs step %lld floor %d by refutation of %d on %d vertices (%lld nodes)\n", now() - t0, steps, floor, floor - 1, H.n, nodes);
                } else break;
            }
            graph_free(&H);
        }
        if (steps % 50 == 0) fprintf(stderr, "%8.1fs step %lld: minor %d vertices, proxy %d, floor %d (best proxy %d), exact calls %lld\n", now() - t0, steps, cur_h, cur_proxy, floor, best_proxy, exact_calls);
    }
    /* ---- output ---- */
    memcpy(s.in_forest, best_forest, (size_t) s.m);
    printf("{\"n\":%d,\"m\":%d,\"floor\":%d,\"kind\":\"%s\",\"minor_vertices\":%d,\"refuted\":%d,\"nodes\":%lld,"
           "\"whole_graph_floor\":%d,\"best_proxy\":%d,\"steps\":%lld,\"exact_calls\":%lld,\"exact_nodes\":%lld,\"seconds\":%.1f,"
           "\"reached_target\":%s,\"sequence\":",
           n, s.m, floor, best_kind, best_h, floor - 1, best_nodes, floor_whole, best_proxy, steps, exact_calls, exact_total_nodes,
           now() - t0, (target >= 0 && floor >= target) ? "true" : "false");
    print_sequence(&s);
    printf("}\n");
    return 0;
}
