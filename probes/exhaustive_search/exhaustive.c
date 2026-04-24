/*
 * exhaustive.c — App C exhaustive-search worker, screaming-C edition.
 *
 * Responsibility: for one oriented state-count vector, enumerate every
 * candidate good cycle (with forced-neighbor det propagation + lex-min
 * start canonicalization), every rule-table completion of each cycle,
 * and every completion that the six-property verifier rejects.
 * Emit one JSON line per rejection to stdout.
 *
 * The caller (driver.py) handles:
 *   - multiset enumeration (C1) and D_n orbit reduction (C2);
 *   - dispatching this binary per (n, multiset, orientation);
 *   - collecting the rejection streams into artifacts/rejections/;
 *   - writing summary.json.
 *
 * Build:
 *     cc -O3 -std=c11 -Wall -Wextra exhaustive.c -o exhaustive
 *
 * Usage:
 *     ./exhaustive --n 5 --ms 2,2,2,2,3 --orient 2,2,2,2,3
 *
 * Output: a JSON object per line on stdout. Final line is a summary
 *     {"kind":"summary", ...} giving counters. Determinism: the same
 *     arguments produce bit-for-bit identical output.
 *
 * Invariants and asserts:
 *   - n <= MAX_N (10).
 *   - each m_i in [2, MAX_M-1] (15).
 *   - prod(ms) < MAX_CFG_COUNT.
 * These bounds comfortably cover the paper's n=3..9 regime (M_9 = 8748).
 */

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* --------------------------------------------------------------------- */
/* Compile-time bounds                                                   */
/* --------------------------------------------------------------------- */

#define MAX_N          10
#define MAX_M          16          /* per-coordinate state count <= 15   */
#define MAX_CFG_COUNT  (12 * 1024) /* prod(ms) <= M_9 = 8748 < 12288     */
#define MAX_RT         (MAX_N * MAX_M * MAX_M * MAX_M)  /* rule-table idx space */

/* --------------------------------------------------------------------- */
/* Global problem state (set once per invocation)                        */
/* --------------------------------------------------------------------- */

static int g_n;                             /* ring size                 */
static int g_ms[MAX_N];                     /* multiset                  */
static int g_cfg_count;                     /* prod(ms)                  */
static uint16_t g_all_configs[MAX_CFG_COUNT]; /* lex-ordered packed cfgs */

/* cfg packing: 4 bits per coordinate, least-significant = position 0.
   Max 10 positions * 4 bits = 40 bits, fits easily in uint16_t is NOT
   true; we need uint64_t. But prod(ms) is the index, so an index fits
   in uint16_t (since <= 12288 < 65536). We store cfgs as indices into
   g_all_configs (uint16_t), and decode coordinates via an inverse
   lookup (g_cfg_coords). */

static uint8_t g_cfg_coords[MAX_CFG_COUNT][MAX_N]; /* inverse of g_all_configs */

/* We use a mixed-radix encoder to index configs:
   cfg_hash(c) = c[0] + c[1]*m_0 + c[2]*m_0*m_1 + ...
   which fits in uint16_t (< prod(ms) <= 12288). No lookup table needed. */

static int g_radix_stride[MAX_N];   /* stride[i] = prod(m_0..m_{i-1})    */

/* --------------------------------------------------------------------- */
/* Rule table                                                            */
/* --------------------------------------------------------------------- */

/* rt[rt_key(p, L, S, R)] ∈ {-1, 0..m_p-1}, where -1 means "free". */
static int8_t g_rt[MAX_RT];

static inline int rt_key(int p, int L, int S, int R) {
    /* Flat: (((p * MAX_M) + L) * MAX_M + S) * MAX_M + R */
    return ((p * MAX_M + L) * MAX_M + S) * MAX_M + R;
}

/* --------------------------------------------------------------------- */
/* Config encode / decode                                                */
/* --------------------------------------------------------------------- */

static inline int cfg_hash(const uint8_t c[]) {
    int h = 0;
    for (int i = g_n - 1; i >= 0; --i) {
        h = h * g_ms[i] + c[i];
    }
    return h;
}

static void init_configs(void) {
    g_cfg_count = 1;
    for (int i = 0; i < g_n; ++i) {
        g_radix_stride[i] = g_cfg_count;
        g_cfg_count *= g_ms[i];
    }
    assert(g_cfg_count <= MAX_CFG_COUNT);

    /* Enumerate in hash order (== lex order over coordinates since
       stride[0]=1, stride[1]=m_0, ..., so incrementing the hash
       cycles through c[0] fastest). But we want *lex* order, which
       means c[0] varies SLOWEST. Reorder: produce cfgs in lex order
       and record their hash. */
    uint8_t c[MAX_N] = {0};
    for (int idx = 0; idx < g_cfg_count; ++idx) {
        int h = cfg_hash(c);
        g_all_configs[idx] = (uint16_t)h;
        memcpy(g_cfg_coords[h], c, g_n);
        /* Increment c in lex order (c[n-1] varies fastest). */
        for (int j = g_n - 1; j >= 0; --j) {
            if (++c[j] < g_ms[j]) break;
            c[j] = 0;
        }
    }
}

/* --------------------------------------------------------------------- */
/* Verifier                                                              */
/* --------------------------------------------------------------------- */

/* Privilege count per config; also records the single priv processor
   when count is exactly 1. */
static uint8_t g_priv_count[MAX_CFG_COUNT];
static uint8_t g_priv_one[MAX_CFG_COUNT]; /* only valid where priv_count == 1 */

static void compute_priv(void) {
    for (int h = 0; h < g_cfg_count; ++h) {
        const uint8_t *c = g_cfg_coords[h];
        int cnt = 0, last = 0;
        for (int i = 0; i < g_n; ++i) {
            int L = c[(i + g_n - 1) % g_n];
            int S = c[i];
            int R = c[(i + 1) % g_n];
            int out = g_rt[rt_key(i, L, S, R)];
            if (out != S) {
                cnt += 1;
                last = i;
                if (cnt > 1) break;
            }
        }
        g_priv_count[h] = (uint8_t)cnt;
        g_priv_one[h] = (uint8_t)last;
    }
}

/* Deterministic successor at config h under processor p (assumes p is
   privileged). */
static int apply_move(int h, int p) {
    uint8_t c[MAX_N];
    memcpy(c, g_cfg_coords[h], g_n);
    int L = c[(p + g_n - 1) % g_n];
    int S = c[p];
    int R = c[(p + 1) % g_n];
    c[p] = (uint8_t)g_rt[rt_key(p, L, S, R)];
    (void)S;
    return cfg_hash(c);
}

/* Return codes for verify. 0 = valid (BUG if this happens at sub-
   threshold!). Otherwise the first property that fails. */
enum {
    V_VALID                   = 0,
    V_LIVENESS                = 1,
    V_MUTUAL_EXCLUSION        = 2,
    V_CLOSURE                 = 3,
    V_CONVERGENCE             = 4,
    V_FAIRNESS                = 5,
    V_CONNECTEDNESS           = 6,
    V_NO_GOOD_CYCLE           = 7,  /* closed single-priv set has no cycle */
};

static int g_fail_witness;  /* config index that surfaced the failure */

/* Iterative DFS with 3-coloring to detect any cycle in a sub-digraph
   described by a node set `mask` and a per-node successor list.
   Used for convergence (no cycle in bad configs under any daemon
   choice).

   We build the bad-successor lists on the fly (indexed by config
   hash). The deterministic good-successor list is already implicit
   from priv_one + apply_move.

   Returns true if ANY cycle exists in the bad-config nondeterministic
   subgraph. */

static uint8_t g_is_good[MAX_CFG_COUNT];
static int8_t g_color[MAX_CFG_COUNT];  /* 0=white, 1=gray, 2=black */

static bool bad_has_cycle(void) {
    memset(g_color, 0, sizeof(int8_t) * g_cfg_count);
    int stack[MAX_CFG_COUNT * 2];
    for (int start = 0; start < g_cfg_count; ++start) {
        if (g_is_good[start] || g_color[start] != 0) continue;
        int sp = 0;
        stack[sp++] = start;
        stack[sp++] = 0;     /* successor-iteration cursor */
        g_color[start] = 1;
        while (sp > 0) {
            int cur_sp = sp - 2;
            int node = stack[cur_sp];
            int cursor = stack[cur_sp + 1];
            const uint8_t *c = g_cfg_coords[node];
            bool pushed = false;
            int priv_idx = 0;
            for (int p = 0; p < g_n; ++p) {
                int L = c[(p + g_n - 1) % g_n];
                int S = c[p];
                int R = c[(p + 1) % g_n];
                int out = g_rt[rt_key(p, L, S, R)];
                if (out == S) continue;
                if (priv_idx < cursor) { priv_idx += 1; continue; }
                priv_idx += 1;
                int succ = apply_move(node, p);
                if (g_is_good[succ]) continue;            /* no edge in bad subgraph */
                if (g_color[succ] == 1) {
                    g_fail_witness = succ;
                    return true;
                }
                if (g_color[succ] == 2) continue;         /* already done, no cycle via it */
                g_color[succ] = 1;
                stack[cur_sp + 1] = priv_idx;             /* resume after this priv */
                stack[sp++] = succ;
                stack[sp++] = 0;
                pushed = true;
                break;
            }
            if (!pushed) {
                g_color[node] = 2;
                sp -= 2;
            }
        }
    }
    return false;
}

/* Compute the good set. Algorithm:
   1. single_priv = {h : priv_count[h] == 1}
   2. Iteratively remove h whose deterministic successor (apply_move with
      priv_one[h]) leaves the set.
   3. The remaining set contains the cycles + their basins. If empty,
      no good set exists.

   Returns:
     V_VALID / V_CLOSURE / V_NO_GOOD_CYCLE / V_FAIRNESS / V_CONVERGENCE /
     V_CONNECTEDNESS per the rules spelled out inline.
*/
static int verify(void) {
    compute_priv();

    /* Liveness. */
    for (int h = 0; h < g_cfg_count; ++h) {
        if (g_priv_count[h] == 0) {
            g_fail_witness = h;
            return V_LIVENESS;
        }
    }

    /* Build single-priv set and successor map. */
    static uint8_t in_set[MAX_CFG_COUNT];
    static int succ_of[MAX_CFG_COUNT];
    memset(in_set, 0, sizeof(uint8_t) * g_cfg_count);
    for (int h = 0; h < g_cfg_count; ++h) {
        if (g_priv_count[h] == 1) {
            in_set[h] = 1;
            succ_of[h] = apply_move(h, g_priv_one[h]);
        } else {
            succ_of[h] = -1;
        }
    }

    /* Iteratively remove h whose succ leaves the set. */
    bool changed = true;
    while (changed) {
        changed = false;
        for (int h = 0; h < g_cfg_count; ++h) {
            if (in_set[h] && !in_set[succ_of[h]]) {
                in_set[h] = 0;
                changed = true;
            }
        }
    }

    /* Find cycles within in_set (functional subgraph: each node has
       exactly one outgoing edge in the set). */
    static int8_t vcol[MAX_CFG_COUNT];
    memset(vcol, 0, sizeof(int8_t) * g_cfg_count);
    int any_cycle_start = -1;
    /* walk from each in_set node; first revisit closes a cycle */
    for (int h = 0; h < g_cfg_count; ++h) {
        if (!in_set[h] || vcol[h] != 0) continue;
        int trail[MAX_CFG_COUNT];
        int tlen = 0;
        int node = h;
        while (vcol[node] == 0) {
            vcol[node] = 1;  /* on current walk */
            trail[tlen++] = node;
            node = succ_of[node];
        }
        if (vcol[node] == 1) {
            /* Found a cycle in this walk; record and mark members. */
            any_cycle_start = node;
            for (int k = 0; k < tlen; ++k) vcol[trail[k]] = 2;
            break;
        }
        /* otherwise, node is in an earlier walk's cycle — fine */
        for (int k = 0; k < tlen; ++k) vcol[trail[k]] = 2;
    }

    if (any_cycle_start < 0) {
        g_fail_witness = 0;
        return V_NO_GOOD_CYCLE;
    }

    /* Trace the cycle starting at any_cycle_start. */
    int cyc[MAX_CFG_COUNT];
    int clen = 0;
    int node = any_cycle_start;
    do {
        cyc[clen++] = node;
        node = succ_of[node];
    } while (node != any_cycle_start);

    /* Fairness: cycle must include every processor as a mover. */
    bool seen[MAX_N] = {false};
    for (int k = 0; k < clen; ++k) {
        int h = cyc[k];
        int p = g_priv_one[h];
        seen[p] = true;
    }
    for (int i = 0; i < g_n; ++i) {
        if (!seen[i]) {
            g_fail_witness = cyc[0];
            return V_FAIRNESS;
        }
    }

    /* Build the good set: the cycle + all configs in in_set that
       eventually reach the cycle via succ. Since in_set has been
       iteratively cleaned, every node in in_set reaches a cycle.
       But we need to make sure it's THIS cycle (not another). If
       there's more than one cycle, that's a connectedness failure. */
    static uint8_t on_cycle[MAX_CFG_COUNT];
    memset(on_cycle, 0, sizeof(uint8_t) * g_cfg_count);
    for (int k = 0; k < clen; ++k) on_cycle[cyc[k]] = 1;

    /* For each in_set node, check it reaches any on_cycle node. */
    /* Since functional successor is unique, follow succ until we hit
       on_cycle or a visited node. */
    static uint8_t reaches[MAX_CFG_COUNT];
    memset(reaches, 0, sizeof(uint8_t) * g_cfg_count);
    for (int k = 0; k < clen; ++k) reaches[cyc[k]] = 1;
    for (int h = 0; h < g_cfg_count; ++h) {
        if (!in_set[h] || reaches[h]) continue;
        int trail[MAX_CFG_COUNT];
        int tlen = 0;
        int node2 = h;
        while (in_set[node2] && !reaches[node2]) {
            trail[tlen++] = node2;
            node2 = succ_of[node2];
            if (tlen > g_cfg_count) break;  /* shouldn't happen */
        }
        bool ok = reaches[node2];
        for (int k = 0; k < tlen; ++k) reaches[trail[k]] = ok ? 1 : 0;
        if (!ok) {
            /* A second cycle exists in in_set. */
            g_fail_witness = trail[0];
            return V_CONNECTEDNESS;
        }
    }

    /* The good set is everything flagged `reaches`; bad is the rest.
       Convergence: no cycle in the bad non-deterministic subgraph. */
    for (int h = 0; h < g_cfg_count; ++h) g_is_good[h] = reaches[h];
    if (bad_has_cycle()) {
        return V_CONVERGENCE;  /* g_fail_witness set by bad_has_cycle */
    }

    return V_VALID;
}

static const char *PROP_NAME[] = {
    [V_VALID]            = "valid",
    [V_LIVENESS]         = "liveness",
    [V_MUTUAL_EXCLUSION] = "mutual_exclusion",
    [V_CLOSURE]          = "closure",
    [V_CONVERGENCE]      = "convergence",
    [V_FAIRNESS]         = "fairness",
    [V_CONNECTEDNESS]    = "connectedness",
    [V_NO_GOOD_CYCLE]    = "no_good_cycle",
};

/* --------------------------------------------------------------------- */
/* Cycle enumeration (DFS with det propagation)                          */
/* --------------------------------------------------------------------- */

/* --------------------------------------------------------------------- */
/* JSON emission (by hand)                                               */
/* --------------------------------------------------------------------- */

static long long g_stat_cycles = 0;
static long long g_stat_completions = 0;
static long long g_stat_rejections = 0;
static long long g_stat_valid = 0;

static void emit_int_array(const uint8_t *a, int n) {
    putchar('[');
    for (int i = 0; i < n; ++i) {
        if (i) putchar(',');
        printf("%d", a[i]);
    }
    putchar(']');
}

static void emit_cycle(const int cycle_hashes[], int cycle_len) {
    putchar('[');
    for (int i = 0; i < cycle_len; ++i) {
        if (i) putchar(',');
        emit_int_array(g_cfg_coords[cycle_hashes[i]], g_n);
    }
    putchar(']');
}

static void emit_movers(const int movers[], int mover_count) {
    putchar('[');
    for (int i = 0; i < mover_count; ++i) {
        if (i) putchar(',');
        printf("%d", movers[i]);
    }
    putchar(']');
}

static void emit_det(const int keys[], int n_keys) {
    putchar('{');
    bool first = true;
    for (int k = 0; k < n_keys; ++k) {
        int key = keys[k];
        int R = key % MAX_M; key /= MAX_M;
        int S = key % MAX_M; key /= MAX_M;
        int L = key % MAX_M; key /= MAX_M;
        int p = key;
        int out = g_rt[keys[k]];
        if (!first) putchar(',');
        first = false;
        printf("\"%d,%d,%d,%d\":%d", p, L, S, R, out);
    }
    putchar('}');
}

/* --------------------------------------------------------------------- */
/* Rule-table completion enumeration                                     */
/* --------------------------------------------------------------------- */

static int g_free_keys[MAX_RT];
static int g_free_count;

static void compute_free_keys(void) {
    g_free_count = 0;
    for (int p = 0; p < g_n; ++p) {
        int mL = g_ms[(p + g_n - 1) % g_n];
        int mS = g_ms[p];
        int mR = g_ms[(p + 1) % g_n];
        for (int L = 0; L < mL; ++L) {
            for (int S = 0; S < mS; ++S) {
                for (int R = 0; R < mR; ++R) {
                    int k = rt_key(p, L, S, R);
                    if (g_rt[k] == -1) {
                        g_free_keys[g_free_count++] = k;
                    }
                }
            }
        }
    }
}

static int g_orient[MAX_N];
static bool g_summary_only = false;

static void emit_cert(int cycle_len, const int cycle_hashes[],
                      const int movers[], int mover_count,
                      const int det_keys[], int det_key_count,
                      const int free_keys[], int free_count,
                      const int8_t completion_values[], int prop) {
    if (g_summary_only) return;
    printf("{\"schema_version\":1,\"kind\":\"rejection\",");
    printf("\"n\":%d,", g_n);
    printf("\"ms_sorted\":");
    putchar('[');
    /* sorted view of orientation */
    int sorted_ms[MAX_N];
    memcpy(sorted_ms, g_orient, sizeof(int) * g_n);
    for (int i = 1; i < g_n; ++i) {
        int x = sorted_ms[i];
        int j = i - 1;
        while (j >= 0 && sorted_ms[j] > x) {
            sorted_ms[j + 1] = sorted_ms[j]; j--;
        }
        sorted_ms[j + 1] = x;
    }
    for (int i = 0; i < g_n; ++i) {
        if (i) putchar(',');
        printf("%d", sorted_ms[i]);
    }
    putchar(']');
    printf(",\"orientation\":[");
    for (int i = 0; i < g_n; ++i) {
        if (i) putchar(',');
        printf("%d", g_orient[i]);
    }
    printf("]");
    long long prod = 1;
    for (int i = 0; i < g_n; ++i) prod *= g_orient[i];
    printf(",\"product\":%lld", prod);
    printf(",\"cycle\":"); emit_cycle(cycle_hashes, cycle_len);
    printf(",\"movers\":"); emit_movers(movers, mover_count);
    printf(",\"det_forced\":"); emit_det(det_keys, det_key_count);
    /* completion: the free-key assignments */
    printf(",\"completion\":{");
    bool first = true;
    for (int i = 0; i < free_count; ++i) {
        int key = free_keys[i];
        int kk = key;
        int R = kk % MAX_M; kk /= MAX_M;
        int S = kk % MAX_M; kk /= MAX_M;
        int L = kk % MAX_M; kk /= MAX_M;
        int p = kk;
        if (!first) putchar(',');
        first = false;
        printf("\"%d,%d,%d,%d\":%d", p, L, S, R, completion_values[i]);
    }
    printf("}");
    printf(",\"property_failed\":\"%s\"", PROP_NAME[prop]);
    printf("}\n");
}

/* Branch-exhaust completion DFS with immediate verify at each leaf. */
static int8_t g_completion_values[MAX_RT];

static bool run_completions(int cycle_len, const int cycle_hashes[],
                            const int movers[], int mover_count,
                            const int det_keys[], int det_key_count) {
    if (g_free_count == 0) {
        g_stat_completions += 1;
        int v = verify();
        if (v == V_VALID) {
            g_stat_valid += 1;
            fprintf(stderr, "FATAL: sub-threshold VALID system. "
                    "Cycle len=%d (free=0). This contradicts M_n.\n", cycle_len);
            return true;
        }
        g_stat_rejections += 1;
        emit_cert(cycle_len, cycle_hashes, movers, mover_count,
                  det_keys, det_key_count,
                  g_free_keys, g_free_count, g_completion_values, v);
        return false;
    }
    /* Odometer over free keys. Each digit d ranges over 0..mp-1 where
       mp = m_p for the mover p of g_free_keys[d]. Initial = all zeros. */
    for (int i = 0; i < g_free_count; ++i) {
        g_rt[g_free_keys[i]] = 0;
        g_completion_values[i] = 0;
    }
    while (true) {
        g_stat_completions += 1;
        int v = verify();
        if (v == V_VALID) {
            g_stat_valid += 1;
            fprintf(stderr, "FATAL: sub-threshold VALID system. "
                    "Cycle len=%d. This contradicts M_n.\n", cycle_len);
            return true;
        }
        g_stat_rejections += 1;
        emit_cert(cycle_len, cycle_hashes, movers, mover_count,
                  det_keys, det_key_count,
                  g_free_keys, g_free_count, g_completion_values, v);
        /* Increment odometer from rightmost digit. */
        int d = g_free_count - 1;
        while (d >= 0) {
            int k = g_free_keys[d];
            int mp = g_ms[k / (MAX_M * MAX_M * MAX_M)];
            if (g_completion_values[d] + 1 < mp) {
                g_completion_values[d] += 1;
                g_rt[k] = g_completion_values[d];
                break;
            }
            g_completion_values[d] = 0;
            g_rt[k] = 0;
            d -= 1;
        }
        if (d < 0) break;
    }
    /* Restore free keys to -1 so cycle-DFS backtrack sees them free. */
    for (int i = 0; i < g_free_count; ++i) g_rt[g_free_keys[i]] = -1;
    return false;
}

/* --------------------------------------------------------------------- */
/* Cycle-enumeration DFS                                                 */
/* --------------------------------------------------------------------- */

/* Returns true if a sub-threshold valid witness was found (fatal). */
static bool enumerate_cycles(int L_cap) {
    /* Start from each lex-min config. Within the DFS, we also enforce
       "new config >= start", which guarantees each cycle is enumerated
       from its unique lex-min rotation. */
    for (int start_h = 0; start_h < g_cfg_count; ++start_h) {
        /* Initialise state: path = [start_h]. Nothing forced yet.
           As we extend, we add rt entries via forced-neighbor, tracking
           which keys we added so we can undo on backtrack. */
        int path[MAX_CFG_COUNT];
        int path_len = 1;
        path[0] = start_h;
        uint8_t visited[MAX_CFG_COUNT] = {0};
        visited[start_h] = 1;
        int movers[MAX_CFG_COUNT];
        int mover_count = 0;
        bool mover_seen[MAX_N] = {false};
        /* det_key_stack[i] = list of keys added at step i; each step
           can add up to n keys (one mover + up to n-1 silent). */
        int added_at_depth[MAX_CFG_COUNT][MAX_N + 1];
        int n_added[MAX_CFG_COUNT] = {0};
        /* Branch iteration cursor for each depth. */
        int cursor[MAX_CFG_COUNT];
        cursor[0] = 0;
        int max_branches_per_step = g_n * MAX_M; /* (p, new_val) pairs */

        while (path_len > 0) {
            int cur_h = path[path_len - 1];
            const uint8_t *c = g_cfg_coords[cur_h];
            /* Look up next (p, new_val) we haven't tried at this depth. */
            int branch = cursor[path_len - 1];
            /* branches enumerated: (p=0..n-1, new_val=0..m_p-1) with new_val != c[p].
               Linearize: for each p, sub-index = new_val; skip where ==c[p]. */
            int chosen_p = -1, chosen_nv = -1;
            int lin = 0;
            for (int p = 0; p < g_n && chosen_p < 0; ++p) {
                for (int nv = 0; nv < g_ms[p]; ++nv) {
                    if (nv == c[p]) continue;
                    if (lin == branch) { chosen_p = p; chosen_nv = nv; }
                    lin += 1;
                    if (chosen_p >= 0) break;
                }
            }
            if (chosen_p < 0) {
                /* Exhausted branches at this depth. Backtrack. */
                int undo_keys = n_added[path_len - 1];
                for (int u = 0; u < undo_keys; ++u) {
                    g_rt[added_at_depth[path_len - 1][u]] = -1;
                }
                n_added[path_len - 1] = 0;
                path_len -= 1;
                if (path_len > 0) {
                    int taken_h = path[path_len];
                    visited[taken_h] = 0;
                    /* restore mover_seen bookkeeping */
                    if (mover_count > 0) {
                        int last_mover = movers[mover_count - 1];
                        /* compute how many times last_mover appears in prior movers */
                        int prior = 0;
                        for (int mk = 0; mk < mover_count - 1; ++mk) {
                            if (movers[mk] == last_mover) { prior = 1; break; }
                        }
                        if (!prior) mover_seen[last_mover] = false;
                        mover_count -= 1;
                    }
                }
                (void)max_branches_per_step;
                continue;
            }
            cursor[path_len - 1] = branch + 1;

            /* Attempt (p=chosen_p, new_val=chosen_nv). */
            int p = chosen_p;
            int nv = chosen_nv;
            int L = c[(p + g_n - 1) % g_n];
            int S = c[p];
            int R = c[(p + 1) % g_n];
            int mover_key = rt_key(p, L, S, R);
            int local_added[MAX_N + 1];
            int local_added_count = 0;
            bool consistent = true;

            if (g_rt[mover_key] != -1) {
                if (g_rt[mover_key] != nv) continue;
            } else {
                g_rt[mover_key] = (int8_t)nv;
                local_added[local_added_count++] = mover_key;
            }
            /* Silent propagation on non-movers. */
            for (int i = 0; i < g_n; ++i) {
                if (i == p) continue;
                int Li = c[(i + g_n - 1) % g_n];
                int Si = c[i];
                int Ri = c[(i + 1) % g_n];
                int ki = rt_key(i, Li, Si, Ri);
                if (g_rt[ki] != -1) {
                    if (g_rt[ki] != Si) { consistent = false; break; }
                } else {
                    g_rt[ki] = (int8_t)Si;
                    local_added[local_added_count++] = ki;
                }
            }
            if (!consistent) {
                for (int u = 0; u < local_added_count; ++u) {
                    g_rt[local_added[u]] = -1;
                }
                continue;
            }

            /* Compute new_cfg. */
            uint8_t new_c[MAX_N];
            memcpy(new_c, c, g_n);
            new_c[p] = (uint8_t)nv;
            int new_h = cfg_hash(new_c);

            /* Closure? */
            if (new_h == start_h && path_len >= g_n) {
                /* Fairness: every processor moved at least once. */
                bool all_seen = true;
                for (int i = 0; i < g_n; ++i) {
                    bool s = (i == p) || mover_seen[i];
                    if (!s) { all_seen = false; break; }
                }
                if (all_seen) {
                    /* Mutual exclusion on every cycle config against
                       the det accumulated so far. */
                    bool me_ok = true;
                    for (int k = 0; k < path_len; ++k) {
                        const uint8_t *cc = g_cfg_coords[path[k]];
                        int priv = 0;
                        for (int i = 0; i < g_n; ++i) {
                            int Li = cc[(i + g_n - 1) % g_n];
                            int Si = cc[i];
                            int Ri = cc[(i + 1) % g_n];
                            int ki = rt_key(i, Li, Si, Ri);
                            int out = g_rt[ki];
                            if (out != -1 && out != Si) {
                                priv += 1;
                                if (priv > 1) break;
                            }
                        }
                        if (priv != 1) { me_ok = false; break; }
                    }
                    if (me_ok) {
                        /* Capture list of det keys currently set. */
                        int det_keys[MAX_RT];
                        int det_count = 0;
                        for (int kk = 0; kk < MAX_RT; ++kk) {
                            if (g_rt[kk] != -1) {
                                det_keys[det_count++] = kk;
                            }
                        }
                        g_stat_cycles += 1;
                        /* Build mover list for emission. */
                        int mvr[MAX_CFG_COUNT];
                        memcpy(mvr, movers, sizeof(int) * mover_count);
                        mvr[mover_count] = p;
                        /* Before running completions, compute g_free_keys. */
                        compute_free_keys();
                        /* Save the forced-det outputs so completion DFS
                           can branch cleanly (it only touches g_rt[k]
                           for k in g_free_keys). */
                        bool fatal = run_completions(
                            path_len, path, mvr, mover_count + 1,
                            det_keys, det_count);
                        if (fatal) return true;
                    }
                }
                for (int u = 0; u < local_added_count; ++u) {
                    g_rt[local_added[u]] = -1;
                }
                continue;
            }

            if (visited[new_h]) {
                for (int u = 0; u < local_added_count; ++u) {
                    g_rt[local_added[u]] = -1;
                }
                continue;
            }
            /* Lex-min start filter. */
            if (new_h < start_h) {
                for (int u = 0; u < local_added_count; ++u) {
                    g_rt[local_added[u]] = -1;
                }
                continue;
            }
            if (path_len >= L_cap) {
                for (int u = 0; u < local_added_count; ++u) {
                    g_rt[local_added[u]] = -1;
                }
                continue;
            }
            /* Fairness pruning. */
            {
                int unseen = 0;
                for (int i = 0; i < g_n; ++i) {
                    bool s = (i == p) || mover_seen[i];
                    if (!s) unseen += 1;
                }
                int remaining = L_cap - path_len;
                if (unseen > remaining) {
                    for (int u = 0; u < local_added_count; ++u) {
                        g_rt[local_added[u]] = -1;
                    }
                    continue;
                }
            }

            /* Descend. */
            path[path_len] = new_h;
            visited[new_h] = 1;
            movers[mover_count++] = p;
            if (!mover_seen[p]) mover_seen[p] = true;
            /* Record what we added at the NEW depth (path_len). */
            for (int u = 0; u < local_added_count; ++u) {
                added_at_depth[path_len][u] = local_added[u];
            }
            n_added[path_len] = local_added_count;
            cursor[path_len] = 0;
            path_len += 1;
        }

        /* All g_rt entries added under this start have been cleared by
           backtracking; reset cursor for next start. */
        (void)max_branches_per_step;
    }
    return false;
}

/* --------------------------------------------------------------------- */
/* Main                                                                  */
/* --------------------------------------------------------------------- */

static void usage(const char *prog) {
    fprintf(stderr,
            "Usage: %s --n N --ms M0,M1,... --orient M0,M1,... [--summary-only]\n", prog);
}

static int parse_csv_ints(const char *s, int *out, int max_out) {
    int n = 0;
    const char *p = s;
    while (*p && n < max_out) {
        char *end;
        long v = strtol(p, &end, 10);
        if (end == p) return -1;
        out[n++] = (int)v;
        p = end;
        if (*p == ',') p += 1;
        else if (*p == '\0') break;
        else return -1;
    }
    return n;
}

int main(int argc, char **argv) {
    int orient[MAX_N];
    int orient_n = 0;
    int want_n = -1;

    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--n") && i + 1 < argc) {
            want_n = atoi(argv[++i]);
        } else if (!strcmp(argv[i], "--orient") && i + 1 < argc) {
            orient_n = parse_csv_ints(argv[++i], orient, MAX_N);
        } else if (!strcmp(argv[i], "--ms") && i + 1 < argc) {
            /* Ignored at this level; the caller should pass the sorted
               multiset only for logging. We use --orient for actual work. */
            ++i;
        } else if (!strcmp(argv[i], "--summary-only")) {
            g_summary_only = true;
        } else {
            usage(argv[0]);
            return 2;
        }
    }
    if (orient_n < 3 || orient_n > MAX_N) {
        usage(argv[0]); return 2;
    }
    if (want_n > 0 && want_n != orient_n) {
        fprintf(stderr, "Mismatch: --n %d vs orient length %d\n",
                want_n, orient_n);
        return 2;
    }
    g_n = orient_n;
    memcpy(g_ms, orient, sizeof(int) * g_n);
    memcpy(g_orient, orient, sizeof(int) * g_n);
    for (int i = 0; i < g_n; ++i) {
        if (g_ms[i] < 2 || g_ms[i] >= MAX_M) {
            fprintf(stderr, "m_%d=%d out of range [2,%d)\n",
                    i, g_ms[i], MAX_M);
            return 2;
        }
    }

    init_configs();
    memset(g_rt, -1, sizeof(g_rt));

    int L_cap = 3 * g_n;
    if (2 * g_cfg_count / g_n > L_cap) L_cap = 2 * g_cfg_count / g_n;
    if (L_cap > MAX_CFG_COUNT - 1) L_cap = MAX_CFG_COUNT - 1;

    bool fatal = enumerate_cycles(L_cap);

    printf("{\"kind\":\"summary\","
           "\"n\":%d,\"orientation\":[", g_n);
    for (int i = 0; i < g_n; ++i) {
        if (i) putchar(',');
        printf("%d", g_orient[i]);
    }
    long long prod = 1;
    for (int i = 0; i < g_n; ++i) prod *= g_orient[i];
    printf("],\"product\":%lld", prod);
    printf(",\"candidate_cycles\":%lld", g_stat_cycles);
    printf(",\"completions_tried\":%lld", g_stat_completions);
    printf(",\"rejections\":%lld", g_stat_rejections);
    printf(",\"valid_found\":%lld", g_stat_valid);
    printf("}\n");

    return fatal ? 1 : 0;
}
