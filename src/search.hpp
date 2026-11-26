// Backward MITM chain search over a pool.
#pragma once
#include "santa.hpp"

// A chain element: value v = A op B, where operand refs are >=0 pool index, or <0 => chain index (-1-j).
struct CNode { ll v; int op; int a, b; };

struct R1Entry { int op; int a, b; }; // a,b pool indices

struct Pool {
    ll L;
    vector<ll> vals;            // pool values (index = pool idx)
    HMap pidx;                  // value -> pool idx
    vector<R1Entry> r1;         // one-step values not in pool
    vector<ll> r1v;
    HMap r1idx;                 // value -> r1 index
    void init(ll L_) { L = L_; vals.clear(); pidx.init(1024); r1.clear(); r1v.clear(); r1idx.init(1 << 16); }
    // add a value to the pool, updating R1 incrementally
    int add(ll v) {
        int e = pidx.get(v);
        if (e >= 0) return e;
        int id = vals.size(); vals.push_back(v); pidx.put(v, id);
        // new one-step values: v op p, p op v for all p (including itself)
        for (int j = 0; j <= id; j++) {
            ll p = vals[j];
            add_r1(OP_ADD, id, j, v + p);
            { i128 m = (i128)v * p; if (m <= (i128)L) add_r1(OP_MUL, id, j, (ll)m); }
            if (v > p) add_r1(OP_SUB, id, j, v - p); else if (p > v) add_r1(OP_SUB, j, id, p - v);
            if (p != 0 && v % p == 0 && v != p) add_r1(OP_DIV, id, j, v / p);
            if (v != 0 && p % v == 0 && v != p) add_r1(OP_DIV, j, id, p / v);
            if (v == p) add_r1(OP_DIV, id, id, 1);
        }
        return id;
    }
    inline void add_r1(int op, int a, int b, ll v) {
        if (v < 1 || v > L) return;
        if (pidx.get(v) >= 0) return;
        if (r1idx.put(v, (int)r1.size())) { r1.push_back({op, a, b}); r1v.push_back(v); }
    }
    // when a value becomes a pool value, it may already be in r1: we leave stale r1 entries (harmless: lookups
    // check pool first).
};

// inverse candidates: values x such that (x op p == T) or (p op x == T). Writes up to 6 entries.
// For each candidate also records (op, xfirst) so the forward instruction can be reconstructed:
// xfirst=1 means T = x op p, else T = p op x.
struct Inv { ll x; int op; int xfirst; };
static inline int inverses(ll T, ll p, ll L, Inv* out) {
    int n = 0;
    if (T > p) out[n++] = {T - p, OP_ADD, 1};                       // x + p = T
    { ll x = T + p; if (x <= L && x > T) out[n++] = {x, OP_SUB, 1}; } // x - p = T
    if (p > T) out[n++] = {p - T, OP_SUB, 0};                        // p - x = T
    if (T % p == 0) { ll x = T / p; if (x >= 1) out[n++] = {x, OP_MUL, 1}; }  // x * p = T
    { i128 x = (i128)T * p; if (x <= (i128)L) out[n++] = {(ll)x, OP_DIV, 1}; } // x / p = T
    if (p % T == 0) { ll x = p / T; if (x >= 1) out[n++] = {x, OP_DIV, 0}; }   // p / x = T
    return n;
}

struct Searcher {
    const Pool* P; ll L;
    vector<CNode> best; int bestc;
    long long probes = 0;

    // Is value s obtainable with cost exactly <= c (c in {0,1}) ? returns chain via cb
    // We build chains backwards: stack of (value, op, other operand ref, xfirst)
    struct Step { ll v; int op; int oref; int xfirst; }; // v = result of this step; operand chain value is 'next' value
    vector<Step> stk;

    // emit chain from stk plus terminal (s found in pool or r1)
    void emit(int termPool, int termR1) {
        // stk[0] is the final step (produces T), stk[k] produces stk[k-1]'s chain operand.
        // terminal value is the chain operand of the last stack element.
        vector<CNode> ch;
        int termRef;
        if (termPool >= 0) termRef = termPool;
        else {
            const R1Entry& e = P->r1[termR1];
            ch.push_back({P->r1v[termR1], e.op, e.a, e.b});
            termRef = -1 - 0;
        }
        // other operands that are r1 values need their own nodes
        int cur = termRef;
        for (int k = (int)stk.size() - 1; k >= 0; k--) {
            const Step& s = stk[k];
            int oref = s.oref;
            if (oref < -1000000) { // r1 operand: encoded as -1000001 - r1index
                int ri = -1000001 - oref;
                const R1Entry& e = P->r1[ri];
                ch.push_back({P->r1v[ri], e.op, e.a, e.b});
                oref = -(int)ch.size(); // -1 - (size-1)
            }
            CNode nd; nd.v = s.v; nd.op = s.op;
            if (s.xfirst) { nd.a = cur; nd.b = oref; } else { nd.a = oref; nd.b = cur; }
            ch.push_back(nd);
            cur = -(int)ch.size();
        }
        best = ch; bestc = ch.size();
    }

    // depth-first: can s be produced with remaining budget r (number of new values incl. s)?
    // useR1: whether operands may be R1 values (costs one extra)
    bool dfs(ll s, int r, int maxR1ops) {
        // terminal checks
        int pi = P->pidx.get(s); probes++;
        if (pi >= 0) { emit(pi, -1); return true; }
        if (r <= 0) return false;
        int ri = P->r1idx.get(s); probes++;
        if (ri >= 0) { emit(-1, ri); return true; }
        if (r <= 1) return false;
        Inv iv[6];
        int m = P->vals.size();
        // operand from pool: costs 1 (the value s itself)
        for (int j = 0; j < m; j++) {
            ll p = P->vals[j];
            int n = inverses(s, p, L, iv);
            for (int t = 0; t < n; t++) {
                stk.push_back({s, iv[t].op, j, iv[t].xfirst});
                if (dfs(iv[t].x, r - 1, maxR1ops)) return true;
                stk.pop_back();
            }
        }
        // operand from R1: costs 2 (s and the operand); only when budget allows terminal r1 lookup after
        if (maxR1ops > 0 && r >= 3) {
            int nr = P->r1v.size();
            for (int j = 0; j < nr; j++) {
                ll p = P->r1v[j];
                if (P->pidx.get(p) >= 0) continue;
                int n = inverses(s, p, L, iv);
                for (int t = 0; t < n; t++) {
                    // remaining budget for chain operand: r - 2
                    ll x = iv[t].x;
                    if (r - 2 <= 1) {
                        // only terminal checks
                        int pi2 = P->pidx.get(x); probes++;
                        int ri2 = -1;
                        if (pi2 < 0 && r - 2 == 1) { ri2 = P->r1idx.get(x); probes++; }
                        if (pi2 >= 0 || ri2 >= 0) {
                            stk.push_back({s, iv[t].op, -1000001 - j, iv[t].xfirst});
                            emit(pi2, ri2); stk.pop_back(); return true;
                        }
                    } else {
                        stk.push_back({s, iv[t].op, -1000001 - j, iv[t].xfirst});
                        if (dfs(x, r - 2, maxR1ops - 1)) return true;
                        stk.pop_back();
                    }
                }
            }
        }
        return false;
    }

    // iterative deepening; returns cost or -1
    int search(ll T, int maxk, int maxR1ops = 1) {
        bestc = -1; best.clear();
        for (int k = 0; k <= maxk; k++) {
            stk.clear();
            if (dfs(T, k, maxR1ops)) return bestc;
        }
        return -1;
    }
};
