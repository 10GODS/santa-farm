// sa.cpp — slack annealing with exact bit-parallel knockout (own implementation).
// Representation: value graph. Moves: perturb (alternative recipes, possibly via a new helper value, within a length cap),
// exact knockout (drop any value whose consumers can be re-derived from other existing values; or drop 2 values with one new
// helper), MITM rotate (rebuild a value's private cone with <=2 fresh values). Accept strictly shorter, register-feasible programs.
#include "search.hpp"

static mt19937_64 rng(1);

struct Rec { int op; ll a, b; };   // op<0: start

struct VG {
    ll L; int nreg;
    vector<ll> starts, targets;
    unordered_map<ll, Rec> g;       // value -> recipe

    static inline ll calc(int op, ll a, ll b, ll L) { return apply_op(op, a, b, L); }

    // topological live order (cone of targets); returns false on cycle/missing
    bool order(vector<ll>& ord) const {
        unordered_map<ll, char> st; st.reserve(g.size() * 2); ord.clear();
        vector<pair<ll, int>> stack;
        for (ll t : targets) {
            if (st.count(t) && st[t] == 2) continue;
            stack.push_back({t, 0});
            while (!stack.empty()) {
                auto& [v, phase] = stack.back();
                auto it = g.find(v); if (it == g.end()) return false;
                if (it->second.op < 0) { st[v] = 2; stack.pop_back(); continue; }
                if (phase == 0) {
                    char& s = st[v];
                    if (s == 2) { stack.pop_back(); continue; }
                    if (s == 1) return false;
                    s = 1; phase = 1;
                    ll a = it->second.a, b = it->second.b;
                    if (!(st.count(a) && st[a] == 2)) stack.push_back({a, 0});
                    if (!(st.count(b) && st[b] == 2)) stack.push_back({b, 0});
                } else {
                    st[v] = 2; ord.push_back(v); stack.pop_back();
                }
            }
        }
        return true;
    }
    void prune(const vector<ll>& ord) {
        unordered_map<ll, Rec> ng; ng.reserve(ord.size() * 2 + 16);
        for (ll s : starts) ng[s] = {-1, 0, 0};
        for (ll v : ord) ng[v] = g.at(v);
        g.swap(ng);
    }
    int length() const { vector<ll> o; if (!order(o)) return INT_MAX; return o.size(); }
    // build node list for compile
    bool to_nodes(vector<Node>& nodes) const {
        vector<ll> o; if (!order(o)) return false;
        nodes.clear(); unordered_map<ll, int> idx;
        for (ll s : starts) if (!idx.count(s)) { idx[s] = nodes.size(); nodes.push_back({s, -1, -1, -1}); }
        for (ll v : o) { const Rec& r = g.at(v); nodes.push_back({v, r.op, idx.at(r.a), idx.at(r.b)}); idx[v] = nodes.size() - 1; }
        return true;
    }
};

struct Annealer {
    Puzzle Pz; VG best, champ;
    int bestLen;
    vector<array<int, 4>> bestProg;
    long long stat_ko = 0, stat_kh = 0, stat_rot = 0, stat_cfail = 0, stat_cross = 0, stat_cfix = 0, stat_regrej = 0;

    bool compile(const VG& G, vector<array<int, 4>>& prog) {
        vector<Node> nodes; if (!G.to_nodes(nodes)) return false;
        if (!nodes_to_prog_any(Pz, nodes, prog)) {
            if (getenv("SA_NOFIT")) return false;
            if (!schedule_fit(Pz, nodes, prog, 400, 0x5eed + nodes.size())) return false;
            stat_cfix++;
        }
        return verify_prog(Pz, prog) == (int)prog.size();
    }

    // ---------------- exact knockout ----------------
    // returns true if graph G was shortened (G updated)
    bool knockout(VG& G, bool tryHelpers, int capLen) {
        vector<ll> ord; if (!G.order(ord)) return false;
        G.prune(ord);
        vector<ll> val;
        { unordered_set<ll> s; for (ll x : G.starts) if (s.insert(x).second) val.push_back(x); }
        int first = val.size();
        for (ll v : ord) val.push_back(v);
        int n = val.size(); if (n > 512) return false;
        int words = (n + 63) / 64;
        HMap id; id.init(n * 2); for (int i = 0; i < n; i++) id.put(val[i], i);
        vector<char> req(n, 0); for (ll t : G.targets) { int i = id.get(t); if (i >= 0) req[i] = 1; }
        // direct recipes (flat) + first-witness table of non-existing results
        vector<int> dcnt(n, 0); vector<array<int, 3>> dlist; dlist.reserve(n * 8);
        vector<pair<int, array<int, 3>>> dtmp; dtmp.reserve(n * 8);
        HMap M; vector<ll> mval; vector<array<int, 3>> mwit;
        if (tryHelpers) M.init(n * n * 3 + 64);
        for (int i = 0; i < n; i++) for (int j = 0; j <= i; j++) {
            ll a = val[i], b = val[j];
            for (int op = 0; op < 4; op++) for (int sw = 0; sw < 2; sw++) {
                if (sw && (op == OP_ADD || op == OP_MUL || i == j)) continue;
                ll x = sw ? apply_op(op, b, a, Pz.L) : apply_op(op, a, b, Pz.L);
                if (!x) continue;
                int ia = sw ? j : i, ib = sw ? i : j;
                if (x == val[ia] || x == val[ib]) continue;
                int k = id.get(x);
                if (k >= 0) { if (k >= first) dtmp.push_back({k, {ia, ib, op}}); }
                else if (tryHelpers) { if (M.put(x, (int)mval.size())) { mval.push_back(x); mwit.push_back({ia, ib, op}); } }
            }
        }
        sort(dtmp.begin(), dtmp.end(), [](const pair<int, array<int, 3>>& p, const pair<int, array<int, 3>>& q) { return p.first < q.first; });
        vector<int> doff(n + 1, 0);
        for (auto& p : dtmp) dcnt[p.first]++;
        for (int i = 0; i < n; i++) doff[i + 1] = doff[i] + dcnt[i];
        for (auto& p : dtmp) dlist.push_back(p.second);
        typedef array<ull, 8> Bits;
        Bits sel{}; for (int i = first; i < n; i++) if (!req[i]) sel[i / 64] |= 1ULL << (i % 64);
        vector<Bits> allow(n), rows(n);
        for (int i = 0; i < n; i++) { allow[i] = sel; allow[i][i / 64] &= ~(1ULL << (i % 64)); rows[i] = Bits{}; if (i < first) rows[i] = sel; }
        for (int i = first; i < n; i++) if (req[i]) allow[i] = sel;
        // helper uses (flat): for helper index hi: list of (output v, other f or -1, code)
        vector<int> huoff; vector<array<int, 3>> hulist;
        auto close = [&](vector<Bits>& R, int hi, const Bits* hm) {
            bool ch = true;
            while (ch) {
                ch = false;
                for (int v = first; v < n; v++) for (int w = 0; w < words; w++) {
                    ull open = allow[v][w] & ~R[v][w]; if (!open) continue;
                    ull gain = 0;
                    for (int e = doff[v]; e < doff[v + 1]; e++) gain |= R[dlist[e][0]][w] & R[dlist[e][1]][w];
                    gain &= open;
                    if (gain) { R[v][w] |= gain; ch = true; }
                }
                if (hi >= 0) for (int e = huoff[hi]; e < huoff[hi + 1]; e++) {
                    auto& u = hulist[e]; int v = u[0];
                    for (int w = 0; w < words; w++) {
                        ull gain = allow[v][w] & ~R[v][w] & (*hm)[w] & (u[1] >= 0 ? R[u[1]][w] : ~0ULL);
                        if (gain) { R[v][w] |= gain; ch = true; }
                    }
                }
            }
        };
        close(rows, -1, nullptr);
        Bits ok = sel;
        for (int t = first; t < n; t++) if (req[t]) for (int w = 0; w < words; w++) ok[w] &= rows[t][w];
        auto rebuild = [&](const vector<int>& drops, int hi, VG& out) -> bool {
            vector<char> got(n, 0), ban(n, 0); for (int i = 0; i < first; i++) got[i] = 1;
            for (int d : drops) ban[d] = 1;
            vector<Rec> ch(n); bool hgot = false; Rec hrec{}; ll hv = hi >= 0 ? mval[hi] : 0;
            bool prog = true;
            while (prog) {
                prog = false;
                if (hi >= 0 && !hgot) { auto& e = mwit[hi]; if (got[e[0]] && got[e[1]]) { hgot = true; hrec = {e[2], val[e[0]], val[e[1]]}; prog = true; } }
                for (int v = first; v < n; v++) if (!got[v] && !ban[v]) {
                    for (int e = doff[v]; e < doff[v + 1]; e++) { auto& r = dlist[e]; if (got[r[0]] && got[r[1]]) { got[v] = 1; ch[v] = {r[2], val[r[0]], val[r[1]]}; prog = true; break; } }
                    if (!got[v] && hi >= 0 && hgot) for (int e = huoff[hi]; e < huoff[hi + 1]; e++) { auto& u = hulist[e]; if (u[0] == v && (u[1] < 0 || got[u[1]])) {
                        int op = u[2] & 3, hfirst = (u[2] >> 2) & 1; ll o = u[1] >= 0 ? val[u[1]] : hv;
                        got[v] = 1; ch[v] = hfirst ? Rec{op, hv, o} : Rec{op, o, hv}; prog = true; break; } }
                }
            }
            for (int t = first; t < n; t++) if (req[t] && !got[t]) return false;
            out = G; out.g.clear();
            for (ll s : G.starts) out.g[s] = {-1, 0, 0};
            for (int v = first; v < n; v++) if (got[v]) out.g[val[v]] = ch[v];
            if (hi >= 0 && hgot) out.g[hv] = hrec;
            vector<ll> o2; if (!out.order(o2)) return false;
            out.prune(o2);
            return true;
        };
        int curLen = ord.size();
        vector<int> cands;
        for (int i = first; i < n; i++) if ((ok[i / 64] >> (i % 64)) & 1) cands.push_back(i);
        shuffle(cands.begin(), cands.end(), rng);
        for (int x : cands) { VG out; if (rebuild({x}, -1, out) && out.length() < curLen && out.length() <= capLen) { G = out; stat_ko++; return true; } }
        if (!tryHelpers || mval.empty()) return false;
        // pass 1: count distinct outputs per helper
        int nh = mval.size();
        vector<int> hc(nh, 0), lastOut(nh, -1);
        auto scan = [&](auto&& emit) {
            for (int v = first; v < n; v++) {
                ll V = val[v];
                for (int f = 0; f < n; f++) {
                    if (f == v) continue; ll F = val[f];
                    ll c[6]; int code[6]; int m = 0;
                    if (V > F) { c[m] = V - F; code[m++] = OP_ADD | 4; }
                    if (F <= Pz.L - V) { c[m] = V + F; code[m++] = OP_SUB | 4; }
                    if (F > V) { c[m] = F - V; code[m++] = OP_SUB; }
                    if (F > 1 && V % F == 0) { c[m] = V / F; code[m++] = OP_MUL | 4; }
                    if (F > 1) { i128 p = (i128)V * F; if (p <= (i128)Pz.L) { c[m] = (ll)p; code[m++] = OP_DIV | 4; } }
                    if (F > V && F % V == 0) { c[m] = F / V; code[m++] = OP_DIV; }
                    for (int k = 0; k < m; k++) { int hi = M.get(c[k]); if (hi >= 0) emit(hi, v, f, code[k]); }
                }
                if (V % 2 == 0) { int hi = M.get(V / 2); if (hi >= 0) emit(hi, v, -1, OP_ADD | 4); }
                { ll r = (ll)sqrtl((long double)V); while (r * r > V) r--; while ((r + 1) * (r + 1) <= V) r++; if (r * r == V) { int hi = M.get(r); if (hi >= 0) emit(hi, v, -1, OP_MUL | 4); } }
            }
        };
        scan([&](int hi, int v, int f, int code) { if (lastOut[hi] != v) { hc[hi]++; lastOut[hi] = v; } });
        vector<int> keep; for (int h = 0; h < nh; h++) if (hc[h] >= 2) keep.push_back(h);
        if (keep.empty()) return false;
        vector<int> kidx(nh, -1); for (size_t q = 0; q < keep.size(); q++) kidx[keep[q]] = q;
        vector<int> kcnt(keep.size(), 0);
        scan([&](int hi, int v, int f, int code) { if (kidx[hi] >= 0) kcnt[kidx[hi]]++; });
        // remap helper indices: use helper id space = original hi but huoff indexed by original hi (sparse ok)
        huoff.assign(nh + 1, 0);
        { vector<int> cnt(nh, 0); for (size_t q = 0; q < keep.size(); q++) cnt[keep[q]] = kcnt[q]; for (int h = 0; h < nh; h++) huoff[h + 1] = huoff[h] + cnt[h]; }
        hulist.assign(huoff[nh], {0, 0, 0});
        { vector<int> fill = huoff; scan([&](int hi, int v, int f, int code) { if (kidx[hi] >= 0) hulist[fill[hi]++] = {v, f, code}; }); }
        shuffle(keep.begin(), keep.end(), rng);
        // consumer lists for incremental propagation: for operand u -> list of values v having a direct recipe using u
        vector<vector<int>> cons(n);
        for (int v = first; v < n; v++) for (int e = doff[v]; e < doff[v + 1]; e++) { cons[dlist[e][0]].push_back(v); if (dlist[e][1] != dlist[e][0]) cons[dlist[e][1]].push_back(v); }
        int tested = 0;
        vector<Bits> R(n); vector<int> dirty; vector<char> inq(n, 0);
        for (int hi : keep) {
            Bits hm{};
            { auto& e = mwit[hi]; for (int w = 0; w < words; w++) hm[w] = rows[e[0]][w] & rows[e[1]][w]; }
            // quick usefulness test
            bool useful = false;
            for (int e = huoff[hi]; e < huoff[hi + 1] && !useful; e++) { auto& u = hulist[e]; int v = u[0];
                for (int w = 0; w < words; w++) if (allow[v][w] & ~rows[v][w] & hm[w] & (u[1] >= 0 ? rows[u[1]][w] : ~0ULL)) { useful = true; break; } }
            if (!useful) continue;
            // incremental propagation from base rows
            vector<int> touched; vector<int> work;
            auto addbits = [&](int v, const Bits& g) {
                bool any = false;
                for (int w = 0; w < words; w++) { ull add = g[w] & allow[v][w] & ~R[v][w]; if (add) { if (!any && !inq[v]) {} any = true; R[v][w] |= add; } }
                if (any && !inq[v]) { inq[v] = 1; work.push_back(v); }
                return any;
            };
            // R starts as copy of rows only for touched entries: use copy-on-write via full copy (n small)
            R = rows;
            for (int e = huoff[hi]; e < huoff[hi + 1]; e++) { auto& u = hulist[e]; Bits g{}; for (int w = 0; w < words; w++) g[w] = hm[w] & (u[1] >= 0 ? R[u[1]][w] : ~0ULL); addbits(u[0], g); }
            while (!work.empty()) {
                int u = work.back(); work.pop_back(); inq[u] = 0;
                for (int v : cons[u]) { Bits g{}; for (int e = doff[v]; e < doff[v + 1]; e++) for (int w = 0; w < words; w++) g[w] |= R[dlist[e][0]][w] & R[dlist[e][1]][w]; addbits(v, g); }
                // helper uses whose 'other' operand is u
                for (int e = huoff[hi]; e < huoff[hi + 1]; e++) { auto& uu = hulist[e]; if (uu[1] == u) { Bits g{}; for (int w = 0; w < words; w++) g[w] = hm[w] & R[u][w]; addbits(uu[0], g); } }
            }
            Bits okh = sel;
            for (int t = first; t < n; t++) if (req[t]) for (int w = 0; w < words; w++) okh[w] &= R[t][w];
            vector<int> drops;
            for (int i = first; i < n; i++) if (((okh[i / 64] >> (i % 64)) & 1) && !((ok[i / 64] >> (i % 64)) & 1)) drops.push_back(i);
            if (drops.size() < 2) continue;
            if (++tested > 400) break;
            shuffle(drops.begin(), drops.end(), rng);
            for (size_t i = 0; i < drops.size() && i < 12; i++) for (size_t j = 0; j < i; j++) {
                VG out;
                if (rebuild({drops[i], drops[j]}, hi, out) && out.length() < curLen) { G = out; stat_kh++; return true; }
            }
        }
        return false;
    }


    // ---------------- deep knockout: two helpers (pairs of 1-step helpers, and 2-step helper chains) ----------------
    long long stat_pairs = 0;
    bool knockout2(VG& G, int maxHelpers, int maxPairs) {
        vector<ll> ord; if (!G.order(ord)) return false;
        G.prune(ord);
        vector<ll> val; { unordered_set<ll> s; for (ll x : G.starts) if (s.insert(x).second) val.push_back(x); }
        int first = val.size(); for (ll v : ord) val.push_back(v);
        int n = val.size(); if (n > 500) return false;
        HMap id; id.init(n * 4); for (int i = 0; i < n; i++) id.put(val[i], i);
        vector<char> req(n, 0); for (ll t : G.targets) { int i = id.get(t); if (i >= 0) req[i] = 1; }
        // helper candidates: 1-step values h (not existing) that are operands of a recipe for some existing value
        HMap M; M.init(n * n * 3 + 64); vector<ll> mval; vector<array<int, 3>> mwit;
        for (int i = 0; i < n; i++) for (int j = 0; j <= i; j++) for (int op = 0; op < 4; op++) for (int sw = 0; sw < 2; sw++) {
            if (sw && (op == OP_ADD || op == OP_MUL || i == j)) continue;
            ll a = val[i], b = val[j]; ll x = sw ? apply_op(op, b, a, Pz.L) : apply_op(op, a, b, Pz.L);
            if (!x || id.get(x) >= 0) continue;
            int ia = sw ? j : i, ib = sw ? i : j;
            if (M.put(x, (int)mval.size())) { mval.push_back(x); mwit.push_back({ia, ib, op}); }
        }
        // useful helpers: appear in inverse scan of existing values
        vector<int> useCnt(mval.size(), 0);
        for (int v = first; v < n; v++) for (int f = 0; f < n; f++) {
            if (f == v) continue; ll V = val[v], F = val[f]; ll c[6]; int m = 0;
            if (V > F) c[m++] = V - F; if (F <= Pz.L - V) c[m++] = V + F; if (F > V) c[m++] = F - V;
            if (F > 1 && V % F == 0) c[m++] = V / F; if (F > 1) { i128 p = (i128)V * F; if (p <= (i128)Pz.L) c[m++] = (ll)p; } if (F > V && F % V == 0) c[m++] = F / V;
            for (int k = 0; k < m; k++) { int hi = M.get(c[k]); if (hi >= 0) useCnt[hi]++; }
        }
        vector<int> helpers; for (size_t h = 0; h < mval.size(); h++) if (useCnt[h] >= 1) helpers.push_back(h);
        shuffle(helpers.begin(), helpers.end(), rng);
        if ((int)helpers.size() > maxHelpers) helpers.resize(maxHelpers);
        int curLen = ord.size();
        // generic closure over extended set: existing values + chosen helpers, all recipes recomputed among extended set
        auto tryset = [&](const vector<ll>& hv, VG& out) -> bool {
            int k = hv.size(); int N = n + k;
            vector<ll> ev = val; for (ll h : hv) ev.push_back(h);
            HMap eid; eid.init(N * 4); for (int i = 0; i < N; i++) if (eid.get(ev[i]) < 0) eid.put(ev[i], i);
            // recipes for every computed/helper value among extended set
            vector<vector<array<int, 3>>> rec(N);
            for (int i = 0; i < N; i++) for (int j = 0; j <= i; j++) {
                if (i < n && j < n) continue; // recipes among existing only are handled below via cache
                for (int op = 0; op < 4; op++) for (int sw = 0; sw < 2; sw++) {
                    if (sw && (op == OP_ADD || op == OP_MUL || i == j)) continue;
                    ll x = sw ? apply_op(op, ev[j], ev[i], Pz.L) : apply_op(op, ev[i], ev[j], Pz.L);
                    if (!x) continue; int t = eid.get(x); if (t < first) continue;
                    int ia = sw ? j : i, ib = sw ? i : j; if (t == ia || t == ib) continue;
                    rec[t].push_back({ia, ib, op});
                }
            }
            for (int t = first; t < n; t++) for (auto& r : base_rec[t]) rec[t].push_back(r);
            // helpers must be made from existing values or other helpers (covered above)
            // drop search: try each triple from candidates? Use closure with ban sets: find values whose removal keeps targets
            // greedy: repeatedly ban optional values while closure reaches all targets
            vector<char> banned(N, 0), seen(N, 0);
            auto close = [&]() { fill(seen.begin(), seen.end(), 0); for (int i = 0; i < first; i++) seen[i] = 1;
                bool pr = true; while (pr) { pr = false; for (int v = first; v < N; v++) if (!seen[v] && !banned[v]) for (auto& r : rec[v]) if (seen[r[0]] && seen[r[1]]) { seen[v] = 1; pr = true; break; } }
                for (int t = first; t < n; t++) if (req[t] && !seen[t]) return false; return true; };
            vector<int> opt; for (int i = first; i < N; i++) if (i >= n || !req[i]) opt.push_back(i);
            for (int rep = 0; rep < 3; rep++) {
                shuffle(opt.begin(), opt.end(), rng); fill(banned.begin(), banned.end(), 0);
                for (int i : opt) { banned[i] = 1; if (!close()) banned[i] = 0; }
                if (!close()) continue;
                int used = 0; for (int i = first; i < N; i++) if (seen[i]) used++;
                if (used < curLen) {
                    // construct graph
                    VG T = G; T.g.clear(); for (ll s : G.starts) T.g[s] = {-1, 0, 0};
                    // pick recipes in derivation order
                    vector<char> got(N, 0); for (int i = 0; i < first; i++) got[i] = 1;
                    bool pr = true; while (pr) { pr = false; for (int v = first; v < N; v++) if (seen[v] && !got[v]) for (auto& r : rec[v]) if (got[r[0]] && got[r[1]] && seen[r[0]] && seen[r[1]]) { got[v] = 1; T.g[ev[v]] = {r[2], ev[r[0]], ev[r[1]]}; pr = true; break; } }
                    vector<ll> o; if (!T.order(o)) continue;
                    if ((int)o.size() < curLen) { T.prune(o); out = T; return true; }
                }
            }
            return false;
        };
        // base recipes among existing values
        base_rec.assign(n, {});
        for (int i = 0; i < n; i++) for (int j = 0; j <= i; j++) for (int op = 0; op < 4; op++) for (int sw = 0; sw < 2; sw++) {
            if (sw && (op == OP_ADD || op == OP_MUL || i == j)) continue;
            ll x = sw ? apply_op(op, val[j], val[i], Pz.L) : apply_op(op, val[i], val[j], Pz.L);
            if (!x) continue; int t = id.get(x); if (t < first) continue; int ia = sw ? j : i, ib = sw ? i : j; if (t == ia || t == ib) continue;
            base_rec[t].push_back({ia, ib, op});
        }
        int tested = 0;
        for (size_t a = 0; a < helpers.size() && tested < maxPairs; a++) for (size_t b = 0; b < a && tested < maxPairs; b++) {
            tested++; stat_pairs++;
            VG out; if (tryset({mval[helpers[a]], mval[helpers[b]]}, out)) { G = out; return true; }
        }
        return false;
    }
    vector<vector<array<int, 3>>> base_rec;
    // ---------------- perturbation (own design) ----------------
    // One-step recipe table over all existing values: value -> up to 6 recipes (operands existing).
    struct Lookup {
        HMap h; vector<ll> keys; vector<array<Rec, 6>> recs; vector<int> cnt;
        void reset(size_t n) { h.init(max<size_t>(64, 3 * n * n)); keys.clear(); recs.clear(); cnt.clear(); }
        void push(ll v, Rec r, mt19937_64& R) {
            int k = h.get(v);
            if (k < 0) { k = keys.size(); h.put(v, k); keys.push_back(v); recs.push_back({}); cnt.push_back(0); }
            int c = cnt[k]++;
            if (c < 6) recs[k][c] = r; else { int j = R() % (c + 1); if (j < 6) recs[k][j] = r; }
        }
        bool sample(ll v, mt19937_64& R, Rec& out) const {
            int k = h.get(v); if (k < 0) return false;
            int c = min(cnt[k], 6); out = recs[k][R() % c]; return true;
        }
    } lookup;

    void build_lookup(const VG& G, const vector<ll>& nums) {
        lookup.reset(nums.size());
        for (size_t i = 0; i < nums.size(); i++) for (size_t j = 0; j <= i; j++) {
            ll a = max(nums[i], nums[j]), b = min(nums[i], nums[j]);
            for (int op = 0; op < 4; op++) {
                ll v = apply_op(op, a, b, Pz.L);
                if (v && v != a && v != b && !G.g.count(v)) lookup.push(v, {op, a, b}, rng);
            }
        }
    }

    // inverse steps of v with partner F: returns (need, recipe for v)
    int inv_steps(ll v, ll F, pair<ll, Rec>* out) {
        int m = 0;
        if (v > F) out[m++] = {v - F, Rec{OP_ADD, v - F, F}};
        if (F <= Pz.L - v) out[m++] = {v + F, Rec{OP_SUB, v + F, F}};
        if (F > v) out[m++] = {F - v, Rec{OP_SUB, F, F - v}};
        if (F > 1 && v % F == 0) out[m++] = {v / F, Rec{OP_MUL, v / F, F}};
        if (F > 1) { i128 p = (i128)v * F; if (p <= (i128)Pz.L) out[m++] = {(ll)p, Rec{OP_DIV, (ll)p, F}}; }
        if (F > v && F % v == 0) out[m++] = {F / v, Rec{OP_DIV, F, F / v}};
        return m;
    }

    bool perturb(VG& G, int cap, int wanted) {
        vector<ll> ord; if (!G.order(ord)) return false;
        G.prune(ord);
        vector<ll> nums = G.starts; nums.insert(nums.end(), ord.begin(), ord.end());
        shuffle(nums.begin(), nums.end(), rng);
        build_lookup(G, nums);
        unordered_map<ll, int> used;
        auto refresh = [&]() { used.clear(); for (ll t : G.targets) used[t]++; for (auto& [v, r] : G.g) if (r.op >= 0) { used[r.a]++; if (r.a != r.b) used[r.b]++; } };
        refresh();
        shuffle(ord.begin(), ord.end(), rng);
        int swaps = 0; int curLen = ord.size();
        for (ll v : ord) {
            auto itv = G.g.find(v); if (itv == G.g.end() || itv->second.op < 0) continue;
            Rec old = itv->second;
            auto isComp = [&](ll x) { auto it = G.g.find(x); return it != G.g.end() && it->second.op >= 0; };
            bool privA = isComp(old.a) && used[old.a] == 1, privB = isComp(old.b) && used[old.b] == 1;
            bool has_private = privA || privB;
            auto replace = [&](Rec step, ll extra, Rec build) {
                if (step.a == v || step.b == v) return false;
                if (extra) { if (extra == v || G.g.count(extra) || !G.g.count(build.a) || !G.g.count(build.b)) return false; G.g[extra] = build; }
                G.g[v] = step;
                vector<ll> live;
                bool valid = G.order(live) && (int)live.size() <= cap;
                if (valid) { G.prune(live); curLen = live.size(); }
                else { G.g[v] = old; if (extra) G.g.erase(extra); }
                return valid;
            };
            bool changed = false; int attempts = 0;
            size_t shift = rng() % nums.size();
            pair<ll, Rec> st[6];
            for (size_t j = 0; j < nums.size() && !changed; j++) {
                ll F = nums[(shift + j) % nums.size()];
                if (F == v || !G.g.count(F)) continue;
                int m = inv_steps(v, F, st);
                for (int q = 0; q < m && !changed; q++) {
                    ll need = st[q].first; Rec step = st[q].second;
                    if (need == v) continue;
                    if (step.op == old.op && ((step.a == old.a && step.b == old.b) || ((step.op == OP_ADD || step.op == OP_MUL) && step.a == old.b && step.b == old.a))) continue;
                    if (G.g.count(need)) { if (rng() % 4 == 0 && replace(step, 0, {})) changed = true; }
                    else if (has_private || cap > curLen) {
                        Rec r; if (!lookup.sample(need, rng, r)) continue;
                        if (r.a == v || r.b == v) continue;
                        if (cap <= curLen) {
                            bool losesA = privA && r.a != old.a && r.b != old.a && F != old.a;
                            bool losesB = privB && r.a != old.b && r.b != old.b && F != old.b;
                            if (!losesA && !losesB) continue;
                        }
                        if (replace(step, need, r)) changed = true;
                        else if (++attempts >= 12) break;
                    }
                }
                if (attempts >= 12) break;
            }
            if (changed) { if (++swaps >= wanted) break; refresh(); }
        }
        return swaps > 0;
    }

    // exact cone rebuild: for a random computed value v whose private cone has >=3 values, find a chain of <=2 fresh values
    bool rotate(VG& G, int cap) {
        vector<ll> ord; if (!G.order(ord)) return false;
        G.prune(ord);
        unordered_map<ll, int> used; for (ll t : G.targets) used[t]++;
        for (auto& [v, r] : G.g) if (r.op >= 0) { used[r.a]++; if (r.a != r.b) used[r.b]++; }
        vector<ll> roots = ord; shuffle(roots.begin(), roots.end(), rng);
        int scanned = 0;
        for (ll v : roots) {
            // private cone of v
            unordered_set<ll> cut{v}; vector<ll> stck;
            Rec rv = G.g.at(v); stck.push_back(rv.a); if (rv.b != rv.a) stck.push_back(rv.b);
            unordered_map<ll, int> u2 = used;
            while (!stck.empty()) { ll x = stck.back(); stck.pop_back(); auto it = G.g.find(x); if (it == G.g.end() || it->second.op < 0) continue;
                if (--u2[x] > 0) continue; if (cut.count(x)) continue; cut.insert(x); stck.push_back(it->second.a); if (it->second.b != it->second.a) stck.push_back(it->second.b); }
            if ((int)cut.size() < 3) continue;
            if (++scanned > 6) break;
            // banned = cut + anything depending on cut (except v's consumers, which keep using v)
            unordered_set<ll> banned = cut;
            for (ll x : ord) { const Rec& r = G.g.at(x); if (x != v && (banned.count(r.a) || banned.count(r.b))) banned.insert(x); }
            vector<ll> fixed; for (ll s : G.starts) fixed.push_back(s); for (ll x : ord) if (!banned.count(x)) fixed.push_back(x);
            if (fixed.size() < 2) continue;
            // pool + R1 from fixed values
            Pool pool; pool.init(Pz.L); for (ll x : fixed) pool.add(x);
            Searcher S; S.P = &pool; S.L = Pz.L;
            int budget = min((int)cut.size() - 1, 3);
            int c = S.search(v, budget, 1);
            if (c < 0 || c >= (int)cut.size()) continue;
            // apply: remove cut, add chain
            VG H = G;
            for (ll x : cut) H.g.erase(x);
            vector<ll> chainVals(S.best.size());
            for (size_t j = 0; j < S.best.size(); j++) {
                const CNode& cn = S.best[j];
                ll a = cn.a >= 0 ? pool.vals[cn.a] : chainVals[-1 - cn.a];
                ll b = cn.b >= 0 ? pool.vals[cn.b] : chainVals[-1 - cn.b];
                chainVals[j] = cn.v;
                if (!H.g.count(cn.v) || cn.v == v) H.g[cn.v] = {cn.op, a, b};
            }
            vector<ll> live;
            if (H.order(live) && (int)live.size() <= cap && (int)live.size() < (int)ord.size() + 1) { H.prune(live); G = H; stat_rot++; return true; }
        }
        return false;
    }


    // ---------------- recombination: union of values, greedy minimal derivable subset (own implementation) ----------------
    bool crossover(const VG& base, const vector<VG>& archive, VG& out) {
        vector<ll> vals; HMap ids; ids.init(4096);
        { for (ll s : base.starts) if (ids.get(s) < 0) { ids.put(s, vals.size()); vals.push_back(s); } }
        int initial = vals.size();
        auto append = [&](const VG& G) { vector<ll> o; if (!G.order(o)) return; for (ll x : o) if (ids.get(x) < 0) { ids.put(x, vals.size()); vals.push_back(x); } };
        append(base); int orig = vals.size();
        for (auto& G : archive) append(G);
        int n = vals.size(); if (n > 2000) return false;
        vector<vector<array<int, 3>>> rec(n);
        for (int i = initial; i < n; i++) {
            ll v = vals[i];
            auto it = base.g.find(v); if (it != base.g.end() && it->second.op >= 0) rec[i].push_back({ids.get(it->second.a), ids.get(it->second.b), it->second.op});
        }
        for (int i = 0; i < n; i++) for (int j = 0; j <= i; j++) {
            int a = vals[i] >= vals[j] ? i : j, b = i + j - a;
            for (int op = 0; op < 4; op++) {
                ll x = apply_op(op, vals[a], vals[b], Pz.L); if (!x || x == vals[a] || x == vals[b]) continue;
                int k = ids.get(x); if (k >= initial) rec[k].push_back({a, b, op});
            }
        }
        vector<char> needed(n, 0); int goal = 0;
        for (ll t : base.targets) { int k = ids.get(t); if (k >= initial && !needed[k]) { needed[k] = 1; goal++; } }
        vector<int> support(n, 0); for (auto& G : archive) for (auto& [v, r] : G.g) { int k = ids.get(v); if (k >= 0) support[k]++; }
        vector<char> banned(n, 0), seen(n, 0); vector<int> pick(n, -1);
        auto close = [&]() {
            int remaining = goal; fill(seen.begin(), seen.end(), 0); fill(seen.begin(), seen.begin() + initial, 1);
            bool progress = true;
            while (progress && remaining) { progress = false;
                for (int v = initial; v < n; v++) if (!seen[v] && !banned[v]) for (size_t j = 0; j < rec[v].size(); j++) {
                    auto& r = rec[v][j]; if (!seen[r[0]] || !seen[r[1]]) continue; seen[v] = 1; pick[v] = j; remaining -= needed[v]; progress = true; break; } }
            return remaining == 0;
        };
        vector<int> optional; for (int i = initial; i < n; i++) if (!needed[i]) optional.push_back(i);
        int baseLen = orig - initial;
        for (int attempt = 0; attempt < 7; attempt++) {
            vector<pair<double, int>> rank;
            for (int i : optional) { double x = (double)(rng() % 1000000) / 1e6; if (attempt % 3 != 0) x += (attempt % 3 == 1 ? 0.22 : 0.09) * support[i]; rank.push_back({x, i}); }
            sort(rank.begin(), rank.end());
            fill(banned.begin(), banned.end(), 0);
            for (auto [p, i] : rank) { banned[i] = 1; if (!close()) banned[i] = 0; }
            if (!close()) continue;
            VG T = base; T.g.clear();
            for (ll s : base.starts) T.g[s] = {-1, 0, 0};
            for (int i = initial; i < n; i++) if (seen[i]) { auto& r = rec[i][pick[i]]; T.g[vals[i]] = {r[2], vals[r[0]], vals[r[1]]}; }
            vector<ll> o; if (!T.order(o)) continue;
            if ((int)o.size() < baseLen) { T.prune(o); out = T; return true; }
        }
        return false;
    }
    vector<VG> seeds;
    void run(double secs, int slackMax) {
        auto t0 = chrono::steady_clock::now();
        VG trial = champ; vector<VG> pool = seeds;
        if (!seeds.empty()) {   // immediate recombination with seed variants
            VG better;
            if (crossover(champ, pool, better)) { vector<array<int, 4>> prog; if (compile(better, prog) && (int)prog.size() < bestLen) { bestLen = prog.size(); bestProg = prog; champ = better; best = better; trial = better; stat_cross++; } }
        }
        long turn = 0;
        int kick = getenv("SA_KICK") ? atoi(getenv("SA_KICK")) : 0;      // basin hopping: kick size
        int coolEvery = getenv("SA_COOL") ? atoi(getenv("SA_COOL")) : 25; // turns per cap decrement after a kick
        int extra = 0; long lastKick = 0;
        int regcap = getenv("SA_REGCAP") ? atoi(getenv("SA_REGCAP")) : -1;
        while (chrono::duration<double>(chrono::steady_clock::now() - t0).count() < secs) {
            turn++;
            if (kick > 0 && extra == 0 && turn - lastKick > 300) {
                // kick: random re-routing of the champion (or a pool member) up to +kick instructions
                trial = (!pool.empty() && rng() % 2) ? pool[rng() % pool.size()] : champ;
                perturb(trial, bestLen + kick, kick * 3);
                extra = max(0, trial.length() - bestLen); lastKick = turn;
            }
            if (extra > 0 && (turn - lastKick) % coolEvery == 0) extra--;
            if (extra == 0) {
                if (turn % 9 == 0) trial = champ;
                else if (turn % 9 == 5 && !pool.empty()) trial = pool[rng() % pool.size()];
                else if (turn % 9 == 7 && !seeds.empty()) trial = seeds[rng() % seeds.size()];
            }
            int slack = extra > 0 ? extra : ((turn % 9 == 1 || turn % 9 == 2) ? slackMax : (turn % 9 <= 5 ? 1 : 0));
            int cap = bestLen + slack;
            perturb(trial, cap, 3 + rng() % 8);
            rotate(trial, cap);
            for (int r = 0; r < 4; r++) if (!knockout(trial, true, cap)) break;
            int len = trial.length();
            if (getenv("SA_DEBUG") && turn < 400) fprintf(stderr, "turn %ld slack %d len %d best %d\n", turn, slack, len, bestLen);
            if (len < bestLen) {
                vector<array<int, 4>> prog;
                bool okc = compile(trial, prog);
                if (okc && (int)prog.size() < bestLen) { bestLen = prog.size(); bestProg = prog; champ = trial; best = trial; }
                else { stat_cfail++;
                    if (getenv("SA_DUMPFAIL")) { vector<Node> nd; trial.to_nodes(nd); FILE* df = fopen(getenv("SA_DUMPFAIL"), "a");
                        if (df) { fprintf(df, "D %s %zu", Pz.id.c_str(), nd.size()); for (auto& x : nd) fprintf(df, " %lld %d %d %d", x.v, x.op, x.a, x.b); fprintf(df, "\n"); fclose(df); } }
                    if (getenv("SA_DEBUG")) { vector<Node> nd; trial.to_nodes(nd); fprintf(stderr, "  compile fail: len %d maxlive %d okc %d\n", len, max_live(nd), (int)okc); } trial = champ; }
            }
            if (regcap >= 0 && len <= bestLen + slackMax) {   // register-aware steering: stay where a 48-register schedule is plausible
                vector<Node> nd; int pk = 0;
                if (trial.to_nodes(nd)) pk = min(max_live(nd), max_live(reschedule(nd)));
                if (pk > Pz.nreg + regcap) { stat_regrej++; trial = champ; continue; }
            }
            if (len <= bestLen + 1) { pool.push_back(trial); if (pool.size() > 12) pool.erase(pool.begin() + rng() % 5); }
            if (turn % 5 == 4 && pool.size() >= 4) {
                VG better;
                if (crossover(champ, pool, better)) {
                    vector<array<int, 4>> prog;
                    if (compile(better, prog) && (int)prog.size() < bestLen) { bestLen = prog.size(); bestProg = prog; champ = better; best = better; trial = better; stat_cross++; }
                }
            }
            if (len > cap && extra == 0) trial = champ;
        }
    }
};

int main(int argc, char** argv) {
    // sa bank out secs worker nworkers [idsfile] [slack]
    string bank = argv[1], outp = argv[2]; double secs = atof(argv[3]); int w = atoi(argv[4]), nw = atoi(argv[5]);
    set<string> only; if (argc > 6 && string(argv[6]) != "-") { ifstream f(argv[6]); string s; while (f >> s) only.insert(s); }
    int slack = argc > 7 ? atoi(argv[7]) : 2;
    rng.seed(777 + 1000 * w + time(nullptr));
    auto puzzles = read_bank(bank);
    map<string, vector<vector<array<int, 4>>>> variants;
    if (getenv("SA_VARIANTS")) { ifstream f(getenv("SA_VARIANTS")); string tag; while (f >> tag) { string pid; int n; f >> pid >> n; vector<array<int, 4>> pr(n); for (auto& x : pr) f >> x[0] >> x[1] >> x[2] >> x[3]; variants[pid].push_back(pr); } }
    FILE* fo = fopen(outp.c_str(), "a"); int total = 0, idx = 0;
    for (auto& Pz : puzzles) {
        if (!only.empty() && !only.count(Pz.id)) continue;
        if ((idx++ % nw) != w) continue;
        { unsigned long long s0 = getenv("SA_SEED") ? strtoull(getenv("SA_SEED"), nullptr, 10) : 1ULL;
          rng.seed(s0 * 0x9E3779B97F4A7C15ULL ^ std::hash<string>{}(Pz.id)); }  // per-puzzle stream: order-independent, varies by SA_SEED
        Annealer A; A.Pz = Pz;
        A.champ.L = Pz.L; A.champ.nreg = Pz.nreg; A.champ.starts = Pz.starts; A.champ.targets = Pz.targets;
        { vector<ll> regs(Pz.nreg, 0); for (size_t i = 0; i < Pz.starts.size(); i++) { regs[i] = Pz.starts[i]; A.champ.g[Pz.starts[i]] = {-1, 0, 0}; }
          for (auto& ins : Pz.prog) { ll a = regs[ins[1]], b = regs[ins[2]]; ll v = apply_op(ins[0], a, b, Pz.L); regs[ins[3]] = v; if (!A.champ.g.count(v)) A.champ.g[v] = {ins[0], a, b}; } }
        { vector<ll> o; A.champ.order(o); A.champ.prune(o); }
        A.best = A.champ; A.bestLen = Pz.prog.size(); A.bestProg = Pz.prog;
        for (auto& pr : variants[Pz.id]) {
            VG V; V.L = Pz.L; V.nreg = Pz.nreg; V.starts = Pz.starts; V.targets = Pz.targets;
            vector<ll> regs(Pz.nreg, 0); for (size_t i = 0; i < Pz.starts.size(); i++) { regs[i] = Pz.starts[i]; V.g[Pz.starts[i]] = {-1, 0, 0}; }
            bool okv = true;
            for (auto& ins : pr) { ll a = regs[ins[1]], b = regs[ins[2]]; ll v = apply_op(ins[0], a, b, Pz.L); if (!v) { okv = false; break; } regs[ins[3]] = v; if (!V.g.count(v)) V.g[v] = {ins[0], a, b}; }
            vector<ll> o; if (okv && V.order(o)) { V.prune(o); A.seeds.push_back(V); }
        }
        if (getenv("SA_INFLATE")) {
            int K = atoi(getenv("SA_INFLATE")); int target = A.bestLen + K;
            for (int t = 0; t < 200 && A.champ.length() < target; t++) A.perturb(A.champ, target, 1);
            vector<array<int,4>> pr; if (A.compile(A.champ, pr)) { A.bestLen = pr.size(); A.bestProg = pr; A.best = A.champ; }
            fprintf(stderr, "%s inflated %zu -> %d\n", Pz.id.c_str(), Pz.prog.size(), A.bestLen);
        }
        int start = A.bestLen;
        if (getenv("SA_DKO")) {
            VG G2 = A.champ; auto t0 = chrono::steady_clock::now();
            while (chrono::duration<double>(chrono::steady_clock::now() - t0).count() < secs) {
                if (!A.knockout2(G2, atoi(getenv("SA_DKO")), 20000)) break;
                vector<array<int,4>> pr; if (A.compile(G2, pr) && (int)pr.size() < A.bestLen) { A.bestLen = pr.size(); A.bestProg = pr; A.champ = G2; fprintf(stderr, "  dko improved %s -> %d\n", Pz.id.c_str(), A.bestLen); }
                else break;
            }
            fprintf(stderr, "%s dko pairs tested %lld\n", Pz.id.c_str(), A.stat_pairs);
        } else
        A.run(secs, slack);
        if (A.bestLen < start) {
            fprintf(fo, "R %s %zu", Pz.id.c_str(), A.bestProg.size()); for (auto& x : A.bestProg) fprintf(fo, " %d %d %d %d", x[0], x[1], x[2], x[3]); fprintf(fo, "\n"); fflush(fo);
            total += start - A.bestLen;
        }
        printf("%s start=%d best=%d ko=%lld kh=%lld rot=%lld cfail=%lld cross=%lld total=%d cfix=%lld regrej=%lld\n", Pz.id.c_str(), start, A.bestLen, A.stat_ko, A.stat_kh, A.stat_rot, A.stat_cfail, A.stat_cross, total, A.stat_cfix, A.stat_regrej); fflush(stdout);
    }
}
