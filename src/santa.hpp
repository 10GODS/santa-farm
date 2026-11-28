// Santa 2026 engine: core data structures, MITM chain search, scheduling.
#pragma once
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef unsigned long long ull;
typedef __int128 i128;

static inline ull mix64(ull x) {
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27; x *= 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

// open-addressing hash map ll -> int (key 0 = empty; all values >= 1)
struct HMap {
    vector<ll> keys; vector<int> vals; ull mask = 0; int cnt = 0;
    void init(int cap) {
        int c = 16; while (c < cap * 2) c <<= 1;
        keys.assign(c, 0); vals.assign(c, -1); mask = c - 1; cnt = 0;
    }
    void clear() { std::fill(keys.begin(), keys.end(), 0); cnt = 0; }
    inline int get(ll k) const {
        ull h = mix64((ull)k) & mask;
        while (true) {
            ll kk = keys[h];
            if (kk == k) return vals[h];
            if (kk == 0) return -1;
            h = (h + 1) & mask;
        }
    }
    inline bool contains(ll k) const { return get(k) >= 0; }
    // insert if absent; returns true if inserted
    inline bool put(ll k, int v) {
        if ((ull)(cnt + 1) * 2 > mask + 1) grow();
        ull h = mix64((ull)k) & mask;
        while (true) {
            ll kk = keys[h];
            if (kk == k) return false;
            if (kk == 0) { keys[h] = k; vals[h] = v; cnt++; return true; }
            h = (h + 1) & mask;
        }
    }
    void grow() {
        vector<ll> ok = keys; vector<int> ov = vals;
        int c = (int)(mask + 1) * 2;
        keys.assign(c, 0); vals.assign(c, -1); mask = c - 1; cnt = 0;
        for (size_t i = 0; i < ok.size(); i++) if (ok[i]) put(ok[i], ov[i]);
    }
};

enum { OP_ADD = 0, OP_SUB = 1, OP_MUL = 2, OP_DIV = 3 };
static const char OPCH[4] = {'+', '-', '*', '/'};

// apply op, return 0 if invalid (out of range / inexact / non-positive)
static inline ll apply_op(int op, ll a, ll b, ll L) {
    switch (op) {
        case OP_ADD: { ll v = a + b; return (v >= 1 && v <= L) ? v : 0; }
        case OP_SUB: { ll v = a - b; return (v >= 1 && v <= L) ? v : 0; }
        case OP_MUL: { i128 v = (i128)a * b; return (v >= 1 && v <= (i128)L) ? (ll)v : 0; }
        case OP_DIV: { if (b == 0 || a % b) return 0; ll v = a / b; return (v >= 1 && v <= L) ? v : 0; }
    }
    return 0;
}

struct Puzzle {
    string id; ll L; int nreg;
    vector<ll> starts, targets;
    vector<array<int, 4>> prog; // op i j d
};

// A node in a value DAG.  a,b index into the node vector (or -1 for starts).
struct Node { ll v; int op; int a, b; };

// Parse the bank file.
static vector<Puzzle> read_bank(const string& path) {
    vector<Puzzle> out; ifstream f(path); string tag;
    Puzzle cur; bool have = false;
    while (f >> tag) {
        if (tag == "P") { if (have) out.push_back(cur); cur = Puzzle(); have = true; f >> cur.id >> cur.L >> cur.nreg; }
        else if (tag == "S") { int n; f >> n; cur.starts.resize(n); for (auto& x : cur.starts) f >> x; }
        else if (tag == "T") { int n; f >> n; cur.targets.resize(n); for (auto& x : cur.targets) f >> x; }
        else if (tag == "G") { int n; f >> n; cur.prog.resize(n); for (auto& x : cur.prog) f >> x[0] >> x[1] >> x[2] >> x[3]; }
    }
    if (have) out.push_back(cur);
    return out;
}

// Verify a register program under official rules; returns length or -1.
static int verify_prog(const Puzzle& P, const vector<array<int, 4>>& prog, string* err = nullptr) {
    vector<ll> regs(P.nreg, 0); vector<char> def(P.nreg, 0);
    for (size_t i = 0; i < P.starts.size(); i++) { regs[i] = P.starts[i]; def[i] = 1; }
    unordered_set<ll> need(P.targets.begin(), P.targets.end());
    for (ll s : P.starts) need.erase(s);
    if (prog.size() > 4096) { if (err) *err = "too long"; return -1; }
    for (size_t k = 0; k < prog.size(); k++) {
        auto [op, i, j, d] = prog[k];
        if (i < 0 || j < 0 || d < 0 || i >= P.nreg || j >= P.nreg || d >= P.nreg) { if (err) *err = "reg range"; return -1; }
        if (!def[i] || !def[j]) { if (err) *err = "undef reg at " + to_string(k); return -1; }
        ll v = apply_op(op, regs[i], regs[j], P.L);
        if (v == 0) { if (err) *err = "bad op at " + to_string(k); return -1; }
        regs[d] = v; def[d] = 1; need.erase(v);
    }
    if (!need.empty()) { if (err) *err = "missing targets " + to_string(need.size()); return -1; }
    return (int)prog.size();
}

// Convert register program to node list: starts first (a=b=-1), then one node per *useful* instruction,
// deduplicating repeated values and dropping dead code.
static vector<Node> prog_to_nodes(const Puzzle& P, const vector<array<int, 4>>& prog) {
    vector<Node> nodes; unordered_map<ll, int> idx;
    vector<int> reg(P.nreg, -1);
    for (size_t i = 0; i < P.starts.size(); i++) {
        ll s = P.starts[i];
        auto it = idx.find(s);
        if (it == idx.end()) { idx[s] = nodes.size(); reg[i] = nodes.size(); nodes.push_back({s, -1, -1, -1}); }
        else reg[i] = it->second;
    }
    for (auto& ins : prog) {
        auto [op, i, j, d] = ins;
        int a = reg[i], b = reg[j];
        ll v = apply_op(op, nodes[a].v, nodes[b].v, P.L);
        auto it = idx.find(v);
        if (it != idx.end()) { reg[d] = it->second; continue; }
        idx[v] = nodes.size(); reg[d] = nodes.size(); nodes.push_back({v, op, a, b});
    }
    // dead code elimination: keep nodes in cones of targets
    int n = nodes.size(); vector<char> keep(n, 0);
    unordered_set<ll> T(P.targets.begin(), P.targets.end());
    vector<int> st;
    for (int k = 0; k < n; k++) if (T.count(nodes[k].v)) st.push_back(k);
    while (!st.empty()) {
        int k = st.back(); st.pop_back();
        if (keep[k]) continue; keep[k] = 1;
        if (nodes[k].op >= 0) { st.push_back(nodes[k].a); st.push_back(nodes[k].b); }
    }
    vector<int> remap(n, -1); vector<Node> out;
    for (int k = 0; k < n; k++) {
        if (nodes[k].op < 0 || keep[k]) {
            Node x = nodes[k];
            if (x.op >= 0) { x.a = remap[x.a]; x.b = remap[x.b]; }
            remap[k] = out.size(); out.push_back(x);
        }
    }
    return out;
}

// Register allocation for a node list in the given (topological) order.
// starts occupy registers 0..s-1 (by position in P.starts). Returns empty on failure (>nreg live).
static bool nodes_to_prog(const Puzzle& P, const vector<Node>& nodes, vector<array<int, 4>>& prog) {
    int n = nodes.size(); prog.clear();
    vector<int> last(n, -1);
    for (int k = 0; k < n; k++) if (nodes[k].op >= 0) { last[nodes[k].a] = k; last[nodes[k].b] = k; }
    vector<int> regof(n, -1);
    vector<char> busy(P.nreg, 0);
    // map start values to their registers
    int ns = 0;
    for (int k = 0; k < n; k++) if (nodes[k].op < 0) ns++;
    for (int k = 0; k < n; k++) if (nodes[k].op < 0) {
        // find the register index of this start value
        int r = -1;
        for (size_t i = 0; i < P.starts.size(); i++) if (P.starts[i] == nodes[k].v) { r = i; break; }
        regof[k] = r; if (last[k] >= 0) busy[r] = 1;
    }
    for (int k = 0; k < n; k++) {
        const Node& x = nodes[k];
        if (x.op < 0) continue;
        int ra = regof[x.a], rb = regof[x.b];
        // free operands whose last use is k
        if (last[x.a] == k) busy[ra] = 0;
        if (last[x.b] == k) busy[rb] = 0;
        int d = -1;
        for (int r = 0; r < P.nreg; r++) if (!busy[r]) { d = r; break; }
        if (d < 0) return false;
        prog.push_back({x.op, ra, rb, d});
        regof[k] = d;
        if (last[k] > k) busy[d] = 1;
    }
    return true;
}

// max live values for an order (for diagnostics)
static int max_live(const vector<Node>& nodes) {
    int n = nodes.size(); vector<int> last(n, -1);
    for (int k = 0; k < n; k++) if (nodes[k].op >= 0) { last[nodes[k].a] = k; last[nodes[k].b] = k; }
    int live = 0, mx = 0;
    vector<int> endc(n + 1, 0);
    for (int k = 0; k < n; k++) if (nodes[k].op < 0 && last[k] >= 0) { live++; endc[last[k]]++; }
    mx = live;
    for (int k = 0; k < n; k++) {
        if (nodes[k].op < 0) continue;
        live -= endc[k];
        live += 1; mx = max(mx, live);
        if (last[k] > k) endc[last[k]]++; else live -= 1;
    }
    return mx;
}

// Reorder nodes to reduce register pressure: greedy list scheduling.
static vector<Node> reschedule(const vector<Node>& nodes) {
    int n = nodes.size();
    vector<vector<int>> users(n); vector<int> indeg(n, 0);
    for (int k = 0; k < n; k++) if (nodes[k].op >= 0) {
        users[nodes[k].a].push_back(k); if (nodes[k].b != nodes[k].a) users[nodes[k].b].push_back(k);
        indeg[k] = (nodes[k].a == nodes[k].b) ? 1 : 2;
    }
    vector<int> remaining_uses(n); for (int k = 0; k < n; k++) remaining_uses[k] = users[k].size();
    vector<int> order; vector<char> done(n, 0);
    set<int> ready;
    for (int k = 0; k < n; k++) if (nodes[k].op < 0) { order.push_back(k); done[k] = 1; }
    for (int k = 0; k < n; k++) if (nodes[k].op < 0) for (int u : users[k]) if (--indeg[u] == 0) ready.insert(u);
    while (!ready.empty()) {
        // pick node that frees most registers (operands with remaining_uses==1), tie: smallest original index
        int best = -1, bscore = INT_MIN;
        for (int u : ready) {
            int fr = 0;
            if (remaining_uses[nodes[u].a] == 1) fr++;
            if (nodes[u].b != nodes[u].a && remaining_uses[nodes[u].b] == 1) fr++;
            int score = fr * 100000 - u;
            if (score > bscore) { bscore = score; best = u; }
        }
        ready.erase(best); order.push_back(best); done[best] = 1;
        remaining_uses[nodes[best].a]--; if (nodes[best].b != nodes[best].a) remaining_uses[nodes[best].b]--;
        for (int u : users[best]) if (--indeg[u] == 0) ready.insert(u);
    }
    vector<int> pos(n); for (int i = 0; i < n; i++) pos[order[i]] = i;
    vector<Node> out(n);
    for (int i = 0; i < n; i++) { Node x = nodes[order[i]]; if (x.op >= 0) { x.a = pos[x.a]; x.b = pos[x.b]; } out[i] = x; }
    return out;
}

// Randomized register-pressure list scheduling (fallback when the greedy orders need more than nreg registers).
// Each trial builds a topological order step by step, only taking instructions whose peak (live values after freeing
// operands at their last use, plus the new value) fits in nreg; priority = registers freed, then users it makes ready
// that free registers themselves, plus noise that grows with the trial index. Returns true with a verified-length program.
static bool schedule_fit(const Puzzle& P, const vector<Node>& nodes, vector<array<int, 4>>& prog, int trials, unsigned long long seed) {
    int n = nodes.size(); vector<vector<int>> users(n); vector<int> indeg0(n, 0);
    for (int k = 0; k < n; k++) if (nodes[k].op >= 0) {
        users[nodes[k].a].push_back(k); if (nodes[k].b != nodes[k].a) users[nodes[k].b].push_back(k);
        indeg0[k] = (nodes[k].a == nodes[k].b) ? 1 : 2;
    }
    mt19937_64 R(seed);
    vector<int> rem(n), indeg(n), order; order.reserve(n); vector<char> done(n);
    for (int t = 0; t < trials; t++) {
        for (int k = 0; k < n; k++) { rem[k] = users[k].size(); indeg[k] = indeg0[k]; done[k] = 0; }
        order.clear(); int live = 0; vector<int> ready;
        for (int k = 0; k < n; k++) if (nodes[k].op < 0) { order.push_back(k); done[k] = 1; if (rem[k] > 0) live++; }
        for (int k = 0; k < n; k++) if (nodes[k].op < 0) for (int u : users[k]) if (--indeg[u] == 0) ready.push_back(u);
        double noise = 0.05 + 3.0 * t / max(1, trials - 1);
        bool ok = true;
        while (!ready.empty()) {
            int bi = -1; double bs = -1e18;
            for (int idx = 0; idx < (int)ready.size(); idx++) {
                int u = ready[idx]; const Node& x = nodes[u];
                int fr = (rem[x.a] == 1) + (x.b != x.a && rem[x.b] == 1);
                if (live - fr + 1 > P.nreg) continue;
                int stays = rem[u] > 0 ? 1 : 0;
                double look = 0;
                for (int w : users[u]) if (indeg[w] == 1) {   // w becomes ready after u
                    const Node& y = nodes[w]; int o = (y.a == u) ? y.b : y.a;
                    look += 0.5 + ((rem[o] == 1 && o != u) ? 1.0 : 0.0) + (rem[u] == 1 ? 1.0 : 0.0);
                }
                double sc = 10.0 * (fr - stays) + 1.5 * look + noise * (double)(R() % 1000) / 1000.0;
                if (sc > bs) { bs = sc; bi = idx; }
            }
            if (bi < 0) { ok = false; break; }
            int u = ready[bi]; ready[bi] = ready.back(); ready.pop_back();
            const Node& x = nodes[u]; order.push_back(u); done[u] = 1;
            int fr = 0; if (--rem[x.a] == 0) fr++; if (x.b != x.a && --rem[x.b] == 0) fr++;
            live = live - fr + (rem[u] > 0 ? 1 : 0);
            for (int w : users[u]) if (--indeg[w] == 0) ready.push_back(w);
        }
        if (!ok || (int)order.size() != n) continue;
        vector<int> pos(n); for (int i = 0; i < n; i++) pos[order[i]] = i;
        vector<Node> out(n);
        for (int i = 0; i < n; i++) { Node x = nodes[order[i]]; if (x.op >= 0) { x.a = pos[x.a]; x.b = pos[x.b]; } out[i] = x; }
        if (nodes_to_prog(P, out, prog)) return true;
    }
    return false;
}

static bool nodes_to_prog_any(const Puzzle& P, const vector<Node>& nodes, vector<array<int, 4>>& prog) {
    if (nodes_to_prog(P, nodes, prog)) return true;
    vector<Node> r = reschedule(nodes);
    return nodes_to_prog(P, r, prog);
}
