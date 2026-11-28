// setwalk: annealing over VALUE SETS (idea: goodpjw2008's "triwalk", described in their public notebook; this is an
// independent implementation on our engine). A state is the set V of values a program computes. Every relation
// a+b=c or a*b=c with a,b,c in V is a "triple": any two members give the third (c=a+b, a=c-b, b=c-a; c=a*b, a=c/b,
// b=c/a). V is a valid program iff closing the starting values under the triples of V reaches all of V (value 1 is
// always derivable as x/x). Cost = |V| - starts. Moves: add a value w that appears in >= 2 relations with pairs of V,
// then greedily drop values that are no longer needed; neutral moves walk plateaus, occasional +1 moves explore.
// Strictly shorter states are compiled (derivation order -> register scheduling -> replay) and written as R lines.
// Usage: ./setwalk bank out secs worker nworkers [idsfile] [slack]
#include "santa.hpp"

static mt19937_64 R(12345);

struct Tri { int a, b, c; bool mul, alive; };

struct PairTable {                         // value -> number of relations y?z over pairs of V; candidates: count >= 2
    vector<ll> key; vector<int> cnt, pos; ull mask = 0; size_t used = 0; vector<ll> cand;
    void init(int bits) { key.assign(1ull << bits, 0); cnt.assign(1ull << bits, 0); pos.assign(1ull << bits, -1); mask = (1ull << bits) - 1; used = 0; cand.clear(); }
    inline size_t find(ll v) const { size_t i = mix64((ull)v) & mask; while (key[i] && key[i] != v) i = (i + 1) & mask; return i; }
    void rebuild() {
        vector<ll> k2; vector<int> c2;
        for (size_t i = 0; i <= mask; i++) if (key[i] && cnt[i] > 0) { k2.push_back(key[i]); c2.push_back(cnt[i]); }
        int bits = 1; while ((1ull << bits) < k2.size() * 4 + 1024) bits++;
        init(bits);
        for (size_t t = 0; t < k2.size(); t++) { size_t i = find(k2[t]); key[i] = k2[t]; cnt[i] = c2[t]; used++; if (c2[t] >= 2) { pos[i] = cand.size(); cand.push_back(k2[t]); } }
    }
    inline void inc(ll v) {
        size_t i = find(v); if (!key[i]) { key[i] = v; used++; if (used * 2 > mask) { rebuild(); i = find(v); if (!key[i]) { key[i] = v; used++; } } }
        if (++cnt[i] == 2) { pos[i] = cand.size(); cand.push_back(v); }
    }
    inline void dec(ll v) {
        size_t i = find(v); if (!key[i]) return;
        if (--cnt[i] == 1) { int p = pos[i]; ll last = cand.back(); cand.pop_back(); if (last != v) { cand[p] = last; pos[find(last)] = p; } pos[i] = -1; }
    }
};

struct SetWalk {
    const Puzzle& Pz; ll L;
    vector<ll> val; vector<char> used, isS, isT; vector<int> freeSlots; unordered_map<ll, int> slotOf;
    vector<vector<int>> triOf; vector<Tri> tris; vector<int> freeTris;
    PairTable pt; int nStartSlots = 0, cost = 0;
    vector<int> dmask, derivedBy, derivedDir; vector<char> der; vector<int> order;   // closure scratch

    SetWalk(const Puzzle& p) : Pz(p), L(p.L) { pt.init(16); }

    int slot(ll v) const { auto it = slotOf.find(v); return it == slotOf.end() ? -1 : it->second; }
    int newSlot(ll v) {
        int s; if (!freeSlots.empty()) { s = freeSlots.back(); freeSlots.pop_back(); }
        else { s = val.size(); val.push_back(0); used.push_back(0); isS.push_back(0); isT.push_back(0); triOf.emplace_back(); }
        val[s] = v; used[s] = 1; isS[s] = 0; isT[s] = 0; triOf[s].clear(); slotOf[v] = s; return s;
    }
    void addTri(int a, int b, int c, bool mul) {
        if (a > b) swap(a, b);
        for (int t : triOf[c]) { const Tri& x = tris[t]; if (x.alive && x.c == c && x.a == a && x.b == b && x.mul == mul) return; }
        int t; if (!freeTris.empty()) { t = freeTris.back(); freeTris.pop_back(); } else { t = tris.size(); tris.push_back({}); }
        tris[t] = {a, b, c, mul, true};
        triOf[a].push_back(t); if (b != a) triOf[b].push_back(t); triOf[c].push_back(t);
    }
    static void pairVals(ll w, ll y, ll L, ll out[5], int& n) {
        n = 0; out[n++] = w + y;
        if (w != y) out[n++] = w > y ? w - y : y - w;
        { i128 m = (i128)w * y; if (m <= (i128)L) out[n++] = (ll)m; }
        if (w != y && y > 1 && w % y == 0) out[n++] = w / y;
        if (w != y && w > 1 && y % w == 0) out[n++] = y / w;
    }
    // insert value v into V: discover its triples, update the pair table
    int insert(ll v, bool start = false) {
        int s = newSlot(v); isS[s] = start; if (!start) cost++;
        for (size_t yi = 0; yi < val.size(); yi++) {
            if (!used[yi]) continue; ll y = val[yi]; int z;
            if (y + v <= L && (z = slot(y + v)) >= 0 && z != s && z != (int)yi) addTri(s, yi, z, false);
            if ((int)yi != s) {
                if (v > y && (z = slot(v - y)) >= 0 && z != s) addTri(yi, z, s, false);          // y + z = v (z == y: v = 2y)
                if (y > v && (z = slot(y - v)) >= 0 && z != s && z != (int)yi) addTri(s, z, yi, false);
                if (y > 1 && v > 1) {
                    i128 m = (i128)y * v; if (m <= (i128)L && (z = slot((ll)m)) >= 0 && z != s && z != (int)yi) addTri(s, yi, z, true);
                    if (v % y == 0 && (z = slot(v / y)) >= 0 && z != s && val[z] > 1) addTri(yi, z, s, true);   // y * z = v (z == y: v = y^2)
                    if (y % v == 0 && (z = slot(y / v)) >= 0 && z != s && z != (int)yi && val[z] > 1) addTri(s, z, yi, true);
                }
            } else if (v > 1) { i128 m = (i128)v * v; if (m <= (i128)L && (z = slot((ll)m)) >= 0 && z != s) addTri(s, s, z, true); }
            ll pv[5]; int n; pairVals(v, y, L, pv, n); for (int k = 0; k < n; k++) if (pv[k] >= 1 && pv[k] <= L) pt.inc(pv[k]);
        }
        return s;
    }
    void erase(int s) {
        ll v = val[s];
        for (size_t yi = 0; yi < val.size(); yi++) {
            if (!used[yi]) continue; ll pv[5]; int n; pairVals(v, val[yi], L, pv, n);
            for (int k = 0; k < n; k++) if (pv[k] >= 1 && pv[k] <= L) pt.dec(pv[k]);
        }
        for (int t : triOf[s]) {
            Tri& x = tris[t]; if (!x.alive) continue; x.alive = false; freeTris.push_back(t);
            for (int m : {x.a, x.b, x.c}) if (m != s) { auto& L2 = triOf[m]; L2.erase(remove(L2.begin(), L2.end(), t), L2.end()); }
        }
        triOf[s].clear(); used[s] = 0; slotOf.erase(v); freeSlots.push_back(s); if (!isS[s]) cost--;
    }
    // closure from the starts with slot `skip` removed; true iff every other value is derivable. Records derivations.
    bool closure(int skip) {
        size_t n = val.size(); der.assign(n, 0); derivedBy.assign(n, -2); derivedDir.assign(n, -1); order.clear();
        if (dmask.size() < tris.size()) dmask.resize(tris.size()); fill(dmask.begin(), dmask.begin() + tris.size(), 0);
        vector<int> q;
        auto mark = [&](int s, int by, int dir) { if (der[s]) return; der[s] = 1; derivedBy[s] = by; derivedDir[s] = dir; q.push_back(s); };
        for (size_t s = 0; s < n; s++) if (used[s] && (int)s != skip && isS[s]) mark(s, -1, -1);
        int one = slot(1); if (one >= 0 && one != skip) mark(one, -3, -1);
        for (size_t h = 0; h < q.size(); h++) {
            int v = q[h]; order.push_back(v);
            for (int t : triOf[v]) {
                const Tri& x = tris[t]; if (!x.alive || x.a == skip || x.b == skip || x.c == skip) continue;
                if (x.a == v) dmask[t] |= 1; if (x.b == v) dmask[t] |= 2; if (x.c == v) dmask[t] |= 4;
                int m = dmask[t];
                if ((m & 3) == 3 && !der[x.c]) mark(x.c, t, 2);
                if (x.a != x.b) {
                    if ((m & 6) == 6 && !der[x.a]) mark(x.a, t, 0);
                    if ((m & 5) == 5 && !der[x.b]) mark(x.b, t, 1);
                }
            }
        }
        for (size_t s = 0; s < n; s++) if (used[s] && (int)s != skip && !der[s]) return false;
        return true;
    }
    // bit-parallel removability (least fixed point, 64 candidate deletions per word): D[v] bit x = "v derivable when x is
    // deleted". Returns the slots x (non-start, non-target, != protect) whose deletion keeps every other value derivable.
    vector<int> removable(int protect) {
        vector<int> idx(val.size(), -1), cand; for (size_t s = 0; s < val.size(); s++) if (used[s] && !isS[s]) { idx[s] = cand.size(); cand.push_back(s); }
        int n = cand.size(), W = (n + 63) / 64; if (!n) return {};
        vector<ull> D((size_t)val.size() * W, 0), self((size_t)W * n, 0);
        auto row = [&](int s) { return &D[(size_t)s * W]; };
        for (size_t s = 0; s < val.size(); s++) if (used[s]) {
            ull* r = row(s);
            if (isS[s]) { for (int k = 0; k < W; k++) r[k] = ~0ull; }
            else if (val[s] == 1) { for (int k = 0; k < W; k++) r[k] = ~0ull; r[idx[s] / 64] &= ~(1ull << (idx[s] % 64)); }
        }
        bool changed = true; int sweeps = 0;
        while (changed && sweeps < 64) {
            changed = false; sweeps++;
            for (size_t t = 0; t < tris.size(); t++) {
                const Tri& x = tris[t]; if (!x.alive) continue;
                // (target, src1, src2): c <- a,b ; a <- c,b ; b <- c,a (the last two only for distinct a,b)
                int dirs = (x.a == x.b) ? 1 : 3;
                for (int d = 0; d < dirs; d++) {
                    int tgt = d == 0 ? x.c : (d == 1 ? x.a : x.b), s1 = d == 0 ? x.a : x.c, s2 = d == 0 ? x.b : (d == 1 ? x.b : x.a);
                    if (isS[tgt]) continue;
                    ull *rt = row(tgt), *r1 = row(s1), *r2 = row(s2); int bt = idx[tgt];
                    for (int k = 0; k < W; k++) {
                        ull nv = rt[k] | (r1[k] & r2[k]);
                        if (k == bt / 64) nv &= ~(1ull << (bt % 64));        // a deleted value is not derivable in its own world
                        if (nv != rt[k]) { rt[k] = nv; changed = true; }
                    }
                }
            }
        }
        vector<ull> ok(W, ~0ull);
        for (int i = 0; i < n; i++) { int s = cand[i]; ull* r = row(s); for (int k = 0; k < W; k++) { ull m = r[k]; if (k == i / 64) m |= 1ull << (i % 64); ok[k] &= m; } }
        vector<int> out;
        for (int i = 0; i < n; i++) if (ok[i / 64] >> (i % 64) & 1) { int s = cand[i]; if (!isT[s] && s != protect) out.push_back(s); }
        return out;
    }
    // build a program from the last successful closure (derivation order) and compile it into 48 registers
    bool compile(vector<array<int, 4>>& prog) {
        vector<Node> nodes; unordered_map<int, int> nodeOf;
        for (size_t i = 0; i < Pz.starts.size(); i++) { int s = slot(Pz.starts[i]); if (s >= 0 && !nodeOf.count(s)) { nodeOf[s] = nodes.size(); nodes.push_back({Pz.starts[i], -1, -1, -1}); } }
        for (int s : order) {
            if (nodeOf.count(s)) continue;
            Node nd; nd.v = val[s];
            if (derivedBy[s] == -3) { nd.op = OP_DIV; nd.a = 0; nd.b = 0; }
            else {
                const Tri& x = tris[derivedBy[s]]; int d = derivedDir[s];
                if (d == 2) { nd.op = x.mul ? OP_MUL : OP_ADD; nd.a = nodeOf[x.a]; nd.b = nodeOf[x.b]; }
                else if (d == 0) { nd.op = x.mul ? OP_DIV : OP_SUB; nd.a = nodeOf[x.c]; nd.b = nodeOf[x.b]; }
                else { nd.op = x.mul ? OP_DIV : OP_SUB; nd.a = nodeOf[x.c]; nd.b = nodeOf[x.a]; }
            }
            nodeOf[s] = nodes.size(); nodes.push_back(nd);
        }
        if (!nodes_to_prog_any(Pz, nodes, prog) && !schedule_fit(Pz, nodes, prog, 300, R())) return false;
        return verify_prog(Pz, prog) == (int)prog.size();
    }
};

int main(int argc, char** argv) {
    if (argc < 6) { fprintf(stderr, "usage: setwalk bank out secs worker nworkers [ids] [slack]\n"); return 1; }
    auto puzzles = read_bank(argv[1]); FILE* fo = fopen(argv[2], "a"); double secs = atof(argv[3]);
    int w = atoi(argv[4]), nw = atoi(argv[5]); int slackMax = argc > 7 ? atoi(argv[7]) : 2;
    set<string> ids; if (argc > 6) { ifstream f(argv[6]); string s; while (f >> s) ids.insert(s); }
    unsigned long long seed0 = getenv("SA_SEED") ? strtoull(getenv("SA_SEED"), nullptr, 10) : 1ULL;
    // alternative programs per puzzle (V lines: pid n op i j d ...): their value sets seed union restarts (value-set crossover)
    map<string, vector<vector<array<int, 4>>>> variants;
    if (getenv("SW_VARIANTS")) { ifstream f(getenv("SW_VARIANTS")); string tag; while (f >> tag) { string pid; int n; f >> pid >> n; vector<array<int, 4>> pr(n); for (auto& x : pr) f >> x[0] >> x[1] >> x[2] >> x[3]; variants[pid].push_back(pr); } }
    long long unionEvery = getenv("SW_UNION") ? atoll(getenv("SW_UNION")) : 25000;
    int idx = 0, total = 0;
    for (auto& Pz : puzzles) {
        if (!ids.empty() && !ids.count(Pz.id)) continue;
        if ((idx++ % nw) != w) continue;
        R.seed(seed0 * 0x9E3779B97F4A7C15ULL ^ std::hash<string>{}(Pz.id));
        // initial value set = values of the bank program
        SetWalk S(Pz);
        { vector<ll> regs(Pz.nreg, 0); for (size_t i = 0; i < Pz.starts.size(); i++) regs[i] = Pz.starts[i];
          for (ll s : Pz.starts) if (S.slot(s) < 0) S.insert(s, true);
          for (auto& ins : Pz.prog) { ll v = apply_op(ins[0], regs[ins[1]], regs[ins[2]], Pz.L); regs[ins[3]] = v; if (v && S.slot(v) < 0) S.insert(v); } }
        for (ll t : Pz.targets) { int s = S.slot(t); if (s >= 0) S.isT[s] = 1; }
        int start = Pz.prog.size(); vector<array<int, 4>> bestProg = Pz.prog; int bestLen = start;
        if (!S.closure(-1)) { printf("%s initial value set not closed; skipped\n", Pz.id.c_str()); fflush(stdout); continue; }
        long long moves = 0, neutral = 0, ups = 0, improved = 0, compileFail = 0, unions = 0;
        vector<vector<ll>> vsets;   // value sets of this puzzle's variant programs
        for (auto& pr : variants[Pz.id]) {
            vector<ll> regs(Pz.nreg, 0), vs; for (size_t i = 0; i < Pz.starts.size(); i++) regs[i] = Pz.starts[i]; bool ok = true;
            for (auto& ins : pr) { if (ins[1] < 0 || ins[1] >= Pz.nreg || ins[2] < 0 || ins[2] >= Pz.nreg || ins[3] < 0 || ins[3] >= Pz.nreg) { ok = false; break; }
                ll v = apply_op(ins[0], regs[ins[1]], regs[ins[2]], Pz.L); if (!v) { ok = false; break; } regs[ins[3]] = v; vs.push_back(v); }
            if (ok) vsets.push_back(vs);
        }
        auto t0 = chrono::steady_clock::now(); int sinceBest = 0;
        // simple greedy cleanup first (values the program never needed)
        bool fast = getenv("SW_FAST") ? atoi(getenv("SW_FAST")) : 1;
        auto dropAll = [&](int protect) {
            int removed = 0;
            if (fast) {
                while (true) { auto rm = S.removable(protect); if (rm.empty()) break; S.erase(rm[R() % rm.size()]); removed++; }
                return removed;
            }
            vector<int> cands;
            for (size_t s = 0; s < S.val.size(); s++) if (S.used[s] && !S.isS[s] && !S.isT[s] && (int)s != protect) cands.push_back(s);
            shuffle(cands.begin(), cands.end(), R);
            for (int x : cands) if (S.used[x] && S.closure(x)) { S.erase(x); removed++; }
            return removed;
        };
        dropAll(-1);
        // targeted removal: only values within two triple-steps of the inserted value (full sweep every 64 moves)
        auto dropNear = [&](int ws) {
            static vector<int> mark; mark.assign(S.val.size(), 0); vector<int> ring, cands;
            for (int t : S.triOf[ws]) { const Tri& x = S.tris[t]; if (!x.alive) continue; for (int m : {x.a, x.b, x.c}) if (!mark[m]) { mark[m] = 1; ring.push_back(m); } }
            size_t r1 = ring.size();
            for (size_t i = 0; i < r1; i++) for (int t : S.triOf[ring[i]]) { const Tri& x = S.tris[t]; if (!x.alive) continue; for (int m : {x.a, x.b, x.c}) if (!mark[m]) { mark[m] = 1; ring.push_back(m); } }
            for (int m : ring) if (m != ws && S.used[m] && !S.isS[m] && !S.isT[m]) cands.push_back(m);
            shuffle(cands.begin(), cands.end(), R); int removed = 0;
            for (int x : cands) if (S.used[x] && S.closure(x)) { S.erase(x); removed++; }
            return removed;
        };
        bool nearMode = getenv("SW_NEAR") ? atoi(getenv("SW_NEAR")) : 1;
        auto snapshot = [&]() { vector<ll> v; for (size_t s = 0; s < S.val.size(); s++) if (S.used[s] && !S.isS[s]) v.push_back(S.val[s]); return v; };
        vector<ll> bestSet = snapshot();
        auto restore = [&](const vector<ll>& vs) {
            SetWalk T(Pz); for (ll s : Pz.starts) if (T.slot(s) < 0) T.insert(s, true);
            for (ll v : vs) if (T.slot(v) < 0) T.insert(v);
            for (ll t : Pz.targets) { int s = T.slot(t); if (s >= 0) T.isT[s] = 1; }
            S.~SetWalk(); new (&S) SetWalk(std::move(T));
        };
        while (chrono::duration<double>(chrono::steady_clock::now() - t0).count() < secs) {
            if (S.pt.cand.empty()) break;
            ll wv = 0; for (int tries = 0; tries < 50; tries++) { ll c = S.pt.cand[R() % S.pt.cand.size()]; if (c >= 1 && c <= Pz.L && S.slot(c) < 0) { wv = c; break; } }
            if (!wv) continue;
            moves++;
            int ws = S.insert(wv);
            int removed = fast ? dropAll(ws) : ((nearMode && moves % 64) ? dropNear(ws) : dropAll(ws));
            int cap = bestLen + slackMax;
            if (removed == 0) {
                // +1 move: keep with small probability while under the slack cap, otherwise undo
                if (S.cost < cap && R() % 100 < 4) ups++;
                else { S.erase(ws); continue; }
            } else if (removed == 1) neutral++;
            if (S.cost > cap) { dropAll(-1); if (S.cost > cap) { restore(bestSet); continue; } }   // drift guard
            if (S.cost < bestLen) {
                if (S.closure(-1)) {
                    vector<array<int, 4>> prog;
                    if (S.compile(prog) && (int)prog.size() < bestLen) { bestLen = prog.size(); bestProg = prog; improved++; sinceBest = 0; bestSet = snapshot(); }
                    else compileFail++;
                }
            }
            if (!vsets.empty() && unionEvery > 0 && moves % unionEvery == 0) {   // value-set crossover: best U variant, then shrink
                vector<ll> u = bestSet; const auto& vv = vsets[R() % vsets.size()]; u.insert(u.end(), vv.begin(), vv.end());
                restore(u); dropAll(-1); unions++; sinceBest = 0; continue;
            }
            if (++sinceBest > 20000) { sinceBest = 0; restore(bestSet); }   // long plateau: restart from the best compiled set
        }
        if (bestLen < start) {
            fprintf(fo, "R %s %zu", Pz.id.c_str(), bestProg.size()); for (auto& x : bestProg) fprintf(fo, " %d %d %d %d", x[0], x[1], x[2], x[3]); fprintf(fo, "\n"); fflush(fo);
            total += start - bestLen;
        }
        printf("%s start=%d best=%d moves=%lld neutral=%lld ups=%lld improved=%lld cfail=%lld unions=%lld total=%d\n", Pz.id.c_str(), start, bestLen, moves, neutral, ups, improved, compileFail, unions, total); fflush(stdout);
    }
}
