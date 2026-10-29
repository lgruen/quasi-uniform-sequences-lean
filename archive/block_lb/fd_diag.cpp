// fd_diag.cpp -- the free diagonal of Theorem thm:block(d) for the designs U*_s (s = 4..10): the program of the Lean
// stage that produced the designs (archived as one of the two programs; computation unchanged).
//
// The off-diagonal entries of the design are those of U*_s (file block_lb/ustar<s>.txt: s, then the s-1 matrices F_n,
// rows); the diagonal of F_0 is replaced by -delta (the deeper diagonals stay 0, so every partial sum M^{(j)} has the
// diagonal -delta).  For a step e in {-1,0,1}^s (e != 0) with carry depths j_c (moving coordinates c) the change of
// a moving coordinate i is sigma_i = -e_i delta_i + R_i, R_i = sum_{c != i} e_c M^{(j_c)}[i][c]; it is backward iff
// e_i sigma_i <= 0 iff r_i := e_i R_i <= delta_i, and then |sigma_i| = delta_i - r_i.
//
//  A(delta) := the least A such that every step has a backward coordinate with |sigma| <= A or two backward
//  coordinates (the hypothesis of Lemma lem:signclass); INF if some step has no backward coordinate at all.  Then
//  LB(F) >= 1 - (A+1)/p for all large p (Lemma lem:signclass), and LB(F) <= 1-(max delta+1)/p (axis steps).
//  (r_i is stored clamped to [-127,127]; for delta_c < 127 this does not change which coordinates are backward, and
//  a clamped value can only make a reported A >= 127, so a reported A < 127 is exact.)
//
// Modes:
//   fd_diag <file> A d_0 .. d_{s-1}          A(delta), the binding tuples
//   fd_diag <file> lb p d_0 .. d_{s-1}       exact one-digit relaxation: prints p - sqrt(min sum g^2) and (archive
//                                            addition, output only) sumsq = min sum g^2 = (p LB)^2
//   fd_diag <file> csp A [cap]               exhaustive DFS over delta in [0,A]^s: the diagonals with A(delta) <= A
//   fd_diag <file> search Dmax restarts seed  coordinate descent over delta in [0,Dmax]^s (heuristic, NOT exhaustive)
//   fd_diag <file> uniform Dmax              A(u,...,u) for u = 0..Dmax
//   fd_diag <file> exh Dmax                  exhaustive over delta in [0,Dmax]^s with pruning by axis bound (small s)
//   (modes cut, fc, gfc: other exact decision procedures of the search; not used by the archive checks)
// Build (from the archive root): g++ -O2 -std=c++17 -o bin/fd_diag block_lb/fd_diag.cpp
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cmath>
#include <vector>
#include <unordered_set>
#include <algorithm>
#include <random>
using namespace std;

int s;
int F[12][12][12];  // F[n][i][c]
int M[12][12][12];  // partial sums
const int L = 127;   // clamp bound for r_i

vector<uint64_t> keys;  // distinct (mask, clamped r_i) tuples

static inline uint64_t pack(int mask, const int* r) {
  uint64_t k = (uint64_t)mask;
  for (int i = 0; i < s; i++) k |= (uint64_t)(uint8_t)(r[i] + 128) << (8 + 8 * i);
  return k;
}

void build() {
  vector<uint64_t> all;
  int e[12], j[12], r[12];
  long long total = 0;
  for (int mask = 1; mask < (1 << s); mask++) {
    int mov[12], k = 0;
    for (int c = 0; c < s; c++) if (mask >> c & 1) mov[k++] = c;
    // signs: first moving coordinate +1 (global flip leaves r invariant)
    for (int sg = 0; sg < (1 << (k - 1)); sg++) {
      for (int c = 0; c < s; c++) e[c] = 0;
      e[mov[0]] = 1;
      for (int t = 1; t < k; t++) e[mov[t]] = (sg >> (t - 1) & 1) ? -1 : 1;
      long long nj = 1;
      for (int t = 0; t < k; t++) nj *= (s - 1);
      for (long long jj = 0; jj < nj; jj++) {
        long long x = jj;
        for (int t = 0; t < k; t++) { j[mov[t]] = x % (s - 1); x /= (s - 1); }
        for (int i = 0; i < s; i++) r[i] = 0;
        for (int t = 0; t < k; t++) {
          int i = mov[t];
          int R = 0;
          for (int u = 0; u < k; u++) { int c = mov[u]; if (c != i) R += e[c] * M[j[c]][i][c]; }
          int v = e[i] * R;
          if (v > L) v = L;
          if (v < -L) v = -L;
          r[i] = v;
        }
        all.push_back(pack(mask, r));
        total++;
      }
    }
  }
  sort(all.begin(), all.end());
  all.erase(unique(all.begin(), all.end()), all.end());
  keys.swap(all);
  fprintf(stderr, "s=%d: %lld step classes (mod global sign), %zu distinct clamped tuples\n", s, total, keys.size());
}

// A(delta); also returns the number of tuples with no backward coordinate (if >0, A = INF)
const int INF = 1 << 20;
int evalA(const int* d, int cap = INF, long long* nobk = nullptr) {
  int A = 0;
  for (int c = 0; c < s; c++) A = max(A, d[c]);
  long long nb = 0;
  for (uint64_t k : keys) {
    int mask = k & 0xff;
    int cnt = 0, bi = -1;
    for (int i = 0; i < s; i++) if (mask >> i & 1) {
      int r = (int)((k >> (8 + 8 * i)) & 0xff) - 128;
      if (r <= d[i]) { cnt++; bi = i; if (cnt >= 2) break; }
    }
    if (cnt == 0) { nb++; if (!nobk) return INF; continue; }
    if (cnt == 1) {
      int r = (int)((k >> (8 + 8 * bi)) & 0xff) - 128;
      int v = d[bi] - r;
      if (v > A) { A = v; if (A >= cap) return A; }
    }
  }
  if (nobk) { *nobk = nb; if (nb) return INF; }
  return A;
}

// exact one-digit relaxation (integer numerators g = p f_1)
long long lastBest = -1;  // archive addition: the integer minimum, for output only
double exactLB(long long p, const int* d) {
  int G[12][12][12];
  for (int n = 0; n < s - 1; n++) for (int i = 0; i < s; i++) for (int c = 0; c < s; c++)
    G[n][i][c] = (i == c) ? -d[c] : M[n][i][c];
  long long best = -1;
  int e[12], j[12];
  for (int mask = 1; mask < (1 << s); mask++) {
    int mov[12], k = 0;
    for (int c = 0; c < s; c++) if (mask >> c & 1) mov[k++] = c;
    for (int sg = 0; sg < (1 << k); sg++) {
      for (int c = 0; c < s; c++) e[c] = 0;
      for (int t = 0; t < k; t++) e[mov[t]] = (sg >> t & 1) ? -1 : 1;
      long long nj = 1;
      for (int t = 0; t < k; t++) nj *= (s - 1);
      for (long long jj = 0; jj < nj; jj++) {
        long long x = jj;
        for (int t = 0; t < k; t++) { j[mov[t]] = x % (s - 1); x /= (s - 1); }
        long long tot = 0;
        for (int i = 0; i < s; i++) {
          long long sig = 0;
          for (int t = 0; t < k; t++) { int c = mov[t]; sig += e[c] * G[j[c]][i][c]; }
          long long rr = ((sig % p) + p) % p;
          long long g;
          if (e[i] == 0) g = rr == 0 ? 0 : min(rr, p - rr) - 1;
          else if (e[i] == 1) g = rr == 0 ? p - 1 : rr - 1;
          else g = p - 1 - rr;
          tot += g * g;
        }
        if (best < 0 || tot < best) best = tot;
      }
    }
  }
  lastBest = best;
  return (double)p - sqrt((double)best);
}


// ---- exhaustive decision: is there delta in [0,A]^s with A(delta) <= A ?  (DFS, all solutions counted up to a cap)
vector<vector<uint64_t>> grp;
int cspA, dd[12];
long long nsol = 0, nodes = 0, solcap = 20;
static inline bool okTuple(uint64_t k) {
  int mask = k & 0xff;
  int cnt = 0, bi = -1;
  for (int i = 0; i < s; i++) if (mask >> i & 1) {
    int r = (int)((k >> (8 + 8 * i)) & 0xff) - 128;
    if (r <= dd[i]) { cnt++; bi = i; if (cnt >= 2) return true; }
  }
  if (cnt == 0) return false;
  int r = (int)((k >> (8 + 8 * bi)) & 0xff) - 128;
  return dd[bi] - r <= cspA;
}
void dfs(int t) {
  if (t == s) {
    nsol++;
    if (nsol <= solcap) { printf("  sol:"); for (int c = 0; c < s; c++) printf(" %d", dd[c]); printf("\n"); }
    return;
  }
  for (int v = 0; v <= cspA; v++) {
    dd[t] = v;
    nodes++;
    vector<uint64_t>& G = grp[t];
    bool ok = true;
    for (size_t q = 0; q < G.size(); q++) {
      if (!okTuple(G[q])) { if (q > 0) swap(G[q], G[q / 2]); ok = false; break; }
    }
    if (ok) dfs(t + 1);
    if (nsol >= solcap) return;
  }
}

// ---- cutting planes: exact decision of "exists delta with A(delta) <= A" using an active subset of tuples
bool foundOne; int solD[12];
void dfs1(int t) {
  if (foundOne) return;
  if (t == s) { foundOne = true; for (int c = 0; c < s; c++) solD[c] = dd[c]; return; }
  for (int v = 0; v <= cspA && !foundOne; v++) {
    dd[t] = v;
    nodes++;
    vector<uint64_t>& G = grp[t];
    bool ok = true;
    for (size_t q = 0; q < G.size(); q++) {
      if (!okTuple(G[q])) { if (q > 0) swap(G[q], G[q / 2]); ok = false; break; }
    }
    if (ok) dfs1(t + 1);
  }
}
void cutDecide(int A, int smallK, int addcap) {
  cspA = A;
  grp.assign(s, {});
  long long nact = 0;
  for (uint64_t k : keys) { int mask = k & 0xff; if (__builtin_popcount(mask) <= smallK) { grp[31 - __builtin_clz(mask)].push_back(k); nact++; } }
  for (int it = 0; it < 100000; it++) {
    foundOne = false; nodes = 0;
    dfs1(0);
    if (!foundOne) { printf("CUT A=%d: INFEASIBLE (exact; iteration %d, active %lld)\n", A, it, nact); return; }
    for (int c = 0; c < s; c++) dd[c] = solD[c];
    long long added = 0;
    for (uint64_t k : keys) if (!okTuple(k)) {
      grp[31 - __builtin_clz((int)(k & 0xff))].push_back(k); nact++; if (++added >= addcap) break; }
    fprintf(stderr, "  it %d: cand", it); for (int c = 0; c < s; c++) fprintf(stderr, " %d", solD[c]);
    fprintf(stderr, " nodes=%lld violated-added=%lld active=%lld\n", nodes, added, nact);
    if (added == 0) {
      printf("CUT A=%d: FEASIBLE d=", A); for (int c = 0; c < s; c++) printf("%d ", solD[c]);
      printf(" (A(d)=%d)\n", evalA(solD)); return; }
  }
}

// ---- forward checking with interval domains (128-bit masks), cutting planes over the full tuple set
typedef unsigned __int128 u128;
static inline u128 ivl(int lo, int hi) {  // bits lo..hi of [0, cspA]
  if (lo < 0) lo = 0;
  if (hi > cspA) hi = cspA;
  if (lo > hi) return 0;
  u128 a = (hi >= 127) ? ~(u128)0 : (((u128)1 << (hi + 1)) - 1);
  u128 b = ((u128)1 << lo) - 1;
  return a & ~b;
}
int ordr[12], posOf[12];
vector<vector<uint64_t>> trig;  // trig[t]: tuples whose second-to-last coordinate (in the order) is ordr[t]; unary/last at t
vector<vector<uint64_t>> lastAt; // tuples with exactly one coordinate (unary) or used as final check
u128 dom[13][12];
bool fcFound; int fcSol[12];
long long fcNodes;
static inline int lastCoord(int mask) { int best = -1, bp = -1; for (int i = 0; i < s; i++) if (mask >> i & 1) if (posOf[i] > bp) { bp = posOf[i]; best = i; } return best; }
static inline int secondLast(int mask) { int l = lastCoord(mask); int best = -1, bp = -1; for (int i = 0; i < s; i++) if ((mask >> i & 1) && i != l) if (posOf[i] > bp) { bp = posOf[i]; best = i; } return best; }
void addActive(uint64_t k) {
  int mask = k & 0xff;
  if (__builtin_popcount(mask) == 1) { lastAt[0].push_back(k); return; }
  trig[posOf[secondLast(mask)]].push_back(k);
}
// restrict the last coordinate u of tuple k given the assigned others (dd)
static inline u128 allowedLast(uint64_t k) {
  int mask = k & 0xff, u = lastCoord(mask);
  int nb = 0; bool good = false;
  for (int i = 0; i < s; i++) if ((mask >> i & 1) && i != u) {
    int r = (int)((k >> (8 + 8 * i)) & 0xff) - 128;
    if (r <= dd[i]) { nb++; if (dd[i] - r <= cspA) good = true; }
  }
  int ru = (int)((k >> (8 + 8 * u)) & 0xff) - 128;
  if (nb >= 2) return ~(u128)0;
  if (nb == 1) return good ? ~(u128)0 : ivl(ru, cspA);
  return ivl(ru, cspA + ru);
}
void fcDfs(int t) {
  if (fcFound) return;
  if (t == s) { fcFound = true; for (int c = 0; c < s; c++) fcSol[c] = dd[c]; return; }
  int x = ordr[t];
  u128 D = dom[t][x];
  for (int v = 0; v <= cspA && !fcFound; v++) if ((D >> v) & 1) {
    dd[x] = v;
    fcNodes++;
    for (int u = 0; u < s; u++) dom[t + 1][u] = dom[t][u];
    bool ok = true;
    vector<uint64_t>& G = trig[t];
    for (size_t q = 0; q < G.size(); q++) {
      int u = lastCoord(G[q] & 0xff);
      dom[t + 1][u] &= allowedLast(G[q]);
      if (!dom[t + 1][u]) { if (q > 0) swap(G[q], G[q / 2]); ok = false; break; }
    }
    if (ok) fcDfs(t + 1);
  }
}
void fcDecide(int A, int smallK, int addcap) {
  cspA = A;
  // order: by alpha-like weight (row sums of |M|) descending, ties by index
  vector<pair<int,int>> w;
  for (int i = 0; i < s; i++) { int a = 0; for (int c = 0; c < s; c++) if (c != i) { int m = 0; for (int j = 0; j < s - 1; j++) m = max(m, abs(M[j][i][c])); a += m; } w.push_back({-a, i}); }
  sort(w.begin(), w.end());
  for (int t = 0; t < s; t++) { ordr[t] = w[t].second; posOf[ordr[t]] = t; }
  trig.assign(s, {}); lastAt.assign(1, {});
  long long nact = 0;
  for (uint64_t k : keys) if (__builtin_popcount((int)(k & 0xff)) <= smallK) { addActive(k); nact++; }
  for (int it = 0; it < 100000; it++) {
    for (int u = 0; u < s; u++) dom[0][u] = ivl(0, A);
    for (uint64_t k : lastAt[0]) { int u = lastCoord(k & 0xff); int r = (int)((k >> (8 + 8 * u)) & 0xff) - 128; dom[0][u] &= ivl(r, A + r); }
    fcFound = false; fcNodes = 0;
    fcDfs(0);
    if (!fcFound) { printf("FC A=%d: INFEASIBLE (exact; iteration %d, active %lld, nodes %lld)\n", A, it, nact, fcNodes); fflush(stdout); return; }
    for (int c = 0; c < s; c++) dd[c] = fcSol[c];
    long long added = 0;
    for (uint64_t k : keys) if (!okTuple(k)) { addActive(k); nact++; if (++added >= addcap) break; }
    fprintf(stderr, "  it %d: cand", it); for (int c = 0; c < s; c++) fprintf(stderr, " %d", fcSol[c]);
    fprintf(stderr, " nodes=%lld added=%lld active=%lld\n", fcNodes, added, nact);
    if (added == 0) { printf("FC A=%d: FEASIBLE d=", A); for (int c = 0; c < s; c++) printf("%d ", fcSol[c]); printf(" (A(d)=%d)\n", evalA(fcSol)); fflush(stdout); return; }
  }
}

// ---- generalized forward checking: every active tuple is re-examined at each of its coordinates' levels
vector<vector<uint64_t>> inv;   // inv[t]: active tuples containing ordr[t]
bool assignedAt[12];
// returns false if the tuple cannot be satisfied; may shrink domains in Dm of unassigned coordinates
static inline bool gfcTuple(uint64_t k, u128* Dm) {
  int mask = k & 0xff;
  int nbA = 0; bool goodA = false; int ncanB = 0, ncanG = 0, lastG = -1;
  for (int i = 0; i < s; i++) if (mask >> i & 1) {
    int r = (int)((k >> (8 + 8 * i)) & 0xff) - 128;
    if (assignedAt[i]) {
      if (r <= dd[i]) { nbA++; if (dd[i] - r <= cspA) goodA = true; }
    } else {
      if (Dm[i] & ivl(r, cspA)) ncanB++;
      if (Dm[i] & ivl(r, cspA + r)) { ncanG++; lastG = i; }
    }
  }
  if (nbA >= 2 || goodA) return true;
  if (nbA + ncanB >= 2) return true;
  if (ncanG == 0) return false;
  if (ncanG == 1 && nbA + ncanB <= 1) {
    int r = (int)((k >> (8 + 8 * lastG)) & 0xff) - 128;
    Dm[lastG] &= ivl(r, cspA + r);
  }
  return true;
}
void gDfs(int t) {
  if (fcFound) return;
  if (t == s) { fcFound = true; for (int c = 0; c < s; c++) fcSol[c] = dd[c]; return; }
  int x = ordr[t];
  u128 D = dom[t][x];
  for (int v = 0; v <= cspA && !fcFound; v++) if ((D >> v) & 1) {
    dd[x] = v; assignedAt[x] = true;
    fcNodes++;
    for (int u = 0; u < s; u++) dom[t + 1][u] = dom[t][u];
    bool ok = true;
    vector<uint64_t>& G = inv[t];
    for (size_t q = 0; q < G.size(); q++) {
      if (!gfcTuple(G[q], dom[t + 1])) { if (q > 0) swap(G[q], G[q / 2]); ok = false; break; }
    }
    if (ok) for (int u = 0; u < s; u++) if (!assignedAt[u] && !dom[t + 1][u]) { ok = false; break; }
    if (ok) gDfs(t + 1);
    assignedAt[x] = false;
  }
}
void gAdd(uint64_t k) { int mask = k & 0xff; for (int i = 0; i < s; i++) if (mask >> i & 1) inv[posOf[i]].push_back(k); }
void gDecide(int A, int smallK, int addcap) {
  cspA = A;
  vector<pair<int,int>> w;
  for (int i = 0; i < s; i++) { int a = 0; for (int c = 0; c < s; c++) if (c != i) { int m = 0; for (int j = 0; j < s - 1; j++) m = max(m, abs(M[j][i][c])); a += m; } w.push_back({-a, i}); }
  sort(w.begin(), w.end());
  for (int t = 0; t < s; t++) { ordr[t] = w[t].second; posOf[ordr[t]] = t; }
  inv.assign(s, {});
  long long nact = 0;
  for (uint64_t k : keys) if (__builtin_popcount((int)(k & 0xff)) <= smallK) { gAdd(k); nact++; }
  for (int it = 0; it < 100000; it++) {
    for (int u = 0; u < s; u++) { dom[0][u] = ivl(0, A); assignedAt[u] = false; }
    fcFound = false; fcNodes = 0;
    gDfs(0);
    if (!fcFound) { printf("GFC A=%d: INFEASIBLE (exact; iteration %d, active %lld, nodes %lld)\n", A, it, nact, fcNodes); fflush(stdout); return; }
    for (int c = 0; c < s; c++) dd[c] = fcSol[c];
    long long added = 0;
    if (addcap == 0) { printf("GFC(small only, |S|<=%d) A=%d: FEASIBLE d=", smallK, A); for (int c = 0; c < s; c++) printf("%d ", fcSol[c]); printf("\n"); return; }
    for (uint64_t k : keys) if (!okTuple(k)) { gAdd(k); nact++; if (++added >= addcap) break; }
    fprintf(stderr, "  it %d: cand", it); for (int c = 0; c < s; c++) fprintf(stderr, " %d", fcSol[c]);
    fprintf(stderr, " nodes=%lld added=%lld active=%lld\n", fcNodes, added, nact);
    if (added == 0) { printf("GFC A=%d: FEASIBLE d=", A); for (int c = 0; c < s; c++) printf("%d ", fcSol[c]); printf(" (A(d)=%d)\n", evalA(fcSol)); fflush(stdout); return; }
  }
}

int main(int argc, char** argv) {
  if (argc < 3) { fprintf(stderr, "usage\n"); return 1; }
  FILE* f = fopen(argv[1], "r");
  if (fscanf(f, "%d", &s) != 1) return 1;
  for (int n = 0; n < s - 1; n++) for (int i = 0; i < s; i++) for (int c = 0; c < s; c++)
    if (fscanf(f, "%d", &F[n][i][c]) != 1) return 1;
  fclose(f);
  for (int i = 0; i < s; i++) for (int c = 0; c < s; c++) {
    int acc = 0;
    for (int n = 0; n < s - 1; n++) { acc += F[n][i][c]; M[n][i][c] = acc; }
  }
  string mode = argv[2];
  if (mode == "lb") {
    long long p = atoll(argv[3]);
    int d[12];
    for (int c = 0; c < s; c++) d[c] = atoi(argv[4 + c]);
    double v = exactLB(p, d);
    printf("p=%lld p-p*LB=%.4f sumsq=%lld\n", p, v, lastBest);
    return 0;
  }
  build();
  if (mode == "A") {
    int d[12];
    for (int c = 0; c < s; c++) d[c] = atoi(argv[3 + c]);
    long long nb = 0;
    int A = evalA(d, INF, &nb);
    printf("A=%d no-backward-tuples=%lld\n", A == INF ? -1 : A, nb);
  } else if (mode == "uniform") {
    int D = atoi(argv[3]);
    for (int u = 0; u <= D; u++) {
      int d[12];
      for (int c = 0; c < s; c++) d[c] = u;
      long long nb = 0;
      int A = evalA(d, INF, &nb);
      printf("u=%d A=%s nobk=%lld\n", u, A == INF ? "INF" : to_string(A).c_str(), nb);
    }
  } else if (mode == "search") {
    int D = atoi(argv[3]), R = atoi(argv[4]);
    mt19937 rng(atoi(argv[5]));
    int bestA = INF, bestd[12];
    for (int rs = 0; rs < R; rs++) {
      int d[12];
      for (int c = 0; c < s; c++) d[c] = (rs == 0) ? D : (int)(rng() % (D + 1));
      int A = evalA(d);
      bool imp = true;
      while (imp) {
        imp = false;
        for (int c = 0; c < s; c++) {
          int keep = d[c], bv = keep;
          for (int v = 0; v <= D; v++) {
            d[c] = v;
            int a = evalA(d, A + 1);
            if (a < A || (a == A && v < bv && bv == keep && false)) { A = a; bv = v; imp = true; }
          }
          d[c] = bv;
        }
      }
      if (A < bestA) { bestA = A; for (int c = 0; c < s; c++) bestd[c] = d[c]; }
      printf("restart %d: A=%s d=", rs, A == INF ? "INF" : to_string(A).c_str());
      for (int c = 0; c < s; c++) printf("%d ", d[c]);
      printf("\n");
      fflush(stdout);
    }
    printf("BEST A=%d d=", bestA);
    for (int c = 0; c < s; c++) printf("%d ", bestd[c]);
    printf("\n");
  } else if (mode == "csp") {
    cspA = atoi(argv[3]);
    if (argc > 4) solcap = atoll(argv[4]);
    grp.assign(s, {});
    for (uint64_t k : keys) { int mask = k & 0xff; int t = 31 - __builtin_clz(mask); grp[t].push_back(k); }
    dfs(0);
    printf("CSP A=%d: solutions=%lld%s nodes=%lld\n", cspA, nsol, nsol >= solcap ? "+" : "", nodes);
  } else if (mode == "cut") {
    cutDecide(atoi(argv[3]), atoi(argv[4]), atoi(argv[5]));
  } else if (mode == "fc") {
    for (int a = 5; a < argc; a++) fcDecide(atoi(argv[a]), atoi(argv[3]), atoi(argv[4]));
  } else if (mode == "gfc") {
    for (int a = 5; a < argc; a++) gDecide(atoi(argv[a]), atoi(argv[3]), atoi(argv[4]));
  } else if (mode == "exh") {
    int D = atoi(argv[3]);
    int bestA = INF;
    vector<int> bestd;
    long long cnt = 0;
    int d[12];
    // enumerate delta in [0,D]^s; A >= max delta, so skip delta with max >= bestA
    long long tot = 1;
    for (int c = 0; c < s; c++) tot *= (D + 1);
    for (long long x = 0; x < tot; x++) {
      long long y = x;
      int mx = 0;
      for (int c = 0; c < s; c++) { d[c] = y % (D + 1); y /= (D + 1); mx = max(mx, d[c]); }
      if (mx >= bestA) continue;
      cnt++;
      int a = evalA(d, bestA);
      if (a < bestA) { bestA = a; bestd.assign(d, d + s); }
    }
    printf("EXH D=%d evaluated=%lld BEST A=%d d=", D, cnt, bestA);
    for (int v : bestd) printf("%d ", v);
    printf("\n");
  }
  return 0;
}
