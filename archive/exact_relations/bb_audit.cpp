// bb_audit.cpp -- audit: independent branch-and-bound over digit-scaled residue scrambles (Remark rem:skelsearch), written from the definitions:
//   free data u_0..u_Kmax in (F_p^*)^s, global scale fixed by u_{0,0} = 1;
//   full-level-K responses D_K(l)[c][c'] = u_{c,K}^{-1} sum_{d<l} Lam[c][c'][d] u_{c',K-1-d}   (R-law, CHECKed by rlaw.py);
//   certificate LB_K = v3 lem:cert (j = 1): min over steps e (up to sign), carry lengths l_{c'} in [1,K] of
//   sum_c b_c^2 / p^2, b_c = max(0, min_t |e_c p + t| - 1), t in {sig, sig - p} (t = 0 if sig = 0).   All in INTEGERS (p^2 LB^2).
//   constraint: lambda_jit(Lambda_{u_n})^2 >= Jmin for every n (Lambda_u = {a in Z^s : u.a = 0 mod p}).
// mode max : exact max over all sequences of V = min_{1<=K<=Kmax} p^2 LB_K^2   (B&B, prune V <= incumbent)
// mode cnt T: number of prefixes (u_0..u_K) with p^2 LB_k^2 > T for all 1<=k<=K, per K   (no pruning other than the test)
// usage: bb7 lamfile max|cnt Kmax Jmin T timelimit
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <ctime>
#include <algorithm>
#include <string>
using namespace std;
int p, s, Dl, Kmax, Jmin, T; vector<int> Lam; vector<int> iv; double tl; clock_t t0; bool tout = false; long long nodes = 0;
vector<vector<int>> U; vector<long long> cnt; int best = -1; vector<vector<int>> bestU; bool modemax;
inline int L(int c, int cp, int d) { return Lam[(c * s + cp) * Dl + d]; }
int bsq(int e, int sig) { // integer b for coordinate with step e, response sig in [0,p)
    int m;
    if (sig == 0) m = abs(e * p); else m = min(abs(e * p + sig), abs(e * p + sig - p));
    return m > 1 ? (m - 1) * (m - 1) : 0;
}
// LB at level K given S[l][c][c'] (l=1..K) and u_K; returns min sum b^2, early exit if <= stop
int lbK(int K, const vector<int>& S, const vector<int>& uK, int stop) {
    vector<int> D((K + 1) * s * s);
    for (int l = 1; l <= K; l++) for (int c = 0; c < s; c++) { int f = iv[uK[c]]; for (int cp = 0; cp < s; cp++) D[(l * s + c) * s + cp] = (int)((long long)S[(l * s + c) * s + cp] * f % p); }
    int ne = 1; for (int i = 0; i < s; i++) ne *= 3; int mn = 1 << 30;
    vector<int> e(s), mv, ls;
    for (int ei = 0; ei < ne; ei++) {
        int t = ei, first = 0; for (int i = 0; i < s; i++) { e[i] = t % 3 - 1; t /= 3; if (e[i] && !first) first = e[i]; }
        if (first <= 0) continue;
        mv.clear(); for (int i = 0; i < s; i++) if (e[i]) mv.push_back(i);
        int nm = mv.size(); ls.assign(nm, 1);
        while (true) {
            int tot = 0;
            for (int c = 0; c < s; c++) { long long sg = 0; for (int i = 0; i < nm; i++) sg += e[mv[i]] * D[(ls[i] * s + c) * s + mv[i]]; sg %= p; if (sg < 0) sg += p; tot += bsq(e[c], (int)sg); }
            if (tot < mn) { mn = tot; if (mn <= stop) return mn; }
            int i = 0; while (i < nm && ls[i] == K) { ls[i] = 1; i++; } if (i == nm) break; ls[i]++;
        }
    }
    return mn;
}
int jit2(const vector<int>& u) { // lambda_jit^2 by box enumeration, complete once best <= B^2
    int bestj = 1 << 30;
    for (int B = 1;; B++) {
        vector<int> a(s, -B);
        while (true) {
            bool nz = false; long long dot = 0; int j = 0;
            for (int c = 0; c < s; c++) { if (a[c]) nz = true; dot += (long long)a[c] * u[c]; int x = abs(a[c]) - 1; if (x > 0) j += x * x; }
            if (nz && dot % p == 0 && j < bestj) bestj = j;
            int c = 0; while (c < s && a[c] == B) { a[c] = -B; c++; } if (c == s) break; a[c]++;
        }
        if (bestj <= B * B) return bestj;
    }
}
vector<vector<int>> cand, allu; bool relax = false; // cand: passing Jmin; allu: all of (F_p^*)^s (used at n=0,Kmax if relax)
void dfs(int K, int curmin) {
    if (tout) return;
    if ((++nodes & 4095) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tl) { tout = true; return; }
    if (K > Kmax) { if (modemax && curmin > best) { best = curmin; bestU = U; } return; }
    vector<int> S((K + 1) * s * s, 0);
    for (int c = 0; c < s; c++) for (int cp = 0; cp < s; cp++) { long long acc = 0; for (int l = 1; l <= K; l++) { int d = l - 1; acc = (acc + (long long)L(c, cp, d) * U[K - 1 - d][cp]) % p; S[(l * s + c) * s + cp] = (int)acc; } }
    vector<pair<int, int>> ch;
    int stop = modemax ? best : T;
    const vector<vector<int>>& CL = (relax && K == Kmax) ? allu : cand;
    for (int i = 0; i < (int)CL.size(); i++) {
        int v = lbK(K, S, CL[i], stop);
        if (v <= stop) continue;
        ch.push_back({v, i});
    }
    if (!modemax) cnt[K] += ch.size();
    sort(ch.begin(), ch.end(), [](const pair<int,int>& x, const pair<int,int>& y) { return x.first > y.first; });
    for (auto& pr : ch) {
        int nm = min(curmin, pr.first);
        if (modemax && nm <= best) continue;
        U[K] = CL[pr.second]; dfs(K + 1, nm); if (tout) return;
    }
}
int main(int argc, char** argv) {
    FILE* f = fopen(argv[1], "r"); if (fscanf(f, "%d %d %d", &p, &s, &Dl) != 3) return 1; Lam.resize(s * s * Dl);
    for (auto& x : Lam) if (fscanf(f, "%d", &x) != 1) return 1; fclose(f);
    modemax = string(argv[2]) == "max"; Kmax = atoi(argv[3]); Jmin = atoi(argv[4]); T = atoi(argv[5]); tl = atof(argv[6]);
    if (Kmax > Dl) { fprintf(stderr, "Kmax > D\n"); return 1; }
    iv.assign(p, 0); for (int x = 1; x < p; x++) for (int y = 1; y < p; y++) if (x * y % p == 1) iv[x] = y;
    int tot = 1; for (int c = 0; c < s; c++) tot *= (p - 1);
    int maxj = 0;
    for (int i = 0; i < tot; i++) { vector<int> u(s); int t = i; for (int c = 0; c < s; c++) { u[c] = t % (p - 1) + 1; t /= (p - 1); }
        int j = jit2(u); maxj = max(maxj, j); allu.push_back(u); if (j >= Jmin) cand.push_back(u); }
    relax = argc > 7 && string(argv[7]) == "relax";
    U.assign(Kmax + 1, vector<int>(s, 1)); cnt.assign(Kmax + 1, 0); t0 = clock();
    for (auto& u : (relax ? allu : cand)) { if (u[0] != 1) continue; U[0] = u; if (!modemax) cnt[0]++; dfs(1, 1 << 30); if (tout) break; }
    double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
    printf("%sp=%d s=%d Kmax=%d Jmin=%d (max over directions %d, %zu allowed u): ", relax ? "[Jmin only on u_1..u_{Kmax-1}] " : "", p, s, Kmax, Jmin, maxj, cand.size());
    if (modemax) { printf("max_u min_K p^2LB^2 = %d  -> LB = %.4f  %s nodes=%lld t=%.1fs\n", best, best >= 0 ? (best >= p * p ? 1.0 : __builtin_sqrt((double)best) / p) : -1.0, tout ? "(TIMEOUT: lower bound)" : "(EXACT)", nodes, el);
        if (best >= 0) { printf("  witness:"); for (auto& r : bestU) { printf(" ("); for (int c = 0; c < s; c++) printf("%d%s", r[c], c + 1 < s ? "," : ")"); } printf("\n"); } }
    else { printf("survivors with p^2LB_k^2 > %d for all k<=K:", T); for (int K = 0; K <= Kmax; K++) printf(" %lld", cnt[K]); printf(" %s t=%.1fs\n", tout ? "(TIMEOUT)" : "(EXACT)", el); }
}
