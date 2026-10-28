// bb_search.cpp (search program) -- branch-and-bound over DIGIT-SCALED U (= every digital frame scramble with an exact pure U-skeleton
// at every level m = sK-1, a lemma of the research notes; Remark rem:skelsearch).  The free data are the per-level vectors u_n in (F_p^*)^s
// (u_n = check vector of the skeleton at m = s(n+1)-1, up to scale; mu_{c,n} = 1/u_{c,n} is the digit scaling).
// Full level K response (exact, validated by lawU.py):  D_K(l)[c][c'] = u_{c,K}^{-1} sum_{d<l} Lam[c][c'][d] u_{c',K-1-d}.
// Certificate at full level K: v3 lem:cert with j = 1 (one-digit neighbour bound) from the actual responses D_K(l), l<=K.
// Mode "bb":   exact maximisation of  min_{1<=K<=Kmax} LB_K  over ALL sequences (u_0..u_Kmax)   [EXHAUSTIVE B&B]
//              optional constraint: lambda_jit(Lambda_{u_n})^2 >= J  for every n (U-quality at the m = -1 levels).
// Mode "count": number of prefixes (u_0..u_K) with LB_k >= tau for all k <= K, per K (global scale fixed: u_{0,0}=1).
// usage: dsu_bb LAMFILE mode Kmax [tau|-] [Jmin] [timelimit_s]
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <vector>
#include <ctime>
#include <algorithm>
using namespace std;
int p, s, D; vector<int> Lam; // Lam[(c*s+cp)*D+d]
int Kmax; double tau; int Jmin; double tlimit; clock_t t0;
vector<int> invt;
vector<vector<int>> U; // U[n][c]
vector<int> jit2; // for s<=3: lambda_jit^2 of direction index
long long nodes = 0; bool timeout = false;
inline double f1(int e, int sig) { // sig in [0,p)
    int best;
    if (sig == 0) best = abs(e * p); else best = min(abs(e * p + sig), abs(e * p + sig - p));
    double b = best - 1; if (b < 0) b = 0; return b / p;
}
// responses for level K: R[(l-1)][c][cp]
void responses(int K, vector<int>& R) {
    R.assign(K * s * s, 0);
    for (int c = 0; c < s; c++) {
        int mu = invt[U[K][c]];
        for (int cp = 0; cp < s; cp++) {
            long long acc = 0;
            for (int l = 1; l <= K; l++) {
                int d = l - 1;
                acc = (acc + (long long)Lam[(c * s + cp) * D + d] * U[K - 1 - d][cp]) % p;
                R[((l - 1) * s + c) * s + cp] = (int)(acc * mu % p);
            }
        }
    }
}
double LBlevel(int K, double stopbelow) {
    vector<int> R; responses(K, R);
    double best = 1e9;
    int ne = 1; for (int i = 0; i < s; i++) ne *= 3;
    vector<int> e(s), mv, ls;
    for (int ei = 0; ei < ne; ei++) {
        int t = ei; bool any = false; int first = 0;
        for (int i = 0; i < s; i++) { e[i] = t % 3 - 1; t /= 3; if (e[i] && !first) first = e[i]; if (e[i]) any = true; }
        if (!any || first < 0) continue;
        mv.clear(); for (int i = 0; i < s; i++) if (e[i]) mv.push_back(i);
        int nm = mv.size(); long long ncomb = 1; for (int i = 0; i < nm; i++) ncomb *= K;
        ls.assign(nm, 0);
        for (long long cmb = 0; cmb < ncomb; cmb++) {
            long long q = cmb; for (int i = 0; i < nm; i++) { ls[i] = q % K; q /= K; }
            double tot = 0;
            for (int c = 0; c < s; c++) {
                long long sig = 0;
                for (int i = 0; i < nm; i++) sig += (long long)e[mv[i]] * R[(ls[i] * s + c) * s + mv[i]];
                sig %= p; if (sig < 0) sig += p;
                double f = f1(e[c], (int)sig); tot += f * f;
            }
            if (tot < best) { best = tot; if (sqrt(best) < stopbelow) return sqrt(best); }
        }
    }
    return min(1.0, sqrt(best));
}
int dirindex(const vector<int>& u) { // normalise first coordinate to 1
    int iv = invt[u[0]]; int idx = 0;
    for (int c = 1; c < s; c++) idx = idx * p + (int)((long long)u[c] * iv % p);
    return idx;
}
void computeJit() {
    int nd = 1; for (int c = 1; c < s; c++) nd *= p;
    jit2.assign(nd, 0);
    for (int idx = 0; idx < nd; idx++) {
        vector<int> v(s); v[0] = 1; int t = idx; for (int c = s - 1; c >= 1; c--) { v[c] = t % p; t /= p; }
        bool zero = false; for (int c = 1; c < s; c++) if (!v[c]) zero = true;
        if (zero) { jit2[idx] = -1; continue; }
        int best = 1 << 30;
        for (int B = 1;; B++) {
            vector<int> a(s, -B);
            while (true) {
                bool nz = false; long long dot = 0; int j = 0;
                for (int c = 0; c < s; c++) { if (a[c]) nz = true; dot += (long long)a[c] * v[c]; int x = abs(a[c]) - 1; if (x > 0) j += x * x; }
                if (nz && ((dot % p) + p) % p == 0 && j < best) best = j;
                int c = 0; while (c < s && a[c] == B) { a[c] = -B; c++; } if (c == s) break; a[c]++;
            }
            if (best <= B * B) break;
        }
        jit2[idx] = best;
    }
}
double bestval = -1; vector<vector<int>> bestU;
vector<long long> cnt;
void dfs(int K, double curmin, bool bb) {
    if (timeout) return;
    if ((++nodes & 1023) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tlimit) { timeout = true; return; }
    if (K > Kmax) { if (bb && curmin > bestval) { bestval = curmin; bestU = U; } return; }
    // enumerate u_K
    int tot = 1; for (int c = 0; c < s; c++) tot *= (p - 1);
    vector<pair<double, int>> ch;
    for (int i = 0; i < tot; i++) {
        int t = i; for (int c = 0; c < s; c++) { U[K][c] = t % (p - 1) + 1; t /= (p - 1); }
        if (Jmin > 0) { int j = jit2[dirindex(U[K])]; if (j < Jmin) continue; }
        double thr = bb ? max(bestval, -1.0) : tau;
        double lb = (K == 0) ? 1.0 : LBlevel(K, bb ? bestval : tau);
        if (bb) { if (lb <= bestval) continue; } else { if (lb < tau) continue; }
        ch.push_back({lb, i});
        (void)thr;
    }
    if (!bb) cnt[K] += ch.size();
    sort(ch.begin(), ch.end(), [](const pair<double,int>& a, const pair<double,int>& b){ return a.first > b.first; });
    for (auto& pr : ch) {
        int t = pr.second; for (int c = 0; c < s; c++) { U[K][c] = t % (p - 1) + 1; t /= (p - 1); }
        double nm = min(curmin, pr.first);
        if (bb && nm <= bestval) continue;
        dfs(K + 1, nm, bb);
        if (timeout) return;
    }
}
int main(int argc, char** argv) {
    FILE* f = fopen(argv[1], "r"); fscanf(f, "%d %d %d", &p, &s, &D); Lam.resize(s * s * D);
    for (int i = 0; i < s * s * D; i++) fscanf(f, "%d", &Lam[i]); fclose(f);
    bool bb = string(argv[2]) == "bb"; Kmax = atoi(argv[3]);
    tau = (argc > 4 && argv[4][0] != '-') ? atof(argv[4]) : 0; Jmin = argc > 5 ? atoi(argv[5]) : 0; tlimit = argc > 6 ? atof(argv[6]) : 50;
    invt.assign(p, 0); for (int x = 1; x < p; x++) for (int y = 1; y < p; y++) if (x * y % p == 1) invt[x] = y;
    if (Jmin > 0) computeJit();
    U.assign(Kmax + 1, vector<int>(s, 1)); cnt.assign(Kmax + 2, 0); t0 = clock();
    // u_0: fix global scale u_{0,0} = 1
    int tot0 = 1; for (int c = 1; c < s; c++) tot0 *= (p - 1);
    for (int i = 0; i < tot0; i++) {
        U[0][0] = 1; int t = i; for (int c = 1; c < s; c++) { U[0][c] = t % (p - 1) + 1; t /= (p - 1); }
        if (Jmin > 0 && jit2[dirindex(U[0])] < Jmin) continue;
        if (!bb) cnt[0]++;
        dfs(1, 1.0, bb);
        if (timeout) break;
    }
    double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
    if (bb) {
        printf("p=%d s=%d Kmax=%d Jmin=%d: max over all u-sequences of min_{K<=Kmax} LB_K = %.4f %s nodes=%lld time=%.1fs\n", p, s, Kmax, Jmin, bestval, timeout ? "(TIMEOUT: lower bound on the max)" : "(exact)", nodes, el);
        if (bestval > 0) { printf("  witness u_n (n=0..Kmax):"); for (auto& r : bestU) { printf(" ("); for (int c = 0; c < s; c++) printf("%d%s", r[c], c + 1 < s ? "," : ""); printf(")"); } printf("\n"); }
    } else {
        printf("p=%d s=%d tau=%.3f Jmin=%d: surviving prefixes per K:", p, s, tau, Jmin);
        for (int K = 0; K <= Kmax; K++) printf(" %lld", cnt[K]);
        printf("%s time=%.1fs\n", timeout ? " (TIMEOUT)" : "", el);
    }
}
