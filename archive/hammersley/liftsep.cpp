// liftsep.cpp -- exact toroidal separation of a digital point set given by d generator matrices (R rows, m columns),
// written for the Hammersley lifts {(i/p^m, x_i)} of the residue sequences (coordinate 0 = reversal J, zero rows >= m).
// Input (same format as paper/scripts/sepx.cpp): "p d m R" then d*R rows of m entries C_c[n][k].
// Point i (index digits V_k = base-p digits of i): y_{c,n} = sum_k C_c[n][k] V_k mod p, X_c = sum_{n<R} y_{c,n} p^{-n-1}
// (truncation of digits n >= R moves a point by < p^{-R} per coordinate; for coordinate 0 nothing is truncated).
// Stored as 32-bit torus fixed point floor(X * 2^32).  Grid of G = floor(N^{1/d}) cells per axis, scan of offsets
// [-2,2]^d (or [-W,W]^d with argument W), so the minimum is exact whenever delta < W/G (reported).
// Output: c = delta * N^{1/d} (the normalisation of both papers), closest pair (i, j), |i - j|, and the minimum over
// pairs in a common "slab" (same first K0 digits of coordinate 0, i.e. same aligned block of p^{m-K0} indices) and
// over pairs in different slabs.  Usage: liftsep file [K0] [W] [brute] [nowrap0]
// nowrap0 = 1: coordinate 0 (the index i/N) measured without wrap-around (Euclidean), the others toroidal.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cmath>
#include <vector>
#include <cstring>
using namespace std;
typedef unsigned long long u64; typedef unsigned int u32;
int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: liftsep file [K0] [W] [brute]\n"); return 1; }
    FILE* f = fopen(argv[1], "r"); if (!f) return 1; int p, d, m, R;
    if (fscanf(f, "%d %d %d %d", &p, &d, &m, &R) != 4) return 1;
    vector<int> C(d * R * m);
    for (int c = 0; c < d; c++) for (int n = 0; n < R; n++) for (int k = 0; k < m; k++) if (fscanf(f, "%d", &C[(c * R + n) * m + k]) != 1) return 1;
    fclose(f);
    int K0 = argc > 2 ? atoi(argv[2]) : m / d; int W = argc > 3 ? atoi(argv[3]) : 2; bool brute = argc > 4 && atoi(argv[4]); bool nowrap0 = argc > 5 && atoi(argv[5]);
    u64 N = 1; for (int i = 0; i < m; i++) N *= p;
    u64 slabdiv = 1; for (int i = 0; i < m - K0; i++) slabdiv *= p;           // slab = i / p^{m-K0}
    long double PR = 1; for (int i = 0; i < R; i++) PR *= p;
    vector<int> S(d * R * m);
    for (int c = 0; c < d; c++) for (int n = 0; n < R; n++) { int acc = 0; for (int k = 0; k < m; k++) { acc = (acc + C[(c * R + n) * m + k]) % p; S[(c * R + n) * m + k] = acc; } }
    vector<u32> X((size_t)N * d); vector<int> y(d * R, 0), vd(m + 1, 0);
    vector<long double> pw(R); pw[R - 1] = 1; for (int n = R - 2; n >= 0; n--) pw[n] = pw[n + 1] * p;
    for (u64 v = 0; v < N; v++) {
        if (v > 0) { int k = 0; while (vd[k] == p - 1) { vd[k] = 0; k++; } vd[k]++;   // v -> v+1 adds col_k - sum_{k'<k}(p-1)col_k' = S_k
            for (int c = 0; c < d; c++) for (int n = 0; n < R; n++) { int t = y[c * R + n] + S[(c * R + n) * m + k]; if (t >= p) t -= p; y[c * R + n] = t; } }
        for (int c = 0; c < d; c++) { long double Xc = 0; for (int n = 0; n < R; n++) Xc += y[c * R + n] * pw[n];
            X[v * d + c] = (u32)floorl(Xc / PR * 4294967296.0L); }
    }
    auto dist2 = [&](u64 a, u64 b) { double s = 0; for (int c = 0; c < d; c++) { u32 q = X[a * d + c] - X[b * d + c]; u32 e = 0u - q; double t = (double)(q < e ? q : e); if (c == 0 && nowrap0) { long long z = (long long)X[a * d] - (long long)X[b * d]; t = (double)(z < 0 ? -z : z); } s += t * t; } return s; };
    double best = 1e300, bin = 1e300, bout = 1e300; u64 bi = 0, bj = 0;
    auto consider = [&](u64 a, u64 b) { double s = dist2(a, b); if (s < best) { best = s; bi = a; bj = b; }
        if (a / slabdiv == b / slabdiv) { if (s < bin) bin = s; } else { if (s < bout) bout = s; } };
    double G = 0; bool exact = true;
    if (brute) {
        for (u64 a = 0; a < N; a++) for (u64 b = a + 1; b < N; b++) consider(a, b);
    } else {
        u64 g = (u64)floor(pow((double)N, 1.0 / d) + 1e-9); if (g < (u64)(2 * W + 1)) g = 2 * W + 1; G = (double)g;
        u64 ncell = 1; for (int c = 0; c < d; c++) ncell *= g;
        vector<u32> cell(N), start(ncell + 1, 0), order(N);
        for (u64 v = 0; v < N; v++) { u64 id = 0; for (int c = 0; c < d; c++) id = id * g + (u64)(((unsigned __int128)X[v * d + c] * g) >> 32); cell[v] = (u32)id; start[id + 1]++; }
        for (u64 i = 0; i < ncell; i++) start[i + 1] += start[i];
        { vector<u32> pos(start.begin(), start.end() - 1); for (u64 v = 0; v < N; v++) order[pos[cell[v]]++] = (u32)v; }
        int span = 2 * W + 1, nofs = 1; for (int c = 0; c < d; c++) nofs *= span;
        vector<long long> cc(d);
        for (u64 ci = 0; ci < ncell; ci++) {
            if (start[ci] == start[ci + 1]) continue;
            u64 t = ci; for (int c = d - 1; c >= 0; c--) { cc[c] = (long long)(t % g); t /= g; }
            for (int o = 0; o < nofs; o++) {
                int oo = o; u64 cj = 0;
                for (int c = 0; c < d; c++) { int dd = oo % span - W; oo /= span; long long z = (cc[c] + dd + (long long)g) % (long long)g; cj = cj * g + (u64)z; }
                if (cj < ci) continue;
                for (u32 a = start[ci]; a < start[ci + 1]; a++) {
                    u32 b0 = (cj == ci) ? a + 1 : start[cj];
                    for (u32 b = b0; b < start[cj + 1]; b++) consider(order[a], order[b]);
                }
            }
        }
    }
    double scale = pow((double)p, (double)m / d), u = 4294967296.0;
    double delta = sqrt(best) / u, din = sqrt(bin) / u, dout = sqrt(bout) / u;
    double lim = brute ? 1e300 : W / G;
    exact = delta < lim;
    double err = sqrt((double)d) * 2.0 * (1.0 / (double)PR + 1.0 / u) * scale;
    u64 di = bi > bj ? bi - bj : bj - bi;
    printf("p=%d d=%d m=%d N=%llu c=%.6f exact=%s err<=%.1e pair=%llu,%llu |i-j|=%llu c_inslab=%s%.6f c_crossslab=%s%.6f K0=%d%s\n",
           p, d, m, N, delta * scale, exact ? "yes" : "NO", err, bi, bj, di,
           din < lim ? "" : ">=", (din < lim ? din : lim) * scale, dout < lim ? "" : ">=", (dout < lim ? dout : lim) * scale, K0, nowrap0 ? " nowrap0" : "");
    return 0;
}
