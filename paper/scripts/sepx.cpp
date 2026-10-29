// sepx.cpp -- independent exact toroidal separation of a digital prefix P_m (written without the code of the other kernels).
// input file: "p s m R" then s*R rows of m entries (C_c[n][k], n<R, k<m).
// Point v: digits y_{c,n} = sum_k C_c[n][k] v_k mod p, n<R; coordinate X_c = sum_n y_{c,n} p^{R-1-n}  (exact integer,
// truncation of the digits n>=R moves a point by < p^{-R}); stored as 32-bit torus fixed point x = floor(X * 2^32 / p^R).
// Cells: k = floor(m/s) digits per coordinate; every pair closer than one cell side p^{-k} lies in toroidally adjacent
// cells, so min over same+adjacent cells is exact whenever it is < p^{-k}.  Output: sep = delta * N^{1/s}, N = p^m.
// Error: |x - true| <= p^{-R} + 2^{-32} per coordinate -> reported with the bound on the sep error.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cmath>
#include <vector>
#include <algorithm>
using namespace std;
typedef unsigned long long u64; typedef unsigned int u32;
int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: sepx file\n"); return 1; }
    FILE* f = fopen(argv[1], "r"); int p, s, m, R;
    if (fscanf(f, "%d %d %d %d", &p, &s, &m, &R) != 4) return 1;
    vector<int> C(s * R * m);
    for (int c = 0; c < s; c++) for (int n = 0; n < R; n++) for (int k = 0; k < m; k++) fscanf(f, "%d", &C[(c * R + n) * m + k]);
    fclose(f);
    u64 PR = 1; for (int i = 0; i < R; i++) { PR *= p; if (PR > (1ULL << 62)) { fprintf(stderr, "R too big\n"); return 1; } }
    u64 N = 1; for (int i = 0; i < m; i++) N *= p;
    int kc = m / s; u64 side = 1; for (int i = 0; i < kc; i++) side *= p;   // cells per axis
    u64 ncell = 1; for (int c = 0; c < s; c++) ncell *= side;
    // prefix sums S_k = sum_{k'<=k} col_{k'} (mod p), per coordinate & digit
    vector<int> S(s * R * m);
    for (int c = 0; c < s; c++) for (int n = 0; n < R; n++) { int acc = 0; for (int k = 0; k < m; k++) { acc = (acc + C[(c * R + n) * m + k]) % p; S[(c * R + n) * m + k] = acc; } }
    vector<u32> X((size_t)N * s); vector<u32> cell(N);
    vector<int> y(s * R, 0), vd(m, 0);
    vector<u64> pw(R); pw[R - 1] = 1; for (int n = R - 2; n >= 0; n--) pw[n] = pw[n + 1] * p;
    for (u64 v = 0; v < N; v++) {
        if (v > 0) { int k = 0; while (vd[k] == p - 1) { vd[k] = 0; k++; } vd[k]++;
            for (int c = 0; c < s; c++) for (int n = 0; n < R; n++) { int t = y[c * R + n] + S[(c * R + n) * m + k]; if (t >= p) t -= p; y[c * R + n] = t; } }
        u64 cid = 0;
        for (int c = 0; c < s; c++) {
            u64 Xc = 0; for (int n = 0; n < R; n++) Xc += (u64)y[c * R + n] * pw[n];
            X[v * s + c] = (u32)(((unsigned __int128)Xc << 32) / PR);
            u64 cc = 0; for (int n = 0; n < kc; n++) cc = cc * p + y[c * R + n];
            cid = cid * side + cc;
        }
        cell[v] = (u32)cid;
    }
    // bucket by cell
    vector<u32> start(ncell + 1, 0), order(N);
    for (u64 v = 0; v < N; v++) start[cell[v] + 1]++;
    for (u64 i = 0; i < ncell; i++) start[i + 1] += start[i];
    { vector<u32> pos(start.begin(), start.end() - 1); for (u64 v = 0; v < N; v++) order[pos[cell[v]]++] = (u32)v; }
    double best = 1e300; u64 bi = 0, bj = 0;
    int nofs = 1; for (int c = 0; c < s; c++) nofs *= 3;
    vector<int> cc(s);
    for (u64 ci = 0; ci < ncell; ci++) {
        u64 t = ci; for (int c = s - 1; c >= 0; c--) { cc[c] = (int)(t % side); t /= side; }
        for (int o = 0; o < nofs; o++) {
            int oo = o; u64 cj = 0; bool self = true;
            for (int c = 0; c < s; c++) { int d = oo % 3 - 1; oo /= 3; if (d) self = false; long long z = ((long long)cc[c] + d + (long long)side) % (long long)side; cj = cj * side + (u64)z; }
            if (!self && cj < ci && side >= 3) continue;   // each unordered adjacent pair once
            for (u32 a = start[ci]; a < start[ci + 1]; a++) {
                u32 va = order[a];
                u32 b0 = self ? a + 1 : start[cj];
                for (u32 b = b0; b < start[cj + 1]; b++) {
                    u32 vb = order[b]; double d2 = 0;
                    for (int c = 0; c < s; c++) { u32 d = X[(u64)va * s + c] - X[(u64)vb * s + c]; u32 e = (u32)(0u - d); u32 mm = d < e ? d : e; double dd = (double)mm; d2 += dd * dd; }
                    if (d2 < best) { best = d2; bi = va; bj = vb; }
                }
            }
        }
    }
    double delta = sqrt(best) / 4294967296.0;
    double scale = pow((double)p, (double)m / s);
    double cellside = 1.0 / (double)side;
    double err = sqrt((double)s) * 2.0 * (1.0 / (double)PR + 1.0 / 4294967296.0) * scale;
    printf("p=%d s=%d m=%d N=%llu sep=%.6f  (exact if delta<cell side: %s; |err|<=%.1e) pair %llu %llu\n", p, s, m, N, delta * scale,
           delta < cellside ? "yes" : "NO, lower bound only", err, bi, bj);
    return 0;
}
