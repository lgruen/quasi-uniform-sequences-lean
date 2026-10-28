/* b2_check.c -- checks the two statements of B2_dropin_table.tex about the point sets made with the table and the snippet
 * (b2_dropin.c, included unchanged):
 *   (1) a loop over all elementary intervals: P_m (the first 2^m points) has exactly one point in every box
 *       [a 2^-k, (a+1) 2^-k) x [b 2^-(m-k), (b+1) 2^-(m-k)), k = 0..m, for every m <= MNET (default 14), i.e. P_m is a
 *       (0,m,2)-net;
 *   (2) a brute-force toroidal minimum distance over all pairs of P_m, m = 2, 4, ..., MSEP (default 12), exact in integer
 *       arithmetic on the 32-bit coordinates; printed as sep(P_m) = delta(P_m) * 2^(m/2).
 * Build and run from the archive root:  cc -O2 -std=c99 -o bin/b2check b2_dropin/b2_check.c -lm && ./bin/b2check [MNET MSEP]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "b2_dropin.c"

int main(int argc, char **argv) {
    int mnet = argc > 1 ? atoi(argv[1]) : 14, msep = argc > 2 ? atoi(argv[2]) : 12, bad = 0;
    int mmax = mnet > msep ? mnet : msep;
    uint32_t n = 1u << mmax, *x = malloc(n * sizeof *x), *y = malloc(n * sizeof *y);
    for (uint32_t i = 0; i < n; i++) { x[i] = b2_point(0, i); y[i] = b2_point(1, i); }
    unsigned char *cnt = malloc((size_t)1 << mnet);
    for (int m = 1; m <= mnet; m++) {
        int ok = 1;
        for (int k = 0; k <= m; k++) {
            memset(cnt, 0, (size_t)1 << m);
            for (uint32_t i = 0; i < (1u << m); i++) {
                uint32_t a = k ? x[i] >> (32 - k) : 0, b = (m - k) ? y[i] >> (32 - (m - k)) : 0;
                cnt[(a << (m - k)) | b]++;
            }
            for (uint32_t j = 0; j < (1u << m); j++) if (cnt[j] != 1) ok = 0;
        }
        if (!ok) bad++;
        printf("m=%2d: every elementary interval of volume 2^-%d holds exactly one point of P_m: %s\n", m, m, ok ? "yes" : "NO");
    }
    for (int m = 2; m <= msep; m += 2) {
        uint64_t best = UINT64_MAX; uint32_t N = 1u << m;
        for (uint32_t i = 0; i < N; i++) for (uint32_t j = i + 1; j < N; j++) {
            uint32_t dx = x[i] - x[j], dy = y[i] - y[j];          /* mod 2^32 */
            if (dx > 0x80000000u) dx = -dx;                          /* toroidal: min(d, 2^32 - d) */
            if (dy > 0x80000000u) dy = -dy;
            uint64_t d2 = (uint64_t)dx * dx + (uint64_t)dy * dy;     /* dx, dy <= 2^31: exact, < 2^63 */
            if (d2 < best) best = d2;
        }
        /* delta^2 = best * 2^-64 exactly; sep^2 = delta^2 * 2^m */
        double sep = sqrt(ldexp((double)best, m - 64));
        printf("m=%2d: sep(P_m) = %.4f  (brute force over all %u pairs, toroidal)\n", m, sep, N * (N - 1) / 2);
    }
    printf(bad ? "NET CHECK FAILED\n" : "ALL OK\n");
    return bad != 0;
}
