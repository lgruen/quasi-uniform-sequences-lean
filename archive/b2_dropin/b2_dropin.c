#include <stdint.h>
/* b2_dropin.c -- reference implementation of the drop-in table of Theorem thm:B2 (base-2 sequence, 32-bit direction
 * numbers, digit 0 = most significant bit).  The table M below is transcribed from Table tab:B2dir of
 * B2_dropin_table.tex; the function b2_point and the Gray-code note are the snippet printed there, unchanged.
 * Optional demo (not part of the snippet):  cc -O2 -std=c99 -DB2_DEMO -o b2demo b2_dropin/b2_dropin.c
 *   ./b2demo N      prints the first N points (x_0, x_1) as doubles
 *   ./b2demo words  prints the 64 table words, one row per coordinate (for comparison with b2build.py)
 */
const uint32_t M[2][32] = {
  {
    0x9cc0c000, 0x60000000, 0x2e606000, 0x1e606000, 0x09505000, 0x06606000, 0x02c84800, 0x01f87800,
    0x009c5c00, 0x00606000, 0x002e4e00, 0x001e7e00, 0x00095900, 0x00066600, 0x0002ca80, 0x0001f980,
    0x00009cc0, 0x00006000, 0x00002e60, 0x00001e60, 0x00000950, 0x00000660, 0x000002c8, 0x000001f8,
    0x0000009c, 0x00000060, 0x0000002e, 0x0000001e, 0x00000009, 0x00000006, 0x00000002, 0x00000001
  },
  {
    0xd1010001, 0x80000000, 0xe8808000, 0xa8808000, 0xdcc0c000, 0x88808000, 0xe6e0e000, 0xa2a0a000,
    0xd1d0d000, 0x80808000, 0xe868e800, 0xa828a800, 0xdc1cdc00, 0x88088800, 0xe606e600, 0xa202a200,
    0xd101d100, 0x80008000, 0xe8806880, 0xa8802880, 0xdcc01cc0, 0x88800880, 0xe6e006e0, 0xa2a002a0,
    0xd1d001d0, 0x80800080, 0xe8680068, 0xa8280028, 0xdc1c001c, 0x88080008, 0xe6060006, 0xa2020002
  }
};

extern const uint32_t M[2][32];      /* Table B2dir: M[c][k] */
/* coordinate c (0 or 1) of point i, as a 32-bit fraction */
uint32_t b2_point(int c, uint32_t i) {
    uint32_t r = 0;
    for (int k = 0; i != 0; k++, i >>= 1)
        if (i & 1) r ^= M[c][k];
    return r;                        /* x_c(i) = r * 2^-32 */
}
/* Gray code: x <- x ^ M[c][ctz(i+1)] gives the point with the next
   index in Gray-code order (the same set P_m in every block of 2^m) */

#ifdef B2_DEMO
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    if (argc > 1 && strcmp(argv[1], "words") == 0) {
        for (int c = 0; c < 2; c++) { for (int k = 0; k < 32; k++) printf("%08x%s", M[c][k], k < 31 ? " " : "\n"); }
        return 0;
    }
    unsigned long n = argc > 1 ? strtoul(argv[1], 0, 10) : 8;
    for (unsigned long i = 0; i < n; i++)
        printf("%.10f %.10f\n", b2_point(0, (uint32_t)i) * 0x1p-32, b2_point(1, (uint32_t)i) * 0x1p-32);
    return 0;
}
#endif
