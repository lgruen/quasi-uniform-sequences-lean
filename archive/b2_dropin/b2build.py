# Independent build of Theorem B2 generator matrices over F_2 (audit code, written from the series of Theorem thm:B2; shares no code with the program that produced the table).
# Polynomials over F_2 as python ints (bit n = coeff of x^n), truncated mod x^PREC.
import sys
PREC = 80
MASK = (1 << PREC) - 1
def mul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a = (a << 1) & MASK; b >>= 1
    return r
u = 0
k = 1
while k < PREC: u |= 1 << k; k <<= 1   # u = sum_{k>=0} x^{2^k}
assert mul(u, u) ^ u == 2            # u^2 + u = x
one = 1
g0 = mul(1 | 2, 1 ^ u)               # (1+x)(1+u)
NR = 64; NC = 64
def coef(s, n): return (s >> n) & 1
# L1[n,k] = [x^n](1+x)(1+u)u^k ;  L2[n,k] = [x^{n+1}] u^{k+1}
L1 = [[0]*NC for _ in range(NR)]; L2 = [[0]*NC for _ in range(NR)]
p = 1
for kk in range(NC):
    s = mul(g0, p)
    for n in range(NR): L1[n][kk] = coef(s, n)
    p = mul(p, u)   # now u^{kk+1}
    for n in range(NR): L2[n][kk] = coef(p, n+1)
for n in range(NR):
    assert L1[n][n] == 1 and L2[n][n] == 1
    assert all(L1[n][k] == 0 and L2[n][k] == 0 for k in range(n+1, NC))
# Pascal P[j,k] = C(k,j) mod 2
P = [[1 if (j & k) == j else 0 for k in range(NC)] for j in range(NC)]
C0 = L1
C1 = [[sum(L2[n][j]*P[j][k] for j in range(NC)) & 1 for k in range(NC)] for n in range(NR)]
# cross-check C1 against the form [x^n] (u/x)(1+u)^k
q = 1
for kk in range(NC):
    s = mul(u, q)  # u (1+u)^k
    for n in range(NR): assert C1[n][kk] == coef(s, n+1)
    q = mul(q, 1 ^ u)
# columns as 64-bit ints, digit 0 = MSB (bit 63)
cols = [[sum(C[n][k] << (63-n) for n in range(64)) for k in range(64)] for C in (C0, C1)]
with open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'b2_cols_64bit.txt'), 'w') as f:
    for c in cols: f.write(' '.join('%016x' % v for v in c) + '\n')
# 32-bit table as printed in Table tab:B2dir
M0 = """9cc0c000 60000000 2e606000 1e606000 09505000 06606000 02c84800 01f87800 009c5c00 00606000 002e4e00 001e7e00
      00095900 00066600 0002ca80 0001f980 00009cc0 00006000 00002e60 00001e60 00000950 00000660 000002c8 000001f8
      0000009c 00000060 0000002e 0000001e 00000009 00000006 00000002 00000001""".split()
M1 = """d1010001 80000000 e8808000 a8808000 dcc0c000 88808000 e6e0e000 a2a0a000 d1d0d000 80808000 e868e800 a828a800
      dc1cdc00 88088800 e606e600 a202a200 d101d100 80008000 e8806880 a8802880 dcc01cc0 88800880 e6e006e0 a2a002a0
      d1d001d0 80800080 e8680068 a8280028 dc1c001c 88080008 e6060006 a2020002""".split()
for name, M, cc in (('M_0', M0, cols[0]), ('M_1', M1, cols[1])):
    mine = ['%08x' % (v >> 32) for v in cc[:32]]
    bad = [k for k in range(32) if mine[k] != M[k]]
    print(name, 'mismatches at columns:', bad, 'first entries mine:', mine[:4])
# t-value: digital sequence t=0 iff for all m, a+b=m: rows 0..a-1 of C0 and 0..b-1 of C1 restricted to columns <m independent
def rank(rows):
    rows = list(rows); r = 0
    basis = {}
    for v in rows:
        while v:
            h = v.bit_length()-1
            if h in basis: v ^= basis[h]
            else: basis[h] = v; r += 1; break
    return r
rowint = [[sum(C[n][k] << k for k in range(64)) for n in range(64)] for C in (C0, C1)]
bad = []
for m in range(1, 49):
    mk = (1 << m) - 1
    for a in range(m+1):
        rs = [rowint[0][n] & mk for n in range(a)] + [rowint[1][n] & mk for n in range(m-a)]
        if rank(rs) < m: bad.append((m, a))
print('t=0 failures for m<=48:', bad)
