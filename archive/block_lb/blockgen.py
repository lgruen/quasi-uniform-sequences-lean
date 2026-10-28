# blockgen.py -- search program (only its design loader is used by lb.py here).  w^L-self-similar ("block") residue scrambles that carry a FULL geometric-layer
# design (all s rows, as in [Gru26geo]) exactly at the super-levels P_{s L K}.
#
# Digits:  y_{c, L n + b}(V) = Res_{a_c}( V * phi_{c,b} * W'^{-(n+1)} dz ),   W' = w^L / theta,
#          phi_{c,b} a germ at a_c of valuation exactly L-1-b   (=> C_c = L_c P_{a_c}, lem:t0 => t = 0).
# Construction for L = s (thm:block):
#   phi_{c,1..s-1} = B_c^{-1} (u_i)_{i != c},  u_i = 1/(z - a_i),  beta_{i,c,b} = -v_i F_{s-1-b}[i][c]
#   phi_{c,0}      = ( (1/v_c) W'/(z-a_c) - W' sum_{b>=1} gamma_b phi_{c,b} ) / (1 + gamma_0 W'),
#                    gamma_b = -F_{s-1-b}[c][c]   (own design)
# Then on P_{s L K} (deg V < s L K), for every K >= 1 and every i (residue theorem):
#   y_{i,LK} = sum_{c} sum_{n=0}^{L-1} F_n[i][c] * y_{c, LK-1-n}       (exact design, carry depth n)
#
# usage: python blockgen.py p design m D outfile [netmax] [Kmax_design]
#   design in {rot2, geo3, file:<json>}; json = {"s":..,"a":[..],"v":[..],"theta":..,"F":[[[..]]..]}
import sys, itertools, json

def designs(name, p):
    if name == 'rot2':
        return dict(s=2, a=[0, 1], v=[1, 1], theta=1, F=[[[-1, 1], [-1, -1]], [[0, 0], [0, 0]]])
    if name == 'geo3':  # [Gru26geo]: r = M u + J v
        M = [[-1, -1, 1], [1, -1, -1], [-1, 1, -1]]; J = [[0, 0, -1], [-1, 0, 0], [0, -1, 0]]
        inv2 = pow(2, p - 2, p)
        return dict(s=3, a=[0, 2, 1], v=[inv2, inv2, p - 1], theta=1, F=[M, J, [[0] * 3 for _ in range(3)]])
    if name.startswith('file:'):
        return json.load(open(name[5:]))
    raise SystemExit('unknown design')

def build(p, d, D):
    s = d['s']; L = s; a = [x % p for x in d['a']]; v = [x % p for x in d['v']]; th = d['theta'] % p
    F = [[[x % p for x in row] for row in Fn] for Fn in d['F']]
    assert len(F) == L and len(set(a)) == s and all(v)
    inv = lambda x: pow(x % p, p - 2, p)
    nmax = (D - 1) // L; T = L * (nmax + 1) + 2
    def mul(A, B):
        r = [0] * T
        for i, x in enumerate(A[:T]):
            if x:
                for j, y in enumerate(B[:T - i]):
                    if y: r[i + j] = (r[i + j] + x * y) % p
        return r
    def sinv(A):
        r = [0] * T; i0 = inv(A[0]); r[0] = i0
        for n in range(1, T):
            r[n] = (-sum(A[j] * r[n - j] for j in range(1, n + 1)) * i0) % p
        return r
    def lin(c0, c1):  # c0 + c1 t
        r = [0] * T; r[0] = c0 % p; r[1] = c1 % p; return r
    def val(A):
        for i, x in enumerate(A):
            if x: return i
        return T
    C = []; info = []
    for c in range(s):
        # local series at t = z - a_c
        u = {i: sinv(lin(a[c] - a[i], 1)) for i in range(s) if i != c}
        What = [inv(th)] + [0] * (T - 1)
        for cc in range(s):
            if cc != c:
                for _ in range(L): What = mul(What, lin(a[c] - a[cc], 1))
        Wp = [0] * T  # W' = t^L * What
        for i in range(T - L): Wp[i + L] = What[i]
        g = [0] * T   # W'/(z-a_c) = t^{L-1} What
        for i in range(T - L + 1): g[i + L - 1] = What[i]
        others = [i for i in range(s) if i != c]
        # B_c[i][b], b = 1..s-1
        B = [[(-v[i] * F[L - 1 - b][i][c]) % p for b in range(1, L)] for i in others]
        # invert B over F_p
        n = len(others); Mx = [row[:] + [1 if r == k else 0 for k in range(n)] for r, row in enumerate(B)]
        for col in range(n):
            piv = next((r for r in range(col, n) if Mx[r][col]), None)
            if piv is None: raise SystemExit('B_c singular at c=%d' % c)
            Mx[col], Mx[piv] = Mx[piv], Mx[col]; iv = inv(Mx[col][col]); Mx[col] = [x * iv % p for x in Mx[col]]
            for r in range(n):
                if r != col and Mx[r][col]:
                    f = Mx[r][col]; Mx[r] = [(x - f * y) % p for x, y in zip(Mx[r], Mx[col])]
        Binv = [row[n:] for row in Mx]
        phi = [None] * L
        for bi in range(1, L):
            ser = [0] * T
            for k, i in enumerate(others):
                cf = Binv[bi - 1][k]
                if cf: ser = [(x + cf * y) % p for x, y in zip(ser, u[i])]
            phi[bi] = ser
        gam = [(-F[L - 1 - b][c][c]) % p for b in range(L)]
        num = [x * inv(v[c]) % p for x in g]
        for b in range(1, L):
            if gam[b]:
                t2 = mul(Wp, phi[b]); num = [(x - gam[b] * y) % p for x, y in zip(num, t2)]
        den = [(x * gam[0]) % p for x in Wp]; den[0] = (den[0] + 1) % p
        phi[0] = mul(num, sinv(den))
        vals = [val(ph) for ph in phi]
        info.append(vals)
        if vals != [L - 1 - b for b in range(L)]:
            raise SystemExit('valuation check FAILED at c=%d: %s' % (c, vals))
        # generator matrix rows N < D, columns k < Dcols (we need k < m only; caller trims)
        Cc = []
        Winvp = [1] + [0] * (T - 1); Wi = sinv(What)
        for nn in range(nmax + 1):
            Winvp = mul(Winvp, Wi)  # What^{-(nn+1)}
            for b in range(L):
                N = L * nn + b
                if N >= D: break
                X = mul(phi[b], Winvp); e = L * (nn + 1) - 1
                Cc.append(X[:e + 1])  # keep coefficients up to t^e; entry(k) computed later
        C.append(Cc)
    return s, L, a, v, F, C

def entries(p, a_c, Xrow, m):
    # [t^e] (a_c + t)^k X(t) for k < m, e = len(Xrow)-1
    e = len(Xrow) - 1; out = []
    from math import comb
    for k in range(m):
        tot = 0
        for j in range(min(k, e) + 1):
            tot += comb(k, j) * pow(a_c, k - j, p) * Xrow[e - j]
        out.append(tot % p)
    return out

def rank(rows, p):
    M = [r[:] for r in rows]; rk = 0; ncol = len(M[0]) if M else 0
    for col in range(ncol):
        piv = next((r for r in range(rk, len(M)) if M[r][col]), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]; iv = pow(M[rk][col], p - 2, p); M[rk] = [x * iv % p for x in M[rk]]
        for r in range(len(M)):
            if r != rk and M[r][col]:
                f = M[r][col]; M[r] = [(x - f * y) % p for x, y in zip(M[r], M[rk])]
        rk += 1
    return rk

def main():
    p = int(sys.argv[1]); dname = sys.argv[2]; m = int(sys.argv[3]); D = int(sys.argv[4]); out = sys.argv[5]
    netmax = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    d = designs(dname, p)
    s, L, a, v, F, Cser = build(p, d, max(D, m + 1))
    Cm = [[entries(p, a[c], Cser[c][N], max(m, netmax)) for N in range(len(Cser[c]))] for c in range(s)]
    print('built: p=%d s=%d L=%d places=%s v=%s; valuations OK' % (p, s, L, a, v))
    # design identity on the monomial basis, every K with s L K <= max(m, netmax)
    mm = max(m, netmax); bad = 0; Ks = []
    for K in range(1, mm // (s * L) + 1):
        Ks.append(K)
        for i in range(s):
            for k in range(s * L * K):
                lhs = Cm[i][L * K][k]
                rhs = sum(F[n][i][c] * Cm[c][L * K - 1 - n][k] for c in range(s) for n in range(L)) % p
                if (lhs - rhs) % p: bad += 1
    print('design identity y_{i,LK} = sum F_n[i][c] y_{c,LK-1-n} on deg V < sLK: K in %s, failures = %d' % (Ks, bad))
    # (0,m,s)-net property for m <= netmax
    if netmax:
        tot = 0; fail = 0
        for mm2 in range(1, netmax + 1):
            for comp in itertools.product(range(mm2 + 1), repeat=s):
                if sum(comp) != mm2: continue
                rows = [Cm[c][n][:mm2] for c in range(s) for n in range(comp[c])]
                tot += 1
                if rank(rows, p) < mm2: fail += 1
        print('net property m <= %d: %d box matrices, %d singular' % (netmax, tot, fail))
    with open(out, 'w') as f:
        f.write('%d %d %d %d\n' % (p, s, m, D))
        for c in range(s):
            for N in range(D):
                f.write(' '.join(map(str, Cm[c][N][:m])) + '\n')

if __name__ == '__main__':
    main()
