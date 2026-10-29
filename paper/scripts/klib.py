"""klib.py -- field arithmetic (prime fields and F_4) and Kummer-type frames of the development version; make_figs.py
uses the field class (F_4) for the series of fig:automaton.
Places a_c in F_q^* = mu_{q-1}, s = q - 1, index place infinity, cell uniformizer w = z^s - 1.
Local root at a_c: z = a_c * tau(x), tau^s = 1 + x, tau^{-1} = prod_{i>=0} (1 + x^{q^i}) (coefficients 0/1).
Member: per place c a multiplier g_c = N_c(tau)/D_c(tau), N_c, D_c lists of x-polynomials indexed by the tau power.
Generator matrices C_c[n][k] = [x^n] g_c(x) (a_c tau(x))^k  (row n = digit n of coordinate c, column k <-> z^k).
Fields: prime q (ints mod q) and F_4 with codes 0,1,2,3 <-> 0,1,w,w^2 (code b0+2b1 <-> b0 + b1 w; addition = XOR).
Unchanged copy of the development library.
"""
import numpy as np

class Field:
    def __init__(self, q):
        self.q = q
        if q in (2, 3, 5, 7, 11, 13):
            self.p = q; self.r = 1
            a = np.arange(q)
            self.ADD = (a[:, None] + a[None, :]) % q; self.MUL = (a[:, None] * a[None, :]) % q
            self.NEG = (-a) % q
        elif q == 4:
            self.p = 2; self.r = 2
            a = np.arange(4); self.ADD = a[:, None] ^ a[None, :]
            # codes: 1 = 1, 2 = w, 3 = w^2 = 1 + w ; log: 1->0, 2->1, 3->2
            lg = {1: 0, 2: 1, 3: 2}; ex = [1, 2, 3]
            M = np.zeros((4, 4), np.int64)
            for x in (1, 2, 3):
                for y in (1, 2, 3): M[x, y] = ex[(lg[x] + lg[y]) % 3]
            self.MUL = M; self.NEG = a.copy()
        else:
            raise ValueError(q)
        self.INV = np.zeros(q, np.int64)
        for x in range(1, q):
            for y in range(1, q):
                if self.MUL[x, y] == 1: self.INV[x] = y
        # primitive element
        for g in range(2, q) if q > 2 else [1]:
            seen = set(); v = 1
            for _ in range(q - 1): v = int(self.MUL[v, g]); seen.add(v)
            if len(seen) == q - 1: self.gen = g; break
        if q == 2: self.gen = 1
    def add(self, a, b): return int(self.ADD[a, b])
    def mul(self, a, b): return int(self.MUL[a, b])
    def neg(self, a): return int(self.NEG[a])
    def sub(self, a, b): return int(self.ADD[a, self.NEG[b]])
    def inv(self, a): return int(self.INV[a])
    def pw(self, a, k):
        v = 1
        for _ in range(k % (self.q - 1) if a else k): v = self.mul(v, a)
        return v if (a or k == 0) else 0
    def vadd(self, a, b):
        n = max(len(a), len(b)); A = np.zeros(n, np.int64); B = np.zeros(n, np.int64)
        A[:len(a)] = a; B[:len(b)] = b
        return self.ADD[A, B]
    def vneg(self, a): return self.NEG[np.asarray(a, np.int64)]
    def vscal(self, c, a): return self.MUL[c, np.asarray(a, np.int64)]
    def conv(self, a, b, L=None):
        a = np.asarray(a, np.int64); b = np.asarray(b, np.int64)
        if len(a) == 0 or len(b) == 0: return np.zeros(0 if L is None else L, np.int64)
        if L is not None: a = a[:L]; b = b[:L]
        n = len(a) + len(b) - 1
        if self.r == 1:
            out = np.convolve(a, b) % self.q
        else:
            out = np.zeros(n, np.int64)
            for i in np.nonzero(a)[0]:
                out[i:i + len(b)] ^= self.MUL[a[i], b]
        if L is not None:
            o = np.zeros(L, np.int64); m = min(L, n); o[:m] = out[:m]; return o
        return out

def trim(a):
    a = np.asarray(a, np.int64); nz = np.nonzero(a)[0]
    return a[:nz[-1] + 1] if len(nz) else np.zeros(0, np.int64)

def sinv(F, a, L):
    """power-series inverse mod x^L (a[0] != 0), O(L^2) recurrence."""
    a = np.asarray(a, np.int64); A = np.zeros(L, np.int64); A[:min(L, len(a))] = a[:L]
    i0 = F.inv(int(A[0])); m0 = F.neg(i0); out = np.zeros(L, np.int64); out[0] = i0
    nzA = np.nonzero(A[1:])[0] + 1
    for n in range(1, L):
        ks = nzA[nzA <= n]
        if len(ks) == 0: continue
        pr = F.MUL[A[ks], out[n - ks]]
        v = int(pr.sum() % F.q) if F.r == 1 else int(np.bitwise_xor.reduce(pr))
        out[n] = F.mul(m0, v)
    return out

def tau_inv_series(F, L):
    """prod_{i>=0}(1 + x^{q^i}) mod x^L: 1 at n whose base-q digits are all in {0,1}."""
    t = np.zeros(L, np.int64)
    for n in range(L):
        m = n; ok = True
        while m:
            if m % F.q > 1: ok = False; break
            m //= F.q
        t[n] = 1 if ok else 0
    return t

class Member:
    """Gams[c] = (N, D): lists of x-polynomials (lists of field ints) indexed by tau power; places[c] in F_q^*."""
    def __init__(self, F, places, Gams, L=200):
        self.F = F; self.q = F.q; self.s = F.q - 1; self.places = list(places); self.Gams = Gams
        self.set_L(L)
    def set_L(self, L):
        F = self.F; self.L = L
        self.tinv = tau_inv_series(F, L); self.tau = sinv(F, self.tinv, L)
        self.taupow = [np.eye(1, L, 0, np.int64)[0]]
        for b in range(1, 2 * self.s + 2): self.taupow.append(F.conv(self.taupow[-1], self.tau, L))
        self.tinvpow = [np.eye(1, L, 0, np.int64)[0]]
        for b in range(1, self.s + 1): self.tinvpow.append(F.conv(self.tinvpow[-1], self.tinv, L))
        self.g = []
        for (N, D) in self.Gams:
            self.g.append(F.conv(self.eval_tau(N), sinv(F, self.eval_tau(D), L), L))
    def eval_tau(self, P):
        F = self.F; out = np.zeros(self.L, np.int64)
        for k, poly in enumerate(P):
            poly = trim(poly)
            if len(poly) == 0: continue
            out = F.vadd(out, F.conv(poly, self.taupow[k], self.L))
        return out
    def gen_matrices(self, rows, cols):
        F = self.F; Cs = []
        assert rows <= self.L
        for c, a in enumerate(self.places):
            C = np.zeros((rows, cols), np.int64); ser = self.g[c].copy()
            az = F.vscal(a, self.tau)
            for k in range(cols):
                C[:, k] = ser[:rows]; ser = F.conv(ser, az, self.L)
            Cs.append(C)
        return Cs
    def Sigma_G(self):
        """series Sigma[c][b] = g_c a_c^b tau^b and G[b][c] = -a_c^{-b} tau^{-b} / g_c."""
        F = self.F; s = self.s; L = self.L
        Sig = [[F.vscal(F.pw(a, b), F.conv(self.g[c], self.taupow[b], L)) for b in range(s)] for c, a in enumerate(self.places)]
        G = [[None] * s for _ in range(s)]
        for c, a in enumerate(self.places):
            ig = sinv(F, self.g[c], L)
            for b in range(s):
                G[b][c] = F.vscal(F.neg(F.pw(F.inv(a), b)), F.conv(self.tinvpow[b], ig, L))
        return Sig, G
    def series_law(self, j, Lmax):
        """D[l-1][src][c][i] = [x^{l+i}] (Sigma_{>i} G/(1-x))[c][src], l = 1..Lmax (needs L > Lmax + j)."""
        F = self.F; s = self.s; Sig, G = self.Sigma_G(); L = self.L
        assert L > Lmax + j + 1
        Gh = [[np.cumsum(G[b][c]) % F.q if F.r == 1 else np.bitwise_xor.accumulate(G[b][c]) for c in range(s)] for b in range(s)]
        out = np.zeros((Lmax, s, s, j), np.int64)
        for src in range(s):
            for c in range(s):
                for i in range(j):
                    acc = np.zeros(Lmax, np.int64)
                    if c == src: acc[:] = 1
                    for b in range(s):
                        for a_ in range(i + 1):
                            co = int(Sig[c][b][a_])
                            if co == 0: continue
                            # [x^{l+i-a}] Gh[b][src], l = 1..Lmax
                            seg = Gh[b][src][1 + i - a_: Lmax + 1 + i - a_]
                            acc = F.ADD[acc, F.NEG[F.MUL[co, seg]]]
                    out[:, src, c, i] = acc
        return out

def rank_F(F, M):
    M = np.array(M, np.int64) % (F.q if F.r == 1 else 4); M = M.copy(); r = 0; rows, cols = M.shape
    for col in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, col]: piv = i; break
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]; iv = F.inv(int(M[r, col])); M[r] = F.MUL[iv, M[r]]
        for i in range(rows):
            if i != r and M[i, col]:
                M[i] = F.ADD[M[i], F.NEG[F.MUL[int(M[i, col]), M[r]]]]
        r += 1
        if r == rows: break
    return r

def solve_F(F, A, b):
    """solve A x = b over F (A n x m), return one solution or None."""
    A = np.array(A, np.int64); b = np.array(b, np.int64); n, m = A.shape
    M = np.concatenate([A, b[:, None]], 1); r = 0; pivs = []
    for col in range(m):
        piv = None
        for i in range(r, n):
            if M[i, col]: piv = i; break
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]; iv = F.inv(int(M[r, col])); M[r] = F.MUL[iv, M[r]]
        nzr = np.nonzero(M[:, col])[0]
        for i in nzr:
            if i != r: M[i] = F.ADD[M[i], F.NEG[F.MUL[int(M[i, col]), M[r]]]]
        pivs.append(col); r += 1
        if r == n: break
    if np.any(M[r:, m]): return None
    x = np.zeros(m, np.int64)
    for i, col in enumerate(pivs): x[col] = M[i, m]
    return x

def t_value_seq(F, Cs, mmax):
    """exact t-check of the prefix nets: for each m <= mmax, max over compositions of the rank deficit. returns list t(m)."""
    import itertools
    s = len(Cs); ts = []
    for m in range(1, mmax + 1):
        t = m  # audit fix (KUMMER1_AUDIT 5): if every k >= 1 fails, t = m (was wrongly 0)
        for k in range(m, 0, -1):
            ok = True
            for comp in itertools.product(range(k + 1), repeat=s - 1):
                if sum(comp) > k: continue
                d = list(comp) + [k - sum(comp)]
                rows = [Cs[c][:d[c], :m] for c in range(s) if d[c]]
                if rank_F(F, np.concatenate(rows, 0)) < k: ok = False; break
            if ok: t = m - k; break
        ts.append(t)
    return ts
