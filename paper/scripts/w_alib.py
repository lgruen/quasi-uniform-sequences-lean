# w_alib.py -- independent library for the brick walls W^+/W^- (written from the formulas only), used by wbuild.py.
# Polynomials/series over F_p: lists, low degree first. Unchanged copy of the development library.
import itertools, math

def trim(a):
    while a and a[-1] == 0: a.pop()
    return a
def padd(a, b, p):
    n = max(len(a), len(b)); return trim([((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % p for i in range(n)])
def psub(a, b, p): return padd(a, [(-c) % p for c in b], p)
def pmul(a, b, p):
    if not a or not b: return []
    r = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): r[i+j] = (r[i+j] + x*y) % p
    return trim(r)
def pscal(a, c, p): return trim([(x*c) % p for x in a])
def pdivmod(a, b, p):
    a = a[:]; q = [0]*max(0, len(a)-len(b)+1); inv = pow(b[-1], p-2, p)
    while len(trim(a)) >= len(b):
        d = len(a)-len(b); c = a[-1]*inv % p; q[d] = c
        for i, y in enumerate(b): a[i+d] = (a[i+d] - c*y) % p
        trim(a)
    return trim(q), a
def pgcd(a, b, p):
    a, b = trim(a[:]), trim(b[:])
    while b: a, b = b, pdivmod(a, b, p)[1]
    if a: a = pscal(a, pow(a[-1], p-2, p), p)
    return a
def ppow(a, e, p):
    r = [1]
    for _ in range(e): r = pmul(r, a, p)
    return r

# ---- field F_p(x)(r), r = rho^{-1}, r^2 = 1/u, u = 1 + eps x.  element = (A, B, Q) meaning (A + B r)/Q
class F:
    def __init__(s, p, eps, A, B, Q):
        s.p, s.eps = p, eps; s.u = trim([1, eps % p])
        A, B, Q = trim(list(A)), trim(list(B)), trim(list(Q))
        g = pgcd(pgcd(A, B, p) if (A or B) else [], Q, p) if (A or B) else Q
        if g and len(g) > 1:
            A = pdivmod(A, g, p)[0]; B = pdivmod(B, g, p)[0]; Q = pdivmod(Q, g, p)[0]
        if not A and not B: Q = [1]
        c = pow(Q[-1], p-2, p); s.A, s.B, s.Q = pscal(A, c, p), pscal(B, c, p), pscal(Q, c, p)
    def mk(s, A, B, Q): return F(s.p, s.eps, A, B, Q)
    def __add__(s, o):
        o = s.co(o); p = s.p
        return s.mk(padd(pmul(s.A, o.Q, p), pmul(o.A, s.Q, p), p), padd(pmul(s.B, o.Q, p), pmul(o.B, s.Q, p), p), pmul(s.Q, o.Q, p))
    __radd__ = __add__
    def __neg__(s): return s.mk(pscal(s.A, -1, s.p), pscal(s.B, -1, s.p), s.Q)
    def __sub__(s, o): return s + (-s.co(o))
    def __rsub__(s, o): return s.co(o) - s
    def __mul__(s, o):
        o = s.co(o); p, u = s.p, s.u
        A = padd(pmul(pmul(s.A, o.A, p), u, p), pmul(s.B, o.B, p), p)
        B = pmul(padd(pmul(s.A, o.B, p), pmul(o.A, s.B, p), p), u, p)
        return s.mk(A, B, pmul(pmul(s.Q, o.Q, p), u, p))
    __rmul__ = __mul__
    def inv(s):
        p, u = s.p, s.u
        den = psub(pmul(pmul(s.A, s.A, p), u, p), pmul(s.B, s.B, p), p)
        return s.mk(pmul(pmul(s.Q, s.A, p), u, p), pscal(pmul(pmul(s.Q, s.B, p), u, p), -1, p), den)
    def __truediv__(s, o): return s * s.co(o).inv()
    def __rtruediv__(s, o): return s.co(o) * s.inv()
    def co(s, o):
        if isinstance(o, F): return o
        if isinstance(o, int): return s.mk([o % s.p], [], [1])
        return s.mk(o, [], [1])  # polynomial
    def iszero(s): return not s.A and not s.B
    def series(s, n, rser):
        """Laurent check: requires Q(0)!=0; returns first n coeffs."""
        p = s.p; v = 0
        while s.Q[v] % p == 0: v += 1
        Qp = s.Q[v:]; N = n + v
        assert len(rser) >= N
        num = padd(trunc(s.A, N), trunc(smul(s.B, rser, p, N), N), p)
        ser = smul(trunc(num, N), sinv(Qp, p, N), p, N)
        assert all(c == 0 for c in ser[:v]), "pole"
        return ser[v:]

def trunc(a, n): return (a[:n] + [0]*(n-len(a[:n])))
def smul(a, b, p, n):
    r = [0]*n
    for i, x in enumerate(a[:n]):
        if x:
            for j in range(min(len(b), n-i)): r[i+j] = (r[i+j] + x*b[j]) % p
    return r
def sinv(a, p, n):
    a = trunc(a, n); i0 = pow(a[0], p-2, p); r = [0]*n; r[0] = i0
    for k in range(1, n):
        acc = sum(a[t]*r[k-t] for t in range(1, k+1)) % p
        r[k] = (-acc*i0) % p
    return r
def ssqrt1(a, p, n):  # sqrt of series with a[0]=1, coefficientwise
    a = trunc(a, n); r = [0]*n; r[0] = 1; i2 = pow(2, p-2, p)
    for k in range(1, n):
        r[k] = ((a[k] - sum(r[t]*r[k-t] for t in range(1, k))) * i2) % p
    return r
def lucas_r(p, eps, N):
    """[x^n] (1+eps x)^(-1/2) for n<N via -1/2 = sum ((p-1)/2) p^k (Lucas)."""
    h = (p-1)//2; b = [math.comb(h, d) % p * pow(eps % p, d, p) % p for d in range(p)]
    out = [0]*N
    for n in range(N):
        v, m = 1, n
        while m and v:
            v = v*b[m % p] % p; m //= p
        out[n] = v
    return out
