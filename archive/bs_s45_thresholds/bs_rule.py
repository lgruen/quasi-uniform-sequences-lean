"""Explicit brick-star rule BS_s (research notes, not archived; Theorem thm:A of the paper): frame + gauge + theta as exact rationals, windows, generalized
wrap/sweep coverings (Lemma WS), the closed-form window certificate (Lemma W) and the exact interval certificate
(lem:cert, j=1, product windows) for comparison.  Pure integer/Fraction arithmetic except the final square roots.

Design data (all p-independent):  places a_c (default Faure 0..s-1), brick index b, compressed order J=(j_1..j_{s-1}),
odd positive integers Q_1..Q_{s-1}.  Gauge g_b = 1, g_{j_r} = 2^{1+delta} Q_r / rho_{b j_r};  theta = 2^delta L T with T
odd (p-dependent).  Then kappa_{c<-c'} = theta g_c/(g_{c'} rho_{cc'}) = T * n[c][c'] with fixed rationals n:
n[b][j_r] = L/(2Q_r) (odd/2: antipodal), all other n integers (delta, L chosen minimal).
"""
from fractions import Fraction as F
from math import gcd, ceil, floor, sqrt
import itertools

def lcm(a, b): return a // gcd(a, b) * b
def v2(n):
    n = abs(n); k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k
def oddpart(n):
    n = abs(n)
    while n % 2 == 0: n //= 2
    return n

def frame_rho(a):
    s = len(a)
    wp = []
    for c in range(s):
        pr = F(1)
        for d in range(s):
            if d != c: pr *= (a[c] - a[d])
        wp.append(pr)
    rho = [[None]*s for _ in range(s)]
    for c in range(s):
        for cp in range(s):
            if c != cp: rho[c][cp] = wp[cp]*(a[cp]-a[c])   # rho_{cc'} = w'(a_c')(a_c' - a_c)
    return rho

def design(s, Q, a=None, b=None, J=None):
    a = [F(x) for x in (a if a is not None else range(s))]
    b = (s-1)//2 if b is None else b
    J = [c for c in range(s) if c != b] if J is None else list(J)
    rho = frame_rho(a)
    g = [None]*s; g[b] = F(1)
    # find minimal delta, L
    for delta in range(0, 40):
        for r, j in enumerate(J): g[j] = F(2)**(1+delta)*F(Q[r])/rho[b][j]
        L = 1
        for qq in Q:
            qq = F(qq); assert qq.numerator % 2 and qq.denominator % 2, "Q must be odd/odd"
            L = lcm(L, qq.numerator); L = lcm(L, qq.denominator)
        ok = True; m = {}
        for c in range(s):
            for cp in range(s):
                if c == cp: continue
                x = F(2)**delta * g[c]/(g[cp]*rho[c][cp])        # n/L
                if c == b: x = 2*x                                 # antipodal: need 2n odd integer
                if v2(x.denominator) > 0: ok = False
                L = lcm(L, oddpart(x.denominator))
        if not ok: continue
        n = [[None]*s for _ in range(s)]
        for c in range(s):
            for cp in range(s):
                if c != cp: n[c][cp] = F(2)**delta*L*g[c]/(g[cp]*rho[c][cp])
        for r, j in enumerate(J):
            assert (2*n[b][j]).denominator == 1 and (2*n[b][j]).numerator % 2 == 1, "antipodal not odd/2"
        for c in range(s):
            for cp in range(s):
                if c != cp and c != b: assert n[c][cp].denominator == 1
        return dict(s=s, a=a, b=b, J=J, Q=[F(x) for x in Q], rho=rho, g=g, delta=delta, L=L, n=n)
    raise ValueError("no delta")

def ws_N(steps, lens, p):
    """Lemma WS: steps = list of |v_t| (>=1), lens = window lengths |I_t|.  Sorted by step descending inside.
    Returns (N, ok, detail): any N consecutive integers o contain one with sigma + o v in prod I_t (every sigma)."""
    order = sorted(range(len(steps)), key=lambda t: -steps[t])
    nu = [steps[t] for t in order]; L = [lens[t] for t in order]
    if nu[0] > L[0] or L[0] > p: return None, False, "wrap"
    N = 1 + max(0, -(-(p - L[0]) // nu[0]))
    for t in range(1, len(nu)):
        if N*nu[t] > L[t]: return None, False, "sweep%d" % t
        N = N - 1 + (-(-p // nu[t]))
    return N, True, ""

def rule(D, p, wbc, wcc, wcb, T=None):
    s, b, J, n = D['s'], D['b'], D['J'], D['n']
    Bbc, Bcc, Bcb = int(F(wbc)*p), int(F(wcc)*p), int(F(wcb)*p)
    if T is None:
        nw = max(abs(n[j][b]) for j in J)
        T = int(F(Bbc)/nw)
        if T % 2 == 0: T -= 1
    if T < 1: return None
    kap = [[None]*s for _ in range(s)]
    for c in range(s):
        for cp in range(s):
            if c != cp: kap[c][cp] = T*n[c][cp]          # exact rational (integer or odd/2)
    res = dict(p=p, T=T, Bbc=Bbc, Bcc=Bcc, Bcb=Bcb, kap=kap)
    ok = True; why = []
    # (i) forced crosses in windows (as integers, |.| < p/2 checked)
    for j in J:
        if abs(kap[j][b]) > Bbc: ok = False; why.append("i:brick")
        for i in J:
            if i != j and abs(kap[j][i]) > Bcc: ok = False; why.append("i:cc")
    for i in J:
        x = 2*kap[b][i]
        if abs(x) > 2*Bcb-1: ok = False; why.append("i:cb")
    # coverings
    Nb, okb, wb = ws_N([abs(int(kap[j][b])) for j in J], [2*Bbc+1]*(s-1), p)
    if not okb: ok = False; why.append("cov:b:"+wb)
    Mi = {}
    for i in J:
        steps = []; lens = []
        for c in range(s):
            if c == i: continue
            steps.append(abs(int(2*kap[c][i]))); lens.append(2*Bcb+1 if c == b else 2*Bcc+1)
        Ni, oki, wi = ws_N(steps, lens, p)
        if not oki: ok = False; why.append("cov:%d:%s" % (i, wi)); continue
        Mi[i] = 2*Ni - 1
    res.update(ok=ok, why=why, Mb=Nb, Mi=Mi)
    if not ok: return res
    Mb = Nb; Mmax = max(Mi.values()); A = (s-2)*Bcc + Bbc
    res['A'] = A
    side = (A + Mmax - 1 + (s-2)*Bcc + Bbc <= p-1) and (2*Bcb + 2*Mb < p-1)
    res['side'] = side
    # Lemma W
    Tb = (1 - F(Mb, p))**2
    TC1 = (1 - F(A+Mmax, p))**2 + F(p-3-2*Bcb, 2*p)**2
    TCb = (1 - F(A+Mmax+Bbc, p))**2 + F(p-1-2*Bcb-2*Mb, 2*p)**2
    T2 = 2*(1 - F(A+Mmax+(s-2)*Bcc+Bbc, p))**2
    terms = dict(Tb=Tb, TC1=TC1, TCb=TCb, T2=T2)
    res['LBW'] = sqrt(float(min(terms.values()))); res['binding'] = min(terms, key=lambda k: terms[k])
    return res

def windows(D, res):
    """Integer interval windows win[c][c'] = (lo, hi) for the response of column c' in coordinate c."""
    s, b, J = D['s'], D['b'], D['J']; p = res['p']
    Bbc, Bcc, Bcb, A, Mb, Mi = res['Bbc'], res['Bcc'], res['Bcb'], res['A'], res['Mb'], res['Mi']
    half = (p+1)//2
    win = [[None]*s for _ in range(s)]
    for i in J:
        win[i][i] = (-(A+Mi[i]-1), -A); win[b][i] = (half-Bcb, half+Bcb)
        for j in J:
            if j != i: win[j][i] = (-Bcc, Bcc)
    win[b][b] = (-(Mb-1), 0)
    for j in J: win[j][b] = (-Bbc, Bbc)
    return win

def f1(e, sg, p):
    r = sg % p
    if e == 0: c = min(r, p-r); return F(max(0, c-1), p)
    if e == -1: r = (-sg) % p
    return F(p-1, p) if r == 0 else F(r-1, p)
def f1min(e, lo, hi, p):
    if hi-lo+1 >= p: return F(0)
    if e < 0: lo, hi = -hi, -lo; e = 1
    if e > 0:
        k = lo + ((1-lo) % p)
        return F(0) if k <= hi else f1(1, lo, p)
    for r in (-1, 0, 1):
        k = lo + ((r-lo) % p)
        if k <= hi: return F(0)
    return min(f1(0, lo, p), f1(0, hi, p))
def exact_cert(win, p):
    s = len(win); best = None; arg = None
    for e in itertools.product((-1, 0, 1), repeat=s):
        if not any(e) or [x for x in e if x][0] != 1: continue
        t = F(0)
        for c in range(s):
            lo = hi = 0
            for cp in range(s):
                if e[cp]:
                    a_, b_ = win[c][cp]
                    if e[cp] == 1: lo += a_; hi += b_
                    else: lo -= b_; hi -= a_
            t += f1min(e[c], lo, hi, p)**2
        if best is None or t < best: best, arg = t, e
    return sqrt(float(best)), arg

def residues_check(D, res):
    """kappa from the F_p formula kappa = theta g_c/(g_c' rho_cc') with theta = 2^delta L T, compared with T*n mod p."""
    p = res['p']; s = D['s']
    def red(x): return x.numerator * pow(x.denominator, -1, p) % p
    theta = (2**D['delta'])*D['L']*res['T'] % p
    for c in range(s):
        for cp in range(s):
            if c == cp: continue
            k1 = theta * red(D['g'][c]) * pow(red(D['g'][cp]*D['rho'][c][cp]), -1, p) % p
            if k1 != red(res['kap'][c][cp]): return False
    return True
