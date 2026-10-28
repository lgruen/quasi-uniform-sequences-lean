"""All-large-p constants of the explicit rule (Theorem thm:A and Proposition prop:P0 of the paper).

Rule at a prime p: T := largest odd integer <= u*p (u = fixed rational), kappa = T*n (n from design()), windows
B_bc = floor(wbc p), B_cc = floor(wcc p), B_cb = floor(wcb p), own sizes from Lemma WS.  For every p >= p0 the
hypotheses hold and LB >= 1 - Mb^+/p.  Monotone upper bounds (valid for all p' >= p, see Proposition prop:P0):
   T in [u p - 2, u p],  nu = T|n|(x2 if doubled) in [nu^-, nu^+],  |I| >= 2 w p - 1,
   N_1 <= 2 + (p - |I_1|^-)/nu_1^-,  N_t <= N_{t-1} + p/nu_t^-,  sweep test N_{t-1}^+ nu_t^+ <= |I_t|^-.
Exact Fractions."""
from fractions import Fraction as F
from bs_rule import design
import math, sys

def _ws(ns, ws, u, p, dbl):
    k = 2 if dbl else 1
    o = sorted(range(len(ns)), key=lambda t: -ns[t])
    nus = [ns[t] for t in o]; W = [ws[t] for t in o]
    lo = lambda n: n*k*(u*p - 2); hi = lambda n: n*k*u*p; Il = lambda w: 2*w*p - 1
    if lo(nus[-1]) <= 0: return None
    if hi(nus[0]) > Il(W[0]): return None
    N = 2 + max(F(0), (p - Il(W[0]))/lo(nus[0]))
    for t in range(1, len(nus)):
        if N*hi(nus[t]) > Il(W[t]): return None
        N = N + p/lo(nus[t])
    return N

def bounds(D, wbc, wcc, wcb, u, p):
    s, b, J, n = D['s'], D['b'], D['J'], D['n']
    # (i) forced crosses inside the windows (T <= u p)
    for j in J:
        if abs(n[j][b])*u*p > wbc*p - 1: return None
        for i in J:
            if i != j and abs(n[j][i])*u*p > wcc*p - 1: return None
    for i in J:
        if abs(2*n[b][i])*u*p > 2*(wcb*p - 1) - 1: return None
    Nb = _ws([abs(n[j][b]) for j in J], [wbc]*(s-1), u, p, False)
    if Nb is None: return None
    M = 0
    for i in J:
        ns = [abs(n[c][i]) for c in range(s) if c != i]; ws = [wcb if c == b else wcc for c in range(s) if c != i]
        N = _ws(ns, ws, u, p, True)
        if N is None: return None
        M = max(M, 2*N - 1)
    return Nb, M

def ok(D, wbc, wcc, wcb, u, p):
    s = D['s']
    r = bounds(D, wbc, wcc, wcb, u, p)
    if r is None: return False, None
    Mb, M = r
    x = 1 - (s-2)*wcc - 2*wbc; y = F(1, 2) - wcb
    Delta = x*x + y*y - 1
    if Delta <= 0: return False, r
    c1 = p*Delta >= 2*x*M + 2*y*(Mb + F(1, 2))                 # T_Cb >= 1
    c2 = 1 - 2*(s-2)*wcc - 2*wbc - M/p >= F(7072, 10000)       # T_2 >= 1   (0.7072 > 1/sqrt 2)
    c3 = (2*(s-2)*wcc + 2*wbc)*p + M + 2 <= p - 1 and 2*wcb*p + 2*Mb + 2 < p - 1 and x - M/p > 0
    return (c1 and c2 and c3), r

def p0(D, wbc, wcc, wcb, u, lo=10**2, hi=10**40):
    wbc, wcc, wcb, u = F(wbc), F(wcc), F(wcb), F(u)
    if not ok(D, wbc, wcc, wcb, u, F(hi))[0]: return None
    while hi/lo > F(1001, 1000):
        mid = F(int(math.sqrt(lo*hi)) + 1)
        if ok(D, wbc, wcc, wcb, u, mid)[0]: hi = mid
        else: lo = mid
    return hi, ok(D, wbc, wcc, wcb, u, hi)[1]

def u_wrap(D, wbc, margin=F(999, 1000)):
    """u putting the brick wrap at margin*wbc*p."""
    s, b, J, n = D['s'], D['b'], D['J'], D['n']
    return F(wbc)*margin/max(abs(n[j][b]) for j in J)

if __name__ == "__main__":
    s = int(sys.argv[1]); R = int(sys.argv[2]); w = F(sys.argv[3]); b = int(sys.argv[4]) if len(sys.argv) > 4 else None
    D = design(s, [R**r for r in range(1, s)], b=b)
    u = u_wrap(D, w)
    res = p0(D, w, w, w, u)
    if res is None: print("s=%d R=%d w=%s: hypotheses fail for all p" % (s, R, w)); sys.exit()
    P0, (Mb, M) = res
    print("s=%d b=%d R=%d w=%s delta=%d L=%d  p0=%.4g  C=%.1f  Mmax<=%.4g" % (s, D['b'], R, w, D['delta'], D['L'], float(P0), float(Mb), float(M)))
