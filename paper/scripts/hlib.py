"""hlib.py -- asymmetric product-set window certificates (window rules of Section sec:antipode): the half-frozen
family HF and the brick-hybrid family HB (hb_best, hb_params, hb_formula: the hexagonal brick wall of thm:HB).
Pair A = place-0 data (O_0, X_1; kappa0), pair B = place-1 data (O_1, X_0; kappa1). The asymmetric build is
dlib.build_LI (kappa1 = c/s, kappa0 = c s). Unchanged copy of the development library (except the import path).
"""
import math


def T1(D, p):
    D %= p
    return 1 - 1 / p if D == 0 else (D - 1) / p


def T0(D, p):
    D %= p
    return max(0.0, (min(D, p - D) - 1) / p)


def covers(p, k, Wo, Wx):
    """covering (ii):  k (Wo - 1) - Wx = F_p  (exact set identity)."""
    S = {(k * (o - 1) - x) % p for o in Wo for x in Wx}
    return len(S) == p


def LB_prod(p, WoA, WxA, WoB, WxB):
    """exact Lemma-C product-set bound (sets of residues), capped at 1."""
    t = lambda f, S: min(f(v, p) for v in S)
    ax0 = t(T1, WoA) ** 2 + t(T0, WxA) ** 2
    ax1 = t(T1, WoB) ** 2 + t(T0, WxB) ** 2
    s = lambda A, B, sg: {(a + sg * b) % p for a in A for b in B}
    dg = t(T1, s(WoA, WxB, 1)) ** 2 + t(T1, s(WoB, WxA, 1)) ** 2
    ad = t(T1, s(WoA, WxB, -1)) ** 2 + t(T1, s(WoB, WxA, -1)) ** 2
    return min(1.0, math.sqrt(min(ax0, ax1, dg, ad)))


def rng(a, b):
    return list(range(a, b + 1))


# ---------- family HF (half-frozen): O_0 == -a, kappa0 = kappa1 = -a, Wx^B = [-a, a], Wo^B = [-(L-1), 0] ----------
def hf_params(p, a):
    L = -(-(p - 1) // a) - 1          # ceil((p-1)/a) - 1
    return dict(a=a, L=L, k0=-a, k1=-a, WoA=[-a], WxA=list(range(p)), WoB=rng(-(L - 1), 0), WxB=rng(-a, a))


def hf_formula(p, a):
    L = -(-(p - 1) // a) - 1
    return 1 - max(2 * a + 1, L) / p


def hf_best(p):
    return max((hf_formula(p, a), a) for a in range(1, (p - 1) // 2))


# ---------- family HB (brick hybrid) ----------
def hb_params(p, w, m):
    q = 2 * w + 1; k = 2 * q * m * m
    LA = -(-(p - 3) // q) + 3
    LB = -(-(p - 1) // k) - 1
    M = k
    aA = M + LA - 1
    h = (p - 1) // 2   # (p+1)/2 = 1/2 in F_p ; window 1/2 + [-w, w]
    WxA = [((p + 1) // 2 + j) % p for j in range(-w, w + 1)]
    return dict(q=q, k=k, LA=LA, LB=LB, aA=aA, k0=(-q * pow(2, p - 2, p)) % p, k1=-k,
                WoA=rng(-aA, -M), WxA=WxA, WoB=rng(-(LB - 1), 0), WxB=rng(-k, k))


def hb_formula(p, w, m):
    q = 2 * w + 1; k = 2 * q * m * m
    if q >= p or 3 * k >= p: return -1
    LA = -(-(p - 3) // q) + 3; LB = -(-(p - 1) // k) - 1
    h = (p - 1 - 2 * w - 2 * LB) / (2 * p)
    if h <= 0: return -1
    ax0 = (1 - (k + LA) / p) ** 2 + ((p - 3 - 2 * w) / (2 * p)) ** 2
    ax1 = (1 - LB / p) ** 2
    dg = max(0, 1 - (2 * k + LA) / p) ** 2 + h * h
    return min(1.0, math.sqrt(min(ax0, ax1, dg)))


def hb_best(p, wmax=None):
    best = (-1, None)
    for w in range(1, (wmax or int(2 * math.sqrt(p)) + 3)):
        for m in range(1, 60):
            if 2 * (2 * w + 1) * m * m * 3 >= p: break
            v = hb_formula(p, w, m)
            if v > best[0]: best = (v, (w, m))
    return best
