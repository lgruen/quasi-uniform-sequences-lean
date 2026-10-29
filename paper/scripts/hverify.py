"""hverify.py -- greedy_pair: the greedy choice of the window values of one pair (place-0 data or place-1 data) of
a product-set window rule; used by make_figs.mats_window. Extracted from the development scripts of the paper
(the verification driver of the development version is not included).
"""
from dlib import gamma_series, inv, cen


def greedy_pair(p, kap, zeta, Wo, Wx, n):
    """Theorem-G greedy for one pair: X[1] = -kap; O^(l) = 1 + kap^{-1}(X^(l+1) + s_l), canonical least |x| (+ first)."""
    g = gamma_series(p, n + 3); Wo = {v % p for v in Wo}; Wx = sorted({v % p for v in Wx}, key=lambda v: (abs(cen(v, p)), -cen(v, p)))
    X = [0] * (n + 2); X[1] = (-kap) % p; assert X[1] in Wx; O = [None] * (n + 2); ki = inv(kap, p)
    for l in range(1, n + 1):
        s = sum(g[l - k] * pow(zeta, l - k, p) * X[k + 1] for k in range(l)) % p
        x = next(x for x in Wx if (1 + ki * (x + s)) % p in Wo)
        X[l + 1] = x; O[l] = (1 + ki * (x + s)) % p
    return X, O
