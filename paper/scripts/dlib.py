"""dlib.py -- odd-level (skeleton) law of scrambled 2D Faure (I,P) sequences over F_p: the part used by the
window-rule builder of make_figs.mats_window (hexagonal brick wall).

Places a_0=0, a_1=1, w=t(t-1), e-basis, L_1 = T_1 E, L_0 = T_0 E diag((-1)^k). Generator matrices, direct law,
partial sums and t-value come from the independent library t2d_alib.py.
  * build_LI(p, c, s, X0ps, X1ps, D): asymmetric level-invariant scramble with slope s (mu_0=1, mu_1=s),
    kappa_1=c/s, kappa_0=c*s, from the cross partial sums X_0^(l), X_1^(l) (l=1..).
Extracted from the development scripts of the paper: only the functions used by the figures are kept, unchanged.
"""
import math
from t2d_alib import gamma_series, inv, series_inv, gen_mats, direct_law, partial_sums, cert_LB, t_value, T  # noqa


def cen(v, p):
    v %= p
    return v - p if v > p // 2 else v


def Emat(p, D):
    return [[((-1) ** (j - k) * math.comb(2 * j + 1 - k, j - k)) % p if k <= j else 0 for k in range(D)] for j in range(D)]


def mul(A, B, p):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) % p for j in range(len(B[0]))] for i in range(len(A))]


def T_from_X(p, c, mu, kappa, Xps, D):
    """T = diag(mu c^j) Toep(tauhat), tauhat(c y) = -kappa / X(y), X(y) = sum_n (X^(n+1)-X^(n)) y^n."""
    xi = [(Xps[n + 1] - (Xps[n] if n >= 1 else 0)) % p for n in range(D)]
    assert xi[0] == (-kappa) % p, "X^(1) must equal -kappa"
    Xi = series_inv(xi, p, D)                     # 1/X(y)
    ci = inv(c, p)
    tau = [(-kappa * Xi[j] * pow(ci, j, p)) % p for j in range(D)]   # tauhat_j = c^{-j} [y^j](-kappa/X)
    assert tau[0] == 1
    return [[(mu * pow(c, j, p) * tau[j - i]) % p if i <= j else 0 for i in range(D)] for j in range(D)]


def build_LI(p, c, s, X0ps, X1ps, D):
    """Asymmetric LI scramble with common scale c and slope s = d_1/d_0 (mu_0 = 1, mu_1 = s).
    X0ps[l] (l>=1): cross partial sums of coordinate 0 (place-1 data), X0ps[1] = -c/s;
    X1ps[l]: cross partial sums of coordinate 1 (place-0 data), X1ps[1] = -c s.  Index 0 unused."""
    k1 = c * inv(s, p) % p; k0 = c * s % p
    T1 = T_from_X(p, c, s, k1, X0ps, D)
    T0 = T_from_X(p, c, 1, k0, X1ps, D)
    E = Emat(p, D)
    L1 = mul(T1, E, p)
    L0 = [[v * (1 if k % 2 == 0 else p - 1) % p for k, v in enumerate(r)] for r in mul(T0, E, p)]
    return L0, L1, T0, T1


# ---------------- odd certificate (Lemma C_odd) ----------------
