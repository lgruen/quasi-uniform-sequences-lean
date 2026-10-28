"""rebuild_check.py -- exact checks behind Table tab:practice and Proposition prop:primepower.

    uv run --with numpy python practice/rebuild_check.py [practice|primepower]     (from the archive root; < 30 s)

(1) Residue sequences of tab:practice: rebuild the generator matrices of Definition def:residue,
        C_c[n][i] = v_c^{-1} theta^{n+1} [(z-a_c)^n] z^i / w_c(z)^{n+1}   over F_p,
    from (places a, theta, check vector v) and compare them entry by entry with the archived matrices
    practice/residue_U_p<p>.txt (the files whose J was measured for the table).  Then compute lambda_jit(Lambda_v)^2
    exactly (enumeration of Lambda_v in a box) and the certified constants, TRUNCATED to 3 digits.
(2) prop:primepower: an independent re-implementation of the bound beta_q (digit relaxation, one digit, staggered
    coordinate only, carry rule over F_q), exhaustive over the weights k, for the power-basis encoding of the stated
    monic irreducible polynomial (code sum c_i p^i).
"""
import os, sys, itertools, math
import numpy as np

PV = os.path.dirname(os.path.abspath(__file__))   # practice/ (the archived matrices)


# ---------------------------------------------------------------- (1) residue sequences
def series_inv(a, n, p):
    """inverse of the power series a (list, a[0] != 0) mod t^n over F_p"""
    inv0 = pow(a[0], p - 2, p); b = [0] * n; b[0] = inv0
    for k in range(1, n):
        s = sum(a[j] * b[k - j] for j in range(1, min(k, len(a) - 1) + 1)) % p
        b[k] = (-s * inv0) % p
    return b


def series_mul(a, b, n, p):
    c = [0] * n
    for i, x in enumerate(a[:n]):
        if x:
            for j, y in enumerate(b[:n - i]):
                c[i + j] = (c[i + j] + x * y) % p
    return c


def residue_matrices(p, a, theta, v, R, C):
    s = len(a); M = np.zeros((s, R, C), dtype=np.int64)
    for c in range(s):
        # w_c(z) expanded at a_c in t = z - a_c: prod_{b != c} (t + a_c - a_b)
        wc = [1]
        for b in range(s):
            if b != c:
                wc = series_mul(wc, [(a[c] - a[b]) % p, 1], R + 1, p) + [0] * 0
        winv = series_inv(wc, R, p)
        vinv = pow(v[c], p - 2, p)
        powinv = [1] + [0] * (R - 1)          # w_c^{-(n+1)} built incrementally
        for n in range(R):
            powinv = series_mul(powinv, winv, R, p)
            for i in range(C):
                # z^i = (t + a_c)^i
                zi = [math.comb(i, k) * pow(a[c], i - k, p) % p for k in range(i + 1)]
                coef = sum(zi[k] * powinv[n - k] for k in range(min(i, n) + 1)) % p
                M[c, n, i] = vinv * pow(theta, n + 1, p) * coef % p
    return M


def load_dump(fn):
    t = open(fn).read().split(); p, R, C = map(int, t[:3])
    return p, np.array(list(map(int, t[3:3 + 3 * R * C])), dtype=np.int64).reshape(3, R, C)


def ljit2(p, v):
    """exact lambda_jit(Lambda_v)^2 for s = 3: min over 0 != b in Lambda_v of sum (|b_c|-1)_+^2 (box search)"""
    s = len(v); inv_last = pow(v[-1], p - 2, p); best = None; B = 1
    while True:
        rng = range(-B, B + 1)
        for b in itertools.product(rng, repeat=s - 1):
            r = (-sum(vc * bc for vc, bc in zip(v[:-1], b)) * inv_last) % p
            for last in (r - p * k for k in range(-2, 3)):
                vec = list(b) + [last]
                if not any(vec):
                    continue
                val = sum(max(0, abs(x) - 1) ** 2 for x in vec)
                if best is None or val < best:
                    best = val
        if best is not None and best <= B * B:   # a vector outside the box has a coordinate >= B+1, so val >= B^2
            return best
        B += 1
        if B > p:
            return best


def trunc(x, d=3):
    return math.floor(x * 10 ** d) / 10 ** d


WIN = {13: ((2, 9, 10), 12, (5, 3, 6)), 17: ((2, 9, 6), 12, (4, 10, 16)),
       23: ((18, 22, 15), 5, (4, 14, 20)), 31: ((8, 0, 16), 9, (10, 30, 7))}


def part1():
    print('(1) residue sequences of tab:practice')
    for p, (a, th, v) in WIN.items():
        q, A = load_dump(os.path.join(PV, f'residue_U_p{p}.txt')); assert q == p
        M = residue_matrices(p, a, th, v, A.shape[1], A.shape[2])
        same = bool((M == A).all())
        l2 = ljit2(p, v); lj = math.sqrt(l2); LB = lj * p ** (-1 / 3)
        print(f'  p={p}: places {a}, theta={th}, v={v}: matrices == archived: {same}; lambda_jit^2={l2}; '
              f'sep(P_3K-1) >= {LB:.5f} (trunc {trunc(LB):.3f}); inclusion lambda_jit/p = {lj / p:.5f} '
              f'(trunc {trunc(lj / p):.3f}); all-N LB/p = {LB / p:.5f} (trunc {trunc(LB / p):.3f})')
        assert same


# ---------------------------------------------------------------- (2) prime powers
def field(p, f):
    r = len(f) - 1; Q = p ** r
    elems = [tuple((x // p ** i) % p for i in range(r)) for x in range(Q)]
    code = {e: x for x, e in enumerate(elems)}
    def add(x, y): return tuple((a + b) % p for a, b in zip(x, y))
    def neg(x): return tuple((-a) % p for a in x)
    def mul(x, y):
        pr = [0] * (2 * r - 1)
        for i in range(r):
            for j in range(r):
                pr[i + j] = (pr[i + j] + x[i] * y[j]) % p
        for k in range(2 * r - 2, r - 1, -1):
            c = pr[k]
            if c:
                for t in range(r + 1):
                    pr[k - r + t] = (pr[k - r + t] - c * f[t]) % p
        return tuple(pr[:r])
    return Q, elems, code, add, neg, mul


def beta_q(p, f, s):
    Q, E, code, add, neg, mul = field(p, f)
    D = sorted({add(E[(code[d] + 1) % Q], neg(d)) for d in E}, key=lambda e: code[e])   # carry changes Delta(y)
    # f_1(e, sigma) * Q = max(0, min_R |e Q + enc(R + sigma) - enc(R)| - 1)
    addtab = np.array([[code[add(x, y)] for y in E] for x in E])          # addtab[R][sigma] = enc(R + sigma)
    Rc = np.arange(Q)[:, None]
    F = {}
    for e in (-1, 0, 1):
        mn = np.abs(e * Q + addtab - Rc).min(axis=0)
        for sg in range(Q):
            F[(e, sg)] = max(0, int(mn[sg]) - 1)
    zero = E[0]; units = E[1:]
    best, bestk = -1, None
    for k in itertools.product(units, repeat=s - 1):
        worst = F[(1, 0)]
        for ev in itertools.product((-1, 0, 1), repeat=s - 1):
            if not any(ev):
                continue
            mv = [i for i in range(s - 1) if ev[i]]
            for dl in itertools.product(D, repeat=len(mv)):
                sg = zero
                for i, d in zip(mv, dl):
                    t = mul(k[i], d); sg = add(sg, t if ev[i] > 0 else neg(t))
                c = code[sg]
                worst = min(worst, F[(0, c)], F[(1, c)], F[(-1, c)])
                if worst <= best:
                    break
            if worst <= best:
                break
        if worst > best:
            best, bestk = worst, [code[x] for x in k]
    return best, Q, bestk


def poly_str(f):
    r = len(f) - 1; terms = []
    for i in range(r, -1, -1):
        c = f[i]
        if c == 0: continue
        mon = '1' if i == 0 else ('x' if i == 1 else f'x^{i}')
        terms.append(mon if (c == 1 and i > 0) else (f'{c}' if i == 0 else f'{c}{mon}'))
    return '+'.join(terms)


CASES = [  # (p, f low->high monic, s)
    (5, [2, 0, 1], 3), (2, [1, 1, 1, 1, 0, 1], 3), (2, [1, 1, 1, 0, 1, 1], 3), (2, [1, 0, 1, 0, 0, 1], 3),
    (7, [1, 0, 1], 3), (2, [1, 1, 0, 0, 0, 0, 1], 3), (3, [2, 1, 0, 0, 1], 3), (11, [1, 0, 1], 3), (5, [1, 1, 0, 1], 3),
    (2, [1, 1, 0, 1], 2), (3, [1, 0, 1], 2), (2, [1, 1, 0, 0, 1], 2), (5, [2, 0, 1], 2), (3, [1, 2, 0, 1], 2),
    (7, [1, 0, 1], 2)]


def part2():
    print('(2) prop:primepower: beta_q, exhaustive over the weights (independent re-implementation)')
    for p, f, s in CASES:
        b, Q, k = beta_q(p, f, s)
        print(f'  q={Q:4d} s={s} f={poly_str(f):18s} beta_q = {b}/{Q}  at k(codes)={k}', flush=True)


if __name__ == '__main__':
    import time
    mode = sys.argv[1] if len(sys.argv) > 1 else 'all'
    t = time.time()
    if mode in ('all', 'practice'): part1()
    if mode in ('all', 'primepower'): part2()
    print(f'total {time.time() - t:.1f}s')
