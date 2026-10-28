"""fq_residue.py -- the residue design over F_Q, Q = p^r (Proposition prop:primepower; original program).
Lemma R2 (residue theorem) holds over any field, so the first geometric digit of the staggered coordinate is
r_* = sum_c k_c * y_{c,K-1} (finest cell digits) at every level.  Over F_Q a step n_c -> n_c + 1 of the integer cell
index changes the finest digit by Delta(d) = enc^{-1}(enc(d)+1) - d, which is one of D_r = {1, 1+b, 1+b+b^2, ...}
(b = basis element of code p) -- not a constant (rem:F4carry).  So sigma_* = sum_c e_c k_c Delta_c with any Delta_c in
D_r, and lem:cert (j = 1, coordinate * only) gives sep >= beta_Q(k) := min f_1(e_*, sigma_*) over e' != 0, Delta, e_*.
This script searches k in (F_Q^*)^{s-1} (exhaustively, or a sample) for the largest beta_Q(k).
usage: python3 primepower/original_fq_residue.py p r s [maxk]
"""
import sys, itertools, random

IRRED = {(2, 2): [1, 1, 1], (2, 3): [1, 1, 0, 1], (2, 4): [1, 1, 0, 0, 1], (3, 2): [1, 0, 1], (3, 3): [2, 2, 0, 1],
         (5, 2): [3, 0, 1], (7, 2): [1, 0, 1], (11, 2): [1, 0, 1], (13, 2): [2, 0, 1]}  # monic, low->high


def find_irred(p, r):
    # smallest monic irreducible of degree r over F_p (low->high), by checking no root in F_{p^k}, k <= r/2,
    # via brute-force trial division by all monic polynomials of degree 1..r//2
    def pdiv_rem(a, b):
        a = a[:]
        while len(a) >= len(b):
            c = a[-1]
            if c:
                sh = len(a) - len(b)
                for i, bi in enumerate(b):
                    a[sh + i] = (a[sh + i] - c * bi) % p
            a.pop()
        return a
    for v in range(p ** r):
        cand = [(v // p**i) % p for i in range(r)] + [1]
        if cand[0] == 0:
            continue
        ok = True
        for d in range(1, r // 2 + 1):
            for u in range(p ** d):
                g = [(u // p**i) % p for i in range(d)] + [1]
                if not any(pdiv_rem(cand, g)):
                    ok = False; break
            if not ok: break
        if ok:
            return cand
    raise ValueError


def main():
    p, r, s = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    maxk = int(sys.argv[4]) if len(sys.argv) > 4 else 10**9
    Q = p ** r
    if r > 1:
        f = find_irred(p, r)
    # element = tuple of r components (code = sum c_i p^i); basis 1, x, x^2, ...
    elems = [tuple((v // p**i) % p for i in range(r)) for v in range(Q)]
    code = {e: v for v, e in enumerate(elems)}

    def add(a, b): return tuple((x + y) % p for x, y in zip(a, b))
    def neg(a): return tuple((-x) % p for x in a)

    def mul(a, b):
        prod = [0] * (2 * r - 1)
        for i in range(r):
            for j in range(r):
                prod[i + j] = (prod[i + j] + a[i] * b[j]) % p
        for k in range(2 * r - 2, r - 1, -1):  # reduce by monic f of degree r
            c = prod[k]
            if c:
                for t in range(r + 1):
                    prod[k - r + t] = (prod[k - r + t] - c * f[t]) % p
        return tuple(prod[:r])
    if r == 1:
        def mul(a, b): return ((a[0] * b[0]) % p,)
    one = elems[1]
    # D_r: Delta(d) = enc^{-1}(enc(d)+1 mod Q) - d
    D = sorted({add(elems[(code[d] + 1) % Q], neg(d)) for d in elems}, key=lambda e: code[e])
    # f_1(e, sigma) * Q (integer numerator)
    F = {}
    for sg in elems:
        for e in (-1, 0, 1):
            mn = min(abs(e * Q + code[add(R, sg)] - code[R]) for R in elems)
            F[(e, sg)] = max(0, mn - 1)
    zero = elems[0]
    units = elems[1:]
    best, bestk, cnt = -1, None, 0
    space = itertools.product(units, repeat=s - 1)
    if (Q - 1) ** (s - 1) > maxk:
        space = (tuple(random.choice(units) for _ in range(s - 1)) for _ in range(maxk))
    for k in space:
        cnt += 1
        worst = F[(1, zero)]
        for ev in itertools.product((-1, 0, 1), repeat=s - 1):
            if not any(ev):
                continue
            mv = [i for i in range(s - 1) if ev[i]]
            for dl in itertools.product(D, repeat=len(mv)):
                sg = zero
                for i, d in zip(mv, dl):
                    t = mul(k[i], d)
                    sg = add(sg, t if ev[i] > 0 else neg(t))
                worst = min(worst, F[(0, sg)], F[(1, sg)], F[(-1, sg)])
                if worst <= best:
                    break
            if worst <= best:
                break
        if worst > best:
            best, bestk = worst, k
    print(f"Q={Q} (p={p}, r={r}) s={s}: D_r={[code[d] for d in D]} searched {cnt} k: best beta_Q = {best}/{Q} = {best/Q:.4f}"
          f" at k(codes)={[code[x] for x in bestk] if bestk else None}")


if __name__ == "__main__":
    main()
