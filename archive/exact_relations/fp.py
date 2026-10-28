# Audit helpers (written from the definitions; prime p only).
# Polynomials / truncated series: lists of ints mod p, index = degree.

def shift_poly(P, a, p):
    """coefficients of P(t + a) in t"""
    n = len(P)
    out = [0] * n
    # Horner: P(t+a)
    for c in reversed(P):
        # out = out*(t+a) + c
        new = [0] * n
        for i in range(n):
            if out[i]:
                new[i] = (new[i] + out[i] * a) % p
                if i + 1 < n:
                    new[i + 1] = (new[i + 1] + out[i]) % p
        new[0] = (new[0] + c) % p
        out = new
    return out

def smul(a, b, p, N):
    r = [0] * N
    for i, x in enumerate(a[:N]):
        if x:
            for j, y in enumerate(b[:N - i]):
                if y:
                    r[i + j] = (r[i + j] + x * y) % p
    return r

def sinv(a, p, N):
    inv0 = pow(a[0] % p, p - 2, p)
    r = [0] * N
    r[0] = inv0
    for n in range(1, N):
        s = 0
        for k in range(1, min(n, len(a) - 1) + 1):
            s += a[k] * r[n - k]
        r[n] = (-s * inv0) % p
    return r

def spow(a, e, p, N):
    r = [1] + [0] * (N - 1)
    for _ in range(e):
        r = smul(r, a, p, N)
    return r

def polymul(a, b, p):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] = (r[i + j] + x * y) % p
    return r

def w_poly(places, p):
    w = [1]
    for a in places:
        w = polymul(w, [(-a) % p, 1], p)
    return w

def rank_mod(M, p):
    M = [list(r) for r in M]
    rk = 0
    cols = len(M[0]) if M else 0
    for c in range(cols):
        piv = None
        for r in range(rk, len(M)):
            if M[r][c] % p:
                piv = r
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], p - 2, p)
        M[rk] = [(x * inv) % p for x in M[rk]]
        for r in range(len(M)):
            if r != rk and M[r][c] % p:
                f = M[r][c]
                M[r] = [(x - f * y) % p for x, y in zip(M[r], M[rk])]
        rk += 1
    return rk

def primes(lo, hi):
    out = []
    for n in range(max(2, lo), hi + 1):
        if all(n % d for d in range(2, int(n ** 0.5) + 1)):
            out.append(n)
    return out
