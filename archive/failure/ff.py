# Audit helpers: independent finite-field / power-series helpers (written from the definitions, prime p only).
# Polynomials and truncated power series are lists of ints mod p, index = degree.

def trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a

def padd(a, b, p):
    n = max(len(a), len(b))
    return trim([((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % p for i in range(n)])

def psub(a, b, p):
    return padd(a, [(-x) % p for x in b], p)

def pmul(a, b, p, N=None):
    if not a or not b:
        return []
    n = len(a) + len(b) - 1
    if N is not None:
        n = min(n, N)
    r = [0] * n
    for i, x in enumerate(a):
        if x == 0 or i >= n:
            continue
        for j, y in enumerate(b):
            if i + j >= n:
                break
            r[i + j] = (r[i + j] + x * y) % p
    return r if N is not None else trim(r)

def pscal(a, c, p):
    return trim([(c * x) % p for x in a])

def pdivmod(a, b, p):
    a = trim(list(a)); b = trim(list(b))
    inv = pow(b[-1], p - 2, p)
    q = [0] * max(0, len(a) - len(b) + 1)
    while len(a) >= len(b) and a:
        c = a[-1] * inv % p
        d = len(a) - len(b)
        q[d] = c
        for i, y in enumerate(b):
            a[i + d] = (a[i + d] - c * y) % p
        trim(a)
    return trim(q), a

def pmod(a, b, p):
    return pdivmod(a, b, p)[1]

def ppow(a, e, p, mod=None, N=None):
    r = [1]
    base = list(a)
    while e:
        if e & 1:
            r = pmul(r, base, p, N)
            if mod is not None:
                r = pmod(r, mod, p)
        e >>= 1
        if e:
            base = pmul(base, base, p, N)
            if mod is not None:
                base = pmod(base, mod, p)
    return r

def sinv(a, p, N):
    """inverse of a unit power series mod x^N"""
    inv0 = pow(a[0] % p, p - 2, p)
    r = [0] * N
    r[0] = inv0
    for n in range(1, N):
        s = 0
        for k in range(1, min(n, len(a) - 1) + 1):
            s += a[k] * r[n - k]
        r[n] = (-s * inv0) % p
    return r

def compose(f, g, p, N):
    """f(g(x)) mod x^N, g(0)=0 assumed (g list), f polynomial/series list."""
    r = [0] * N
    pw = [1] + [0] * (N - 1)
    for i, c in enumerate(f):
        if i >= N:
            break
        if c:
            for k in range(N):
                r[k] = (r[k] + c * pw[k]) % p
        pw = pmul(pw, g, p, N)
        pw += [0] * (N - len(pw))
    return r

def shift_poly(f, a, p):
    """f(a+t) as polynomial in t"""
    r = []
    for c in reversed(f):
        r = padd(pmul(r, [a % p, 1], p), [c], p)
    return r

def deriv(a, p):
    return trim([(i * a[i]) % p for i in range(1, len(a))])

def local_root(w, a, theta, p, N):
    """z_c(theta x) - a_c as series in x mod x^N: solves w(a+T)=theta x, T(0)=0 (Newton by fixed point)."""
    W = shift_poly(w, a, p)  # W(T) = w(a+T), W(0)=0, W'(0)!=0
    W1 = W[1]
    inv = pow(W1, p - 2, p)
    T = [0] * N
    # fixed point: T = inv*(theta x - (W(T)-W1 T))
    for _ in range(N + 1):
        WT = [0] * N
        pw = [1] + [0] * (N - 1)
        for i, c in enumerate(W):
            if i >= 2 and c:
                for k in range(N):
                    WT[k] = (WT[k] + c * pw[k]) % p
            pw = pmul(pw, T, p, N); pw += [0] * (N - len(pw))
        newT = [(-inv * WT[k]) % p for k in range(N)]
        if N > 1:
            newT[1] = (newT[1] + inv * theta) % p
        if newT == T:
            break
        T = newT
    return T

def matinv_modp(M, p):
    n = len(M)
    A = [list(r) + [1 if i == j else 0 for j in range(n)] for i, r in enumerate(M)]
    for col in range(n):
        piv = next(r for r in range(col, n) if A[r][col] % p)
        A[col], A[piv] = A[piv], A[col]
        inv = pow(A[col][col], p - 2, p)
        A[col] = [(x * inv) % p for x in A[col]]
        for r in range(n):
            if r != col and A[r][col]:
                f = A[r][col]
                A[r] = [(x - f * y) % p for x, y in zip(A[r], A[col])]
    return [r[n:] for r in A]

def rank_modp(M, p):
    A = [list(r) for r in M]
    rk = 0; rows = len(A); cols = len(A[0]) if A else 0
    for col in range(cols):
        piv = next((r for r in range(rk, rows) if A[r][col] % p), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        inv = pow(A[rk][col], p - 2, p)
        A[rk] = [(x * inv) % p for x in A[rk]]
        for r in range(rows):
            if r != rk and A[r][col]:
                f = A[r][col]
                A[r] = [(x - f * y) % p for x, y in zip(A[r], A[rk])]
        rk += 1
    return rk

def wpoly(places, p):
    w = [1]
    for a in places:
        w = pmul(w, [(-a) % p, 1], p)
    return w

def gen_residue(places, c, theta, phi_num, phi_den, p, R, M, extra_pole=0):
    """Route B (Taylor/residue): C[n][i] = Res_{a_c}( z^i * phi * (theta/w)^(n+1-extra_pole) dz ),
    phi = phi_num/phi_den polynomials in z (unit at a_c, or with a simple pole handled by extra_pole via phi_den).
    Computed as coefficient extraction in t = z - a_c with exact Laurent bookkeeping."""
    a = places[c]
    w = wpoly(places, p)
    Wt = shift_poly(w, a, p)            # = t * Wc(t)
    Wc = Wt[1:]                          # Wc(t)
    num = shift_poly(phi_num, a, p)
    den = shift_poly(phi_den, a, p)
    vden = 0
    while den[vden] == 0:
        vden += 1
    den = den[vden:]
    C = [[0] * M for _ in range(R)]
    for n in range(R):
        e = n + 1 - extra_pole           # power of theta/w
        # integrand = (a+t)^i * num/den * t^(-vden) * theta^e * t^(-e) * Wc^(-e)
        order = e + vden                 # total pole order in t; residue = [t^(order-1)] of regular part
        Nn = order + 1
        if order <= 0:
            continue
        base = pmul(num, sinv(den, p, Nn), p, Nn)
        if e >= 0:
            base = pmul(base, ppow(sinv(Wc, p, Nn), e, p, N=Nn), p, Nn)
        else:
            base = pmul(base, ppow(Wc, -e, p, N=Nn), p, Nn)
        base += [0] * (Nn - len(base))
        th = pow(theta, e % (p - 1), p)
        zi = [1]
        for i in range(M):
            prod = pmul(zi, base, p, Nn)
            val = prod[order - 1] if order - 1 < len(prod) else 0
            C[n][i] = th * val % p
            zi = pmul(zi, [a % p, 1], p)
    return C

def matvec(C, V, p):
    return [sum(C[n][i] * V[i] for i in range(min(len(V), len(C[n])))) % p for n in range(len(C))]
