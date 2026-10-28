r"""verify_designs.py -- data-only verifier for the archived window designs of the paper (archive README.md).

Reads ONLY data files: cfg records (sp_check format, blank-line separated; optional lines `frame`, `superdiag`,
`order`, `heights`, `member`) or a brick-star CSV table (certs3.csv format of the research repository).  For every record it recomputes from scratch and checks
the hypotheses of Prop CW_s (`prop:steer`), and evaluates the window certificate of `lem:cert` (j = 1):
  (0) p prime >= 5; places pairwise distinct mod p; theta, gauge rho_c, w'(a_c) nonzero mod p;
  (1) kappa_{c<-j} = theta rho_c / (rho_j w'(a_c)(a_j - a_c)) in F_p (sp convention) and, separately, the paper's
      prop:LI(c) form theta g_c/(g_j w'(a_j)(a_j - a_c)) with g_c = rho_c/w'(a_c); both must equal the stored kappa_row;
  (2) if the record carries the rational design (frame + theta + superdiag [Theorem LF] or heights [Theorem MR]): the
      rational gauge is rebuilt (Lemma CF: G_0 = 1, G_t = G_{t-1} d_t w'(a_{t-1})(a_t - a_{t-1})/theta, rho = 1/G; MR:
      rho_c = (s-1-c)!/(h_1..h_c), theta = (s-1)!/g), every upper kappa must be an INTEGER equal to the stored centred
      value, every kappa (all c != j) must agree mod p with (1), and all numerators/denominators must be prime to p;
  (3) forced crosses: -kappa_{c<-j} lies in the window W_{c<-j} for every c != j;
  (4) covering (ii) per column: EXACT (cover_helper: d<=2 always, d>=3 brute force when p^(d-1) <= BRUTE) or, for
      larger lex columns, the Lemma WS certificate in the stored row order (records with `order`/`heights` only):
      (W) nu_1 <= |I_1|, N_1 = 1 + ceil((p-|I_1|)/nu_1); (S_t) N_{t-1} nu_t <= |I_t|, N_t = N_{t-1} - 1 + ceil(p/nu_t);
      own run length >= N_k;
  (5) exact product-window lem:cert LB: minS = min over steps e in {-1,0,1}^s \ 0 (up to sign) of
      sum_c (p f_1(e_c, sigma_c))^2 minimised over the integer sumset interval of row c (f_1 from rem:onedigit,
      cross-checked against its definition min_R |e p + ((R+sigma) mod p) - R| - 1 for p <= 300); LB = sqrt(minS)/p.
      Compared with the stored minS (exact integer) when present;
  (6) lex designs: LEX pattern (lower crosses full, upper narrow), Gamma = max_c (2X_c + M_c) and the Lemma LEX value
      min_c (p - A_c - M_c - X_c)/p, which must EQUAL the exact LB (rem:lexexact) and be >= (p - Gamma)/p.
PASS = all applicable checks hold and LB > 0.  Output: one line per record + a summary line.
usage: python3 verify_designs.py [--brute N] [--range a b] file [file ...]"""
import sys, os, math, subprocess, itertools
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__)); HELPER = os.path.join(HERE, 'cover_helper')
BRUTE = 2e6

def isprime(n): return n > 1 and all(n % d for d in range(2, int(n ** .5) + 1))
def cen(x, p): x %= p; return x - p if x > p // 2 else x
def inv(x, p):
    x %= p
    if x == 0: raise ZeroDivisionError
    return pow(x, p - 2, p)
def inwin(x, w, p): lo, hi = w; return hi - lo + 1 >= p or (x - lo) % p <= hi - lo
def wlen(w): return w[1] - w[0] + 1

# ---------------------------------------------------------------- parsing
def parse_cfg_text(txt):
    d = {'win': {}, 'krow': [], 'order': {}}
    for line in txt.split('\n'):
        t = line.split()
        if not t: continue
        k = t[0]
        if k == 's': d['s'] = int(t[1]); d['p'] = int(t[3]); d['theta'] = int(t[5])
        elif k == 'places': d['a'] = [int(x) for x in t[1:]]
        elif k in ('rho', 'lambda'): d['rho'] = [int(x) for x in t[1:]]
        elif k == 'kappa_row': d['krow'].append([int(x) for x in t[1:]])
        elif k == 'win': j = int(t[1]); v = [int(x) for x in t[2:]]; d['win'][j] = [(v[2 * i], v[2 * i + 1]) for i in range(len(v) // 2)]
        elif k == 'minS': d['minS'] = int(t[1])
        elif k == 'superdiag': d['superdiag'] = [int(x) for x in t[1:]]
        elif k == 'heights': d['heights'] = [int(x) for x in t[1:]]
        elif k == 'order': d['order'][int(t[1])] = [int(x) for x in t[2:]]
        elif k == 'frame':
            i = t.index('theta'); d['frame'] = [Fr(x) for x in t[1:i]]; d['theta_q'] = Fr(t[i + 1])
        elif k == 'member': d['member'] = t[1]
    # W[c][j] = window of column j in coordinate c
    s = d['s']; d['W'] = [[d['win'][j][c] for j in range(s)] for c in range(s)]
    return d

def records(fn):
    if fn.endswith('.csv'):
        lines = open(fn).read().strip().split('\n'); hdr = lines[0].split(',')
        for ln in lines[1:]:
            F = dict(zip(hdr, ln.split(',')))
            p = int(F['p']); k = {(1, 0): 'k10', (2, 0): 'k20', (0, 1): 'k01', (2, 1): 'k21', (0, 2): 'k02', (1, 2): 'k12'}
            W = [[None] * 3 for _ in range(3)]
            for cp in range(3):
                v = [int(x) for x in F[f'win{cp}'].split(':')]; oth = [c for c in range(3) if c != cp]
                W[cp][cp] = (v[0], v[1]); W[oth[0]][cp] = (v[2], v[3]); W[oth[1]][cp] = (v[4], v[5])
            krow = [[0 if c == j else int(F[k[(c, j)]]) for j in range(3)] for c in range(3)]
            yield f'{os.path.basename(fn)}:p{p}', {'s': 3, 'p': p, 'theta': int(F['theta']), 'a': [0, 1, int(F['t'])],
                  'rho': [int(F[f'rho{c}']) for c in range(3)], 'krow': krow, 'W': W, 'order': {}, 'member': 'brickstar_csv',
                  'claimLB': float(F['LB'])}
    else:
        txt = open(fn).read()
        blocks = [b for b in txt.split('\n\n') if b.strip().startswith('s ')]
        for i, b in enumerate(blocks):
            d = parse_cfg_text(b); yield f'{os.path.basename(fn)}:p{d["p"]}' + (f'#{i}' if len(blocks) == 1 else ''), d

# ---------------------------------------------------------------- f_1 and the certificate
def pf1(e, sg, p):
    r = sg % p
    if e == 0: m = min(r, p - r); return m - 1 if m > 0 else 0
    if e < 0: r = (-sg) % p
    return p - 1 if r == 0 else r - 1
def pf1_def(e, sg, p): return max(0, min(abs(e * p + (R + sg) % p - R) for R in range(p)) - 1)
def pf1min(e, lo, hi, p):
    """exact min of p f_1(e, .) over integers in [lo, hi]: candidates = endpoints and the points = -1, 0, 1 mod p."""
    if hi - lo + 1 >= p: return min(pf1(e, x, p) for x in range(p))
    cand = {lo, hi}
    for r in (-1, 0, 1):
        x = lo + (r - lo) % p
        if x <= hi: cand.add(x)
    return min(pf1(e, x, p) for x in cand)
def window_minS(s, p, W):
    best, arg = None, None
    for e in itertools.product((-1, 0, 1), repeat=s):
        f = next((x for x in e if x), 0)
        if f != 1: continue
        tot = 0
        for c in range(s):
            lo = hi = 0; full = False
            for j in range(s):
                if not e[j]: continue
                w = W[c][j]
                if wlen(w) >= p: full = True
                if e[j] > 0: lo += w[0]; hi += w[1]
                else: lo -= w[1]; hi -= w[0]
            m = pf1min(e[c], 0, p - 1, p) if full else pf1min(e[c], lo, hi, p)
            tot += m * m
            if best is not None and tot >= best: break
        if best is None or tot < best: best, arg = tot, e
    return best, arg

# ---------------------------------------------------------------- gauge / kappa
def wprime_q(a, c): return math.prod((a[c] - a[e]) for e in range(len(a)) if e != c)
def kappa_F(d):
    s, p, th, a, rho = d['s'], d['p'], d['theta'], d['a'], d['rho']
    wp = [math.prod((a[c] - a[e]) for e in range(s) if e != c) % p for c in range(s)]
    g = [rho[c] * inv(wp[c], p) % p for c in range(s)]
    k1 = [[0] * s for _ in range(s)]; k2 = [[0] * s for _ in range(s)]
    for c in range(s):
        for j in range(s):
            if c != j:
                k1[c][j] = th * rho[c] * inv(rho[j] * wp[c] * (a[j] - a[c]), p) % p
                k2[c][j] = th * g[c] * inv(g[j] * wp[j] * (a[j] - a[c]), p) % p
    return k1, k2, wp
def rational_design(d):
    """returns (frame, theta, rho) over Q from the stored rational design, or None."""
    s = d['s']
    if 'heights' in d:
        a = [Fr(c) for c in range(s)]; m = {}
        for c in range(s):
            for j in range(c + 1, s): m[c, j] = math.factorial(s - 1) // (math.factorial(c) * math.factorial(s - 1 - j) * (j - c))
        g = 0
        for v in m.values(): g = math.gcd(g, v)
        th = Fr(math.factorial(s - 1), g); h = [1] + d['heights']
        rho = [Fr(math.factorial(s - 1 - c), math.prod(h[1:c + 1])) for c in range(s)]
        return a, th, rho, 'MR'
    if 'frame' in d and 'superdiag' in d:
        a, th, dd = d['frame'], d['theta_q'], [None] + d['superdiag']
        G = [Fr(1)]
        for t in range(1, s): G.append(G[-1] * dd[t] * wprime_q(a, t - 1) * (a[t] - a[t - 1]) / th)
        return a, th, [1 / x for x in G], 'LF'
    return None
def check_rational(d, kF):
    s, p = d['s'], d['p']; r = rational_design(d)
    if r is None: return 'none', True
    a, th, rho, kind = r; ok = True
    nums = [th, *(a[c] - a[e] for c in range(s) for e in range(s) if c != e), *rho] + [Fr(x) for x in d.get('superdiag', [])]
    for q in nums:
        if q == 0 or q.numerator % p == 0 or q.denominator % p == 0: ok = False
    if not ok: return kind + ':denominator', False
    # stored places must be the frame mod p
    if any((a[c].numerator * inv(a[c].denominator, p) - d['a'][c]) % p for c in range(s)): return kind + ':places', False
    for c in range(s):
        for j in range(s):
            if c == j: continue
            kq = th * rho[c] / (rho[j] * wprime_q(a, c) * (a[j] - a[c]))
            if (kq.numerator * inv(kq.denominator, p) - kF[c][j]) % p: return kind + ':modp', False
            if c < j and (kq.denominator != 1 or kq.numerator != d['krow'][c][j]): return kind + ':integer', False
    return kind, True

# ---------------------------------------------------------------- covering
def ws_check(p, rows_order, kv, Wcol, Mown):
    N = None
    for i, r in enumerate(rows_order):
        nu = abs(cen(kv[r], p)); I = wlen(Wcol[r])
        if nu < 1 or I >= p: return False
        if i == 0:
            if nu > I: return False
            N = 1 + -(-(p - I) // nu)
        else:
            if N * nu > I: return False
            N = N - 1 + -(-p // nu)
    return N is not None and Mown >= N
def verify(recs, helper):
    out = []; queries = []
    for name, d in recs:
        s, p = d['s'], d['p']; why = []
        if not isprime(p) or p < 5: why.append('notprime')
        if len({x % p for x in d['a']}) < s: why.append('places')
        if d['theta'] % p == 0 or any(x % p == 0 for x in d['rho']): why.append('zero')
        if why: out.append([name, d, why, None, None]); continue
        k1, k2, wp = kappa_F(d)
        if k1 != k2: why.append('kappa-conv')
        if d['krow'] and any((d['krow'][c][j] - k1[c][j]) % p for c in range(s) for j in range(s) if c != j): why.append('kappa_row')
        kind, rok = check_rational(d, k1)
        if not rok: why.append('rational:' + kind)
        W = d['W']
        if any(not inwin(-k1[c][j], W[c][j], p) for c in range(s) for j in range(s) if c != j): why.append('forced')
        if any(wlen(W[c][j]) < 1 for c in range(s) for j in range(s)): why.append('emptywin')
        lex = all((wlen(W[c][j]) >= p) == (c > j) for c in range(s) for j in range(s) if c != j)
        cov = []
        for j in range(s):
            rows = [c for c in range(s) if c != j and wlen(W[c][j]) < p]; M = wlen(W[j][j]); dd = len(rows)
            order = d['order'].get(j) or (list(range(j)) if 'heights' in d else None)
            if dd <= 2 or p ** (dd - 1) <= BRUTE:
                queries.append(f"{p} {dd} {M} " + " ".join(f"{k1[r][j]} {wlen(W[r][j])}" for r in rows)); cov.append(('EXACT', len(queries) - 1))
            elif order is not None and sorted(order) == sorted(rows):
                cov.append(('WS', ws_check(p, order, [k1[r][j] for r in range(s)], [W[r][j] for r in range(s)], M)))
            else: cov.append(('NONE', False))
        out.append([name, d, why, cov, lex])
    res = subprocess.run([helper], input='\n'.join(queries) + '\n', capture_output=True, text=True).stdout.split()
    if any(x not in ('0', '1') for x in res) or len(res) != len(queries): raise SystemExit('cover_helper failure: ' + ' '.join(res[:5]))
    lines = []; npass = 0
    for name, d, why, cov, lex in out:
        s, p = d['s'], d['p']; meth = []; LB = None
        if cov is not None:
            for j, (m, v) in enumerate(cov):
                okc = (res[v] == '1') if m == 'EXACT' else v
                meth.append(m[0]);
                if not okc: why.append(f'cover{j}({m})')
            minS, arg = window_minS(s, p, d['W']); LB = math.sqrt(minS) / p
            if 'minS' in d and d['minS'] != minS: why.append(f'minS({d["minS"]}!={minS})')
            if 'claimLB' in d and abs(d['claimLB'] - LB) > 1e-6: why.append('claimLB')
            if minS <= 0: why.append('LB=0')
            extra = ''
            if lex:
                W = d['W']; X = [sum((wlen(W[c][j]) - 1) // 2 for j in range(c + 1, s)) for c in range(s)]
                M = [wlen(W[c][c]) for c in range(s)]; A = [-W[c][c][1] for c in range(s)]
                Gam = max(2 * X[c] + M[c] for c in range(s)); lexv = min(p - A[c] - M[c] - X[c] for c in range(s))
                if any(W[c][j][0] != -W[c][j][1] for c in range(s) for j in range(c + 1, s)): why.append('asym-cross')
                if lexv * lexv != minS: why.append(f'LEX-equality({lexv}^2!={minS})')
                if p - Gam > math.isqrt(minS): why.append('Gamma>LB')
                extra = f' Gamma={Gam}'
        st = 'PASS' if not why else 'FAIL'; npass += (st == 'PASS')
        lines.append(f"{st} {name} s={s} p={p} {d.get('member','')} cover={''.join(meth)}" + (f" LB={LB:.6f}" if LB is not None else '') + (extra if cov is not None else '') + ('' if not why else ' WHY=' + ','.join(why)))
    return lines, npass
if __name__ == '__main__':
    args = sys.argv[1:]
    rng = None
    while args and args[0].startswith('--'):
        if args[0] == '--brute': BRUTE = float(args[1]); args = args[2:]
        elif args[0] == '--range': rng = (int(args[1]), int(args[2])); args = args[3:]   # record index range [a, b)
    for e in (-1, 0, 1):
        for p in (5, 7, 11, 13, 101):
            for sg in range(-2 * p, 2 * p): assert pf1(e, sg, p) == pf1_def(e, sg, p)
            import random; rnd = random.Random(p * 7 + e)
            for _ in range(200):
                lo = rnd.randint(-3 * p, 3 * p); hi = lo + rnd.randint(0, p + 2)
                assert pf1min(e, lo, hi, p) == min(pf1(e, x, p) for x in range(lo, hi + 1))
    if not os.path.exists(HELPER): subprocess.run(['g++', '-O3', '-o', HELPER, HELPER + '.cpp'], check=True)
    tot = totp = 0
    for fn in args:
        R = list(records(fn))
        if rng: R = R[rng[0]:rng[1]]
        lines, npass = verify(R, HELPER); tot += len(lines); totp += npass
        for l in lines: print(l)
        print(f'## {fn}: {npass}/{len(lines)} PASS', flush=True)
    print(f'## TOTAL {totp}/{tot} PASS')
