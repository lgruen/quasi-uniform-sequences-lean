# lb.py -- third program (the program of the search): one-digit relaxation (lem:cert, j=1) for an exact bounded-depth design.
# Design F_0..F_{L-1} (s x s, entries mod q), M^{(j)} = F_0+..+F_j; carry depths capped at L-1.
# Two variants: 'H2' (jit_i = 0 for single-axis steps, needs a hypothesis of [Gru26geo], not used here) and 'noH2' (jit = 1 always; always valid).
# usage: python lb.py q design   (design names as in blockgen.py)
import sys, itertools, math
sys.path.insert(0, __import__('os').path.dirname(__file__))
from blockgen import designs

def LB(q, F, h2):
    s = len(F[0]); L = len(F)
    Mj = []; acc = [[0] * s for _ in range(s)]
    for Fn in F:
        acc = [[acc[i][j] + Fn[i][j] for j in range(s)] for i in range(s)]; Mj.append([r[:] for r in acc])
    best = 10.0; arg = None
    for e in itertools.product((-1, 0, 1), repeat=s):
        if not any(e): continue
        first = next(x for x in e if x)
        if first < 0: continue  # up to sign
        mov = [d for d in range(s) if e[d]]
        single = len(mov) == 1
        for js in itertools.product(range(L), repeat=len(mov)):
            tot = 0.0
            for i in range(s):
                sig = sum(e[d] * Mj[js[k]][i][d] for k, d in enumerate(mov)) % q
                jit = 0 if (single and h2 and e[i] != 0) else 1
                ts = [0] if sig == 0 else [sig, sig - q]
                b = min(max(0, abs(e[i] * q + t) - jit) for t in ts)
                tot += b * b
            val = math.sqrt(tot) / q
            if val < best: best = val; arg = (e, js)
    return min(1.0, best), arg

if __name__ == '__main__':
    q = int(sys.argv[1]); d = designs(sys.argv[2], q)
    F = [[[x % q for x in r] for r in Fn] for Fn in d['F']]
    for h2 in (False, True):
        v, arg = LB(q, F, h2)
        print('q=%d %s: LB=%.6f  (1-2/q=%.6f, 1-1/q=%.6f) argmin %s' % (q, 'H2  ' if h2 else 'noH2', v, 1 - 2 / q, 1 - 1 / q, arg))
