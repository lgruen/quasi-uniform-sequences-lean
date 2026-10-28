# law_audit.py -- audit: (1) U's law Lambda in rho-digits from generator matrices (theta=1, v=1), K-independence and
# column sums 0; (2) CHECK of (R-law) for random digit-scaled U against the law solved from generator matrices;
# (3) writes the law file for bb_audit (format: p s D then Lam[c][c'][d]).   usage: law_audit.py p s places Kbig [outfile]
import sys, random, time
from gen7 import *
p, s = int(sys.argv[1]), int(sys.argv[2]); a = [int(x) % p for x in sys.argv[3].split(',')]; Kb = int(sys.argv[4])
t0 = time.time(); rng = random.Random(3)
ones = [[1] * s for _ in range(Kb + 2)]
C = digit_scaled_U(p, a, ones, Kb + 1, s * Kb)
Lams = {}
for K in range(1, Kb + 1):
    Lw = law(C, s, K, p)
    Lams[K] = [[[Lw[c][cp * K + (K - 1 - d)] for d in range(K)] for cp in range(s)] for c in range(s)]
Lam = Lams[Kb]
kind = all(Lams[K][c][cp][d] == Lam[c][cp][d] for K in Lams for c in range(s) for cp in range(s) for d in range(K))
csum = all(sum(Lam[c][cp][d] for c in range(s)) % p == 0 for cp in range(s) for d in range(Kb))
print('p=%d s=%d places=%s: Lambda K-independent (K<=%d): %s; column sums 0: %s' % (p, s, a, Kb, kind, csum))
# R-law check
bad = 0; tot = 0
for trial in range(3):
    Kt = min(Kb, 7)
    mu = [[rng.randrange(1, p) for _ in range(s)] for _ in range(Kt + 1)]
    Cd = digit_scaled_U(p, a, mu, Kt + 1, s * Kt)
    for K in range(1, Kt + 1):
        D = responses(law(Cd, s, K, p), s, K, p)
        u = [[inv(mu[n][c], p) for c in range(s)] for n in range(Kt + 1)]
        for l in range(1, K + 1):
            for c in range(s):
                for cp in range(s):
                    f = inv(u[K][c], p) * sum(Lam[c][cp][d] * u[K - 1 - d][cp] for d in range(l)) % p
                    tot += 1; bad += (f != D[l][c][cp])
print('R-law vs generator-matrix law (random digit-scaled U): %d/%d entries agree' % (tot - bad, tot))
with open(sys.argv[5] if len(sys.argv) > 5 else 'lam7_%d_%d.txt' % (p, s), 'w') as f:
    f.write('%d %d %d\n' % (p, s, Kb))
    f.write(' '.join(str(Lam[c][cp][d]) for c in range(s) for cp in range(s) for d in range(Kb)) + '\n')
print('time %.1fs' % (time.time() - t0))
