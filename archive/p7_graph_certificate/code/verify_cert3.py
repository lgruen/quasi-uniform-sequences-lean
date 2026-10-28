"""verify_cert3.py -- independent re-check of a 3D fault-set covering certificate (Theorem J_3) and of the
sequence it defines.  Shares NO code with sat3.py / the searches: the law kernels, scramble matrices, direct law, t-check
and certificate all come from ../t3d_audit/alib3.py (the auditor's from-the-definitions library); the covering and
combination checks are re-implemented here from the written statement (Theorem thm:p7, Appendix app:p7).

Certificate JSON: {"p","places","mu","theta", "F": [F_0, F_1, F_2]}  (F_c = list of (o, x1, x2) for COLUMN c:
  o = own partial sum of column c, x1 = cross into coordinate c+1, x2 = cross into coordinate c+2)
or the sat3.py symmetric output {"p","theta","rho","F": [...]} (then places = mu_3, mu_c = zeta^{-c} rho^c, F_c = F).

Checks:
  (i)   X^(1)_c (forced depth-0 cross of column c, computed from the law kernels) is in G_c = proj F_c
  (ii)  covering: for every x in G_c and beta in F_p^2 there is o with (o,x) in F_c and beta + o*u_c in G_c,
        u_c = depth-l direction of column c (read off the kernels: d X^(l+1)/d O^(l) at fixed history)
  (iii) every certificate combination (all 26 steps e, ordered column triples t_c in F_c for c in supp e) >= tau
  then the canonical greedy (smallest Q_l in 0..p-1) to depth D, never stuck (+ all triples in F_c),
  direct linear-algebra law == predicted partial sums for K <= Klaw, t=0 for m <= Mt, LB_K (from the DIRECT law) >= tau
  for K <= Kcert, and writes a cms3x-format witness (rows = Rw) + algs_mind2 inputs for P_3, P_6.
usage: python verify_cert3.py cert.json tau D Klaw Mt Kcert Rw witness_out [dump_prefix]
"""
import sys, os, json, itertools, math
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 't3d_audit'))
import alib3 as A

def main():
    cert = json.load(open(sys.argv[1])); tau = float(sys.argv[2])
    D, Klaw, Mt, Kcert, Rw = map(int, sys.argv[3:8]); wout = sys.argv[8]
    dump = sys.argv[9] if len(sys.argv) > 9 else None
    p = cert['p']; theta = cert['theta']
    if 'places' in cert:
        places = cert['places']; mu = cert['mu']; Fs = [[tuple(t) for t in F] for F in cert['F']]
    else:
        z = next(pow(g, (p - 1) // 3, p) for g in range(2, p) if pow(g, (p - 1) // 3, p) != 1)
        rho = cert['rho']
        places = [1, z, z * z % p]
        mu = [pow(z, (-c) % 3, p) * pow(rho, c, p) % p for c in range(3)]
        Fs = [[tuple(t) for t in cert['F']]] * 3
    print(f"p={p} places={places} mu={mu} theta={theta} |F_c|={[len(F) for F in Fs]} tau={tau}")
    N = D + 3
    U, H, G, h0 = A.kernels(places, p, N)
    kap = lambda c, cp: A.kappa(places, mu, h0, p, c, cp)
    # column cp: own uses H[cp], cross into c uses -kappa(c,cp) theta^{n+1} [w^n](G[c][cp] Q)
    def col_coefs(cp, Q, n):
        """increments at depth n for column cp given Q[0..n]: (own_n (n>=1), cross_{cp+1,n}, cross_{cp+2,n})"""
        own = 0
        if n >= 1:
            own = (-pow(theta, n, p) * sum(H[cp][n - k] * Q[k] for k in range(n + 1))) % p
        cr = []
        for d in (1, 2):
            c = (cp + d) % 3
            cr.append((-kap(c, cp) * pow(theta, n + 1, p) * sum(G[c][cp][n - k] * Q[k] for k in range(n + 1))) % p)
        return own, cr[0], cr[1]
    ok = True
    # depth-l direction u_c: coefficient of Q_l in (cross_{l}) divided by its coefficient in own_l
    for cp in range(3):
        F = set(Fs[cp]); Gs = set((x1, x2) for (_, x1, x2) in F)
        W = {}
        for (o, x1, x2) in F: W.setdefault((x1, x2), set()).add(o)
        dO = (-pow(theta, 1, p) * H[cp][0]) % p
        dX = [(-kap((cp + d) % 3, cp) * pow(theta, 2, p) * G[(cp + d) % 3][cp][0]) % p for d in (1, 2)]
        u = tuple(x * A.inv(dO, p) % p for x in dX)   # same ratio at every depth l (theta^l cancels)
        _, x1, x2 = col_coefs(cp, [1], 0)
        i_ok = (x1, x2) in Gs
        ii_ok = all(any(((b1 + o * u[0]) % p, (b2 + o * u[1]) % p) in Gs for o in W[x])
                    for x in Gs for b1 in range(p) for b2 in range(p))
        print(f" column {cp}: u={u} X^(1)={(x1, x2)} |G|={len(Gs)} fibre sizes={sorted(set(len(v) for v in W.values()))}"
              f"  (i) {'OK' if i_ok else 'FAIL'}  (ii) {'OK' if ii_ok else 'FAIL'}")
        ok &= i_ok and ii_ok
    # (iii) all combinations
    TT = A.Ttab(p); best = 9.0; worst = None
    for e in itertools.product((-1, 0, 1), repeat=3):
        if e == (0, 0, 0): continue
        nz = [c for c in range(3) if e[c]]
        for ts in itertools.product(*[Fs[c] for c in nz]):
            tc = dict(zip(nz, ts)); s = 0.0
            for c in range(3):
                Dl = 0
                for cp in nz:
                    t = tc[cp]
                    Dl += e[cp] * (t[0] if cp == c else t[(c - cp) % 3])
                s += TT[e[c]][Dl % p] ** 2
            if s < best: best = s; worst = (e, ts)
    lbF = math.sqrt(best)
    print(f" (iii) min certificate over all combinations from F: {lbF:.4f} (worst {worst})  {'OK' if lbF >= tau - 1e-9 else 'FAIL'}")
    ok &= lbF >= tau - 1e-9
    # canonical greedy per column
    Qs = []
    for cp in range(3):
        F = set(Fs[cp]); Gs = set((x1, x2) for (_, x1, x2) in F)
        Q = [1]; _, X1, X2 = col_coefs(cp, Q, 0); O = 0
        seen = set()
        for l in range(1, D + 1):
            found = False
            for q in range(p):
                o, c1, c2 = col_coefs(cp, Q + [q], l)
                On = (O + o) % p
                if (On, X1, X2) in F and ((X1 + c1) % p, (X2 + c2) % p) in Gs:
                    seen.add((On, X1, X2)); Q.append(q); O, X1, X2 = On, (X1 + c1) % p, (X2 + c2) % p
                    found = True; break
            if not found:
                print(f" greedy column {cp} STUCK at depth {l}"); ok = False; break
        Qs.append(Q)
        print(f" greedy column {cp}: depth {len(Q)-1} reached, distinct triples realised {len(seen)}; Q[:24]={Q[:24]}")
    # scramble matrices from the definition, direct law
    M = max(Rw, 3 * Klaw + 1, 3 * Kcert + 1, Mt + 1)
    Ls = [A.scramble_L(places, c, mu[c], theta, Qs[c][:M], p, M) for c in range(3)]
    Cs = [A.gen_matrix(Ls[c], places[c], p, M, M) for c in range(3)]
    # predicted partial sums partial[c][cp][l] from the column increments
    for K in range(1, max(Klaw, Kcert) + 1):
        law = A.direct_law(Cs, K, p); P = A.partial_from_direct(law, K, p)
        if K <= Klaw:
            for cp in range(3):
                O = 0; X = [0, 0]
                for l in range(1, K + 1):
                    o, _, _ = col_coefs(cp, Qs[cp], l); O = (O + o) % p
                    _, c1, c2 = col_coefs(cp, Qs[cp], l - 1); X = [(X[0] + c1) % p, (X[1] + c2) % p]
                    if not (P[cp][cp][l] == O and P[(cp + 1) % 3][cp][l] == X[0] and P[(cp + 2) % 3][cp][l] == X[1]):
                        print(f"  LAW MISMATCH K={K} col {cp} l={l}"); ok = False
        if K <= Kcert:
            lb = A.certificate(P, K, p, TT)
            print(f"  K={K}: direct-law certificate LB_K={lb:.4f} {'>= tau' if lb >= tau - 1e-9 else 'BELOW tau !!'}")
            ok &= lb >= tau - 1e-9
    print(f" law(direct) == Prop LI_3 partial sums for K <= {Klaw}: {'OK' if ok else 'see above'}")
    bad = A.tvalue_zero_upto(Cs, Mt, p)
    print(f" t=0 (sequence criterion, all compositions) for m <= {Mt}: {'OK' if bad is None else 'FAIL ' + str(bad)}")
    ok &= bad is None
    with open(wout, 'w') as f:
        f.write(f"# thm:p7 witness from {os.path.basename(sys.argv[1])}: places={places} mu={mu} theta={theta}\n")
        f.write(f"{p} {places[2]} {Rw} {Kcert} {tau} {places[0]} {places[1]} {places[2]}\n")
        for c in range(3):
            for i in range(Rw):
                f.write(' '.join(str(Ls[c][i][k]) for k in range(Rw)) + '\n')
    if dump:
        for K in (1, 2):
            m = 3 * K
            with open(f"{dump}_m{m}.txt", 'w') as f:
                f.write(f"{p} {m} 3\n")
                for C in Cs:
                    for i in range(m): f.write(' '.join(str(C[i][j]) for j in range(m)) + '\n')
    json.dump({'Q': Qs}, open(wout + '.Q.json', 'w'))
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")

if __name__ == '__main__':
    main()
