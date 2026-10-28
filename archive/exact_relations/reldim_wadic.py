# Method B, independent cross-check of reldim_rows.py via Lemma lem:reltype: relations among residue rows K-J..K on
# deg V < sK <-> numerators A (deg <= s-1) whose w-adic coefficients nu_{c,k} vanish for J < k <= K at every place.
import sys
def inv(a,p): return pow(a%p,p-2,p)
def mul(f,g,N,p):
    h=[0]*N
    for i,a in enumerate(f[:N]):
        if a:
            for j,b in enumerate(g[:N-i]): h[i+j]=(h[i+j]+a*b)%p
    return h
def polyval_series(coeffs,zs,N,p):  # sum coeffs[k] * zs^k
    out=[0]*N; pw=[1]+[0]*(N-1)
    for ck in coeffs:
        out=[(o+ck*x)%p for o,x in zip(out,pw)]; pw=mul(pw,zs,N,p)
    return out
def local_root(places,c,N,p):
    # solve w(z)=u for z = a_c + sum_{k>=1} z_k u^k by fixed-point iteration on coefficients
    a=places[c]; z=[a]+[0]*(N-1)
    wcoef=[1]
    for b in places: wcoef=[( (wcoef[i-1] if i>0 else 0) - b*(wcoef[i] if i<len(wcoef) else 0))%p for i in range(len(wcoef)+1)]
    # wcoef: low->high? build properly
    return z,wcoef
def wpoly(places,p):
    w=[1]  # low->high coefficients
    for b in places:
        w=[((w[i-1] if i>=1 else 0) - b*(w[i] if i<len(w) else 0))%p for i in range(len(w)+1)]
    return w
def root_series(places,c,N,p):
    w=wpoly(places,p); a=places[c]
    wp=sum(k*w[k]*pow(a,k-1,p) for k in range(1,len(w)))%p
    z=[a]+[0]*(N-1)
    for it in range(N+1):  # Newton-like: z <- z - (w(z)-u)/w'(a)
        wz=polyval_series(w,z,N,p); wz[1]=(wz[1]-1)%p
        z=[(zi - inv(wp,p)*e)%p for zi,e in zip(z,wz)]
    return z
def rank(M,p):
    M=[r[:] for r in M]; r=0
    for col in range(len(M[0])):
        piv=next((i for i in range(r,len(M)) if M[i][col]%p),None)
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]; iv=inv(M[r][col],p); M[r]=[x*iv%p for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][col]: f=M[i][col]; M[i]=[(x-f*y)%p for x,y in zip(M[i],M[r])]
        r+=1
    return r
def reldim(places,J,K,p):
    s=len(places); N=K+1
    roots=[root_series(places,c,N,p) for c in range(s)]
    # condition rows: for each c, k in (J,K]: coefficient of u^k in A(z_c(u)), linear in A's coefficients (basis z^e, e<s)
    cond=[]
    for c in range(s):
        pows=[polyval_series([0]*e+[1],roots[c],N,p) for e in range(s)]
        for k in range(J+1,K+1): cond.append([pows[e][k] for e in range(s)])
    return s-rank(cond,p) if cond else s
p,s,J=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
pl=[int(x) for x in sys.argv[4].split(',')]
print([ (K,reldim(pl,J,K,p)) for K in range(J,J+6)])
