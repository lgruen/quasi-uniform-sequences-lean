"""Audit: independent evaluation of the predicate Pi(p) of Proposition prop:P0, written from the written statement,
with the n-table recomputed from the design (lemR.py logic). Exact Fractions."""
from fractions import Fraction as F
def design(rule):
    if rule == 'A':
        a=[F(0),F(1),F(-5)]; g=[F(24,5),F(1),F(-2,5)]; th=F(900); b=1; W=(F(1,50),F(7,200),F(1,10)); u=F(11,400000)
    else:
        a=[F(0),F(1),F(2)]; g=[F(1),F(-56),F(6)]; th=F(84); b=0; W=(F(27,1000),F(1,200),F(1,10)); u=F(891,78400000)
    wp=lambda c: __import__('math').prod([a[c]-a[d] for d in range(3) if d!=c])
    n={(c,d): th*g[c]/(g[d]*wp(d)*(a[d]-a[c])) for c in range(3) for d in range(3) if c!=d}
    return n,b,W,u
def Pi(rule,p):
    n,b,(wbc,wcc,wcb),u=design(rule); s=3; C=[c for c in range(3) if c!=b]; p=F(p)
    if not u*p>2: return False,None
    def col(entries):   # list of (k|n|, w) ; returns N^+_{last}
        entries=sorted(entries,key=lambda t:-t[0])
        nm=lambda kn: kn*(u*p-2); npl=lambda kn: kn*u*p; ell=lambda w: 2*w*p-1
        kn,w=entries[0]
        if npl(kn)>ell(w): return None
        N=2+max(F(0),(p-ell(w))/nm(kn))
        for kn,w in entries[1:]:
            if N*npl(kn)>ell(w): return None
            N=N+p/nm(kn)
        return N
    Mb=col([(abs(n[(j,b)]),wbc) for j in C])
    if Mb is None: return False,None
    M=0
    for i in C:
        N=col([(2*abs(n[(c,i)]), wcb if c==b else wcc) for c in range(3) if c!=i])
        if N is None: return False,None
        M=max(M,2*N-1)
    for j in C:
        if abs(n[(j,b)])*u*p>wbc*p-1: return False,None
        for i in C:
            if i!=j and abs(n[(j,i)])*u*p>wcc*p-1: return False,None
    for i in C:
        if abs(2*n[(b,i)])*u*p>2*(wcb*p-1)-1: return False,None
    x=1-(s-2)*wcc-2*wbc; y=F(1,2)-wcb; D=x*x+y*y-1
    ok = (D>0 and p*D>=2*x*M+2*y*(Mb+F(1,2)) and 1-2*(s-2)*wcc-2*wbc-M/p>=F(7072,10000)
          and (2*(s-2)*wcc+2*wbc)*p+M+2<=p-1 and 2*wcb*p+2*Mb+2<p-1)
    return ok,(float(Mb),float(M))
for rule,p0 in (('A',1789760),('B',19673600)):
    print(rule,"Pi(p0)=",Pi(rule,p0),"Pi(0.99 p0)=",Pi(rule,int(0.99*p0))[0])
    # monotonicity sample on a geometric grid
    flips=0; prev=False
    for e in range(500):
        q=int(10**(4+e*0.02)); v=Pi(rule,q)[0]
        if prev and not v: flips+=1
        prev=v
    print(rule,"true->false flips on grid 1e4..1e14:",flips)
