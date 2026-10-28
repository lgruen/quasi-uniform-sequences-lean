"""Audit: independent check of Theorem A's s=4 instance (Faure places 0..3, b=0, J=(1,2,3), Q_r=153^r, w=7/250,
u = 0.999 w / max|n_{j<-b}|) at primes above the claimed p_0 = 1.43e16: own Lemma-R design (delta, L), kappa in F_p
from the gauge (prop:LI(c)), Lemma WS/D numbers, Lemma W, and the exact window certificate (all 40 steps)."""
from fractions import Fraction as F
import itertools, math, sys
import sympy
s=int(sys.argv[1]); b=int(sys.argv[2]); R=int(sys.argv[3]); w=F(sys.argv[4]); J=[c for c in range(s) if c!=b]; Q={r:F(R)**r for r in range(1,s)}; a=[F(c) for c in range(s)]
def wp(c): return math.prod([a[c]-a[d] for d in range(s) if d!=c])
rho=lambda c,cp: wp(cp)*(a[cp]-a[c])
def v2(x):
    x=F(x); n,d=abs(x.numerator),x.denominator; v=0
    while n%2==0: n//=2; v+=1
    while d%2==0: d//=2; v-=1
    return v
jt={t+1:J[t] for t in range(s-1)}
P={t:rho(jt[t],b)*rho(b,jt[t]) for t in jt}
delta=0
while not (all(1+2*delta>=v2(P[t]) for t in jt) and all(delta+v2(rho(b,jt[r]))-v2(rho(b,jt[t]))-v2(rho(jt[t],jt[r]))>=0 for t in jt for r in jt if t!=r)): delta+=1
def oddpart(n):
    n=abs(n)
    while n%2==0: n//=2
    return n
cand=[F(2)**(1+2*delta)*Q[t]/P[t] for t in jt]+[F(2)**delta*(Q[t]/Q[r])*rho(b,jt[r])/(rho(b,jt[t])*rho(jt[t],jt[r])) for t in jt for r in jt if t!=r]
L=1
for x in cand: L=math.lcm(L,oddpart(x.denominator))
for r in Q: L=math.lcm(L,oddpart(Q[r].numerator),oddpart(Q[r].denominator))
g={b:F(1)}; g.update({jt[r]:F(2)**(1+delta)*Q[r]/rho(b,jt[r]) for r in jt})
th0=F(2)**delta*L
n={(c,cp):th0*g[c]/(g[cp]*rho(c,cp)) for c in range(s) for cp in range(s) if c!=cp}
ok_int=all((n[(c,cp)].denominator==1) if c!=b else (n[(c,cp)].denominator==2 and n[(c,cp)].numerator%2) for (c,cp) in n)
print("delta",delta,"L",L,"n integral / brick row half-odd:",ok_int)
u=w*F(999,1000)/max(abs(n[(j,b)]) for j in J)
def cen(x,p): x%=p; return x-p if x>p//2 else x
def wsN(steps,arcs,p):
    o=sorted(range(len(steps)),key=lambda t:-steps[t]); n1,l1=steps[o[0]],arcs[o[0]]
    if not(1<=n1<=l1<=p): return None
    N=1+-(-(p-l1)//n1)
    for t in o[1:]:
        if steps[t]<1 or N*steps[t]>arcs[t]: return None
        N=N-1+-(-p//steps[t])
    return N
def minf1(e,lo,hi,p):
    if e==-1: lo,hi,e=-hi,-lo,1
    ln=hi-lo+1
    if ln>=p: return 0
    A_=lo%p
    if e==1: return 0 if (1-A_)%p<ln else (p-1 if A_==0 else A_-1)
    if (-A_)%p<ln: return 0
    B_=A_+ln-1; return max(0,min(min(A_,p-A_),min(B_,p-B_))-1)
def check(p):
    T=int(u*p); T-= (T%2==0)
    fr=lambda q: q.numerator%p*pow(q.denominator,-1,p)%p
    theta=fr(th0)*T%p; G={c:fr(g[c]) for c in g}
    K={(c,cp):theta*G[c]*pow(G[cp]*fr(rho(c,cp))%p,-1,p)%p for (c,cp) in n}
    assert all(K[k]==fr(n[k]*T) for k in K)
    B=int(w*p); h=(p+1)//2
    ctr={(c,cp):(h if c==b else 0) for (c,cp) in n}
    if any(abs(cen(-K[k]-ctr[k],p))>B for k in K): return "fail (i)"
    Mb=wsN([abs(cen(K[(j,b)],p)) for j in J],[2*B+1]*(s-1),p)
    if Mb is None: return "fail WS brick"
    Ms={}
    for i in J:
        N=wsN([abs(cen(2*K[(c,i)],p)) for c in range(s) if c!=i],[2*B+1]*(s-1),p)
        if N is None: return "fail WS col %d"%i
        Ms[i]=2*N-1
    A=(s-2)*B+B; M=max(Ms.values())
    own={b:(-(Mb-1),0)}; own.update({i:(-(A+Ms[i]-1),-A) for i in J})
    W={}
    for cp in range(s):
        W[(cp,cp)]=own[cp]
        for c in range(s):
            if c!=cp: W[(c,cp)]=(ctr[(c,cp)]-B,ctr[(c,cp)]+B)
    best=None
    for e in itertools.product((-1,0,1),repeat=s):
        if not any(e) or next(x for x in e if x)<0: continue
        tot=0
        for c in range(s):
            lo=hi=0
            for cp in range(s):
                if e[cp]:
                    x,y=W[(c,cp)]
                    if e[cp]<0: x,y=-y,-x
                    lo+=x; hi+=y
            tot+=minf1(e[c],lo,hi,p)**2
        if best is None or tot<best[0]: best=(tot,e)
    Nok=(A+M-1+(s-2)*B+B<=p-1) and (2*B+2*Mb<=p-3)
    if not Nok: return "fail (N): Lemma W not applicable (M=%d vs p)"%M
    tb=(p-Mb)**2*4; tcb=4*(p-A-M-B)**2+(p-1-2*B-2*Mb)**2; t2=8*(p-A-M-(s-2)*B-B)**2
    lbw=math.sqrt(min(tb,tcb,t2))/(2*p)
    return "T=%d Mb=%d M=%s exact window LB^2*p^2 == (p-Mb)^2: %s, step=%s, LemmaW binding brick axis: %s"%(T,Mb,Ms,best[0]==(p-Mb)**2,best[1],min(tb,tcb,t2)==tb)
for q in [int(float(x)) for x in sys.argv[5:]]:
    p=sympy.nextprime(q); print(p, check(p))
