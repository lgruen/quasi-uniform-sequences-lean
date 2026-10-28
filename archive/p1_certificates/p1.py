"""p1.py -- audit's own evaluation of G(u) (Lemma B of the earlier version of the paper) and P_1 by bisection;
sanity: Gamma_A/p <= G(u(p)) at primes, and G, uG non-increasing on a grid."""
import sys, math
from fractions import Fraction as F
from sympy import primerange
sys.argv=[sys.argv[0]]+sys.argv[1:]
exec(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)),'mrA.py')).read().split('if __name__')[0])
def Gfun(s,u,m,g,gam):
    Ks=2*F(m[0,s-1],g)*math.prod(gam[1:])
    p=Ks*u**s
    half=F(1,2)
    def nup(t,j): return F(m[t,j],g)*math.prod(gam[i]*u+half for i in range(t+1,j+1))
    def num(t,j): return F(m[t,j],g)*math.prod(gam[i]*u-half for i in range(t+1,j+1))
    def nplus(t,j): return sum(1/num(r,j) for r in range(0,t+1))
    r0=2*sum(nup(0,j) for j in range(1,s))/p+1/p
    rows=[r0]
    for c in range(1,s):
        w=sum(max(nup(c,j)/p, nplus(c-1,j)*nup(c,j)/2) for j in range(c+1,s))
        rows.append(2*w+nplus(c-1,c))
    return max(rows),Ks
for s in (3,4,5):
    m,g,gam=setup(s); umin=max(1/(2*gam[t]) for t in range(1,s))
    lo=F(umin)+F(1,10**6); hi=2*F(umin)+1
    while Gfun(s,hi,m,g,gam)[0]>=1: hi*=2
    for it in range(40):
        mid=(lo+hi)/2
        if Gfun(s,mid,m,g,gam)[0]<1: hi=mid
        else: lo=mid
    G,Ks=Gfun(s,hi,m,g,gam)
    print(f's={s} K^s={Ks} u*~{float(hi):.6f} P_1~{float(Ks*hi**s):.2f} G(u*)={float(G):.6f}')
    # sanity at primes
    viol=0; mono=0
    for p in primerange(int(float(Ks*hi**s))+1, 30000 if s<5 else 60000):
        u=(F(p)/Ks)**F(1) ; uu=(p/float(Ks))**(1/s)
        Gp=Gfun(s,F(uu),m,g,gam)[0]  # float u is fine for the sanity check
        Gam,h=gamma_A(s,p,m,g,gam)
        if Gam/p>float(Gp)+1e-9: viol+=1
    us=[F(umin)+F(k,20) for k in range(1,400)]
    vals=[Gfun(s,x,m,g,gam)[0] for x in us]
    mono=sum(1 for a,b in zip(vals,vals[1:]) if b>a)+sum(1 for x,y,a,b in zip(us,us[1:],vals,vals[1:]) if y*b>x*a)
    print(f'   Gamma/p<=G(u(p)) violations: {viol};  monotonicity violations on grid: {mono}')
