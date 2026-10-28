"""mrA.py -- audit's own implementation of MR rule A (earlier version of the paper) from its written definition; Gamma per prime.
usage: python mrA.py s plo phi  -> first failure >= plo, count, min LB; also writes nothing."""
import sys, math
from fractions import Fraction as F
from math import factorial as fa, gcd
from sympy import primerange
def setup(s):
    m={}
    for c in range(s):
        for j in range(c+1,s):
            q=fa(s-1)//(fa(c)*fa(s-1-j)); assert (fa(s-1))%(fa(c)*fa(s-1-j))==0 and q%(j-c)==0
            m[c,j]=q//(j-c)
    g=0
    for v in m.values(): g=gcd(g,v)
    gam=[None]+[sum(F(m[t,j],m[t-1,j]) for j in range(t+1,s))+F(g,m[t-1,t]) for t in range(1,s)]
    return m,g,gam
def gamma_A(s,p,m,g,gam):
    mu=F(m[0,s-1],g)
    C=(2*float(mu)*p**(s-1)*math.prod(float(x) for x in gam[1:]))**(1/s)
    h=[None]+[max(1,round(float(gam[t])*p/C)) for t in range(1,s)]
    kap={}
    for c in range(s):
        for j in range(c+1,s):
            kap[c,j]=(-1)**(s-1-c)*(m[c,j]//g)*math.prod(h[c+1:j+1])
    W={}; M=[1]*s
    for j in range(1,s):
        nu=abs(kap[0,j]); W[0,j]=nu; N=1+(-(-(p-2*nu-1)//nu))
        for t in range(1,j):
            nu=abs(kap[t,j]); W[t,j]=max(nu,-(-(N*nu-1)//2)); N=N-1+(-(-p//nu))
        M[j]=N
    G=max(2*sum(W[c,j] for j in range(c+1,s))+M[c] for c in range(s))
    return G,h
if __name__=='__main__':
    s,lo,hi=map(int,sys.argv[1:4]); m,g,gam=setup(s)
    fails=[]; n=0; lbmin=2; worst=None
    for p in primerange(lo,hi+1):
        G,h=gamma_A(s,p,m,g,gam); n+=1
        if not G<p or any(x>=p for x in h[1:]): fails.append(p)
        else:
            lb=(p-G)/p
            if lb<lbmin: lbmin=lb; worst=p
    print(f's={s} primes in [{lo},{hi}]: {n}; failures {len(fails)} {fails[:8]}{"..." if len(fails)>8 else ""} last {fails[-1] if fails else None}; min LB {lbmin:.4f} at {worst}')
