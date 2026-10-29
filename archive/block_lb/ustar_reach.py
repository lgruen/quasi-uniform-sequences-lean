# Reachability (def:block) of the U*_s off-diagonal entries at the places 0,1,1/2,...,1/(s-1), v=(1,1,2,...,s-1):
# for each column c and depth n, the interpolant of v_i F_n[i][c]/tau_ic at the s-1 nodes tau_ic must have exact degree n.
# Exact interpolation over Q; prints the primes occurring in the denominators of the coefficients and in the leading
# coefficients.
# usage (from the archive root): python3 block_lb/ustar_reach.py block_lb/ustar<s>.txt
import sys
from fractions import Fraction as Fr
def load(path):
    t=open(path).read().split(); s=int(t[0]); vals=list(map(int,t[1:]))
    return s,[[[vals[(n*s+i)*s+j] for j in range(s)] for i in range(s)] for n in range(s-1)]
def interp(xs, ys):
    n=len(xs); coef=[Fr(0)]*n
    for j in range(n):
        b=[Fr(1)]; den=Fr(1)
        for m in range(n):
            if m==j: continue
            b=[Fr(0)]+b
            for k in range(len(b)-1): b[k]-=xs[m]*b[k+1]
            den*=xs[j]-xs[m]
        for k in range(n): coef[k]+=ys[j]*b[k]/den
    return coef
def primes(x):
    x=abs(x); out=set(); d=2
    while d*d<=x:
        while x%d==0: out.add(d); x//=d
        d+=1
    if x>1: out.add(x)
    return out
s,F=load(sys.argv[1])
a=[Fr(0)]+[Fr(1,c) for c in range(1,s)]; v=[1]+list(range(1,s))
bad=0; P=set()
for c in range(s):
    for n in range(s-1):
        xs=[1/(a[i]-a[c]) for i in range(s) if i!=c]
        ys=[v[i]*F[n][i][c]*(a[i]-a[c]) for i in range(s) if i!=c]
        co=interp(xs,ys)
        if any(co[k]!=0 for k in range(n+1,s-1)) or co[n]==0: bad+=1
        for k in range(n+1):
            P|=primes(co[k].denominator)
        P|=primes(co[n].numerator)
print('s',s,'columns/depths with wrong degree:',bad,'primes in denominators or leading coefficients:',sorted(P))
