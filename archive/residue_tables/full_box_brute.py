import sys, itertools
p=int(sys.argv[1]); v=[int(x) for x in sys.argv[2].split(',')]; B=int(sys.argv[3]); s=len(v)
best=None; arg=None
for a in itertools.product(range(-B,B+1),repeat=s):
    if any(a) and sum(x*y for x,y in zip(a,v))%p==0:
        j=sum((abs(x)-1)**2 for x in a if abs(x)>1)
        if best is None or j<best: best=j; arg=a
print("full-box brute B=%d: jit2=%s at %s (exact if jit2<=B^2)"%(B,best,arg))
