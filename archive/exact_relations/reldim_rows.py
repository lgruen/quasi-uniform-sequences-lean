# Method A (example after cor:nodesign): dimension of the exact relations among the residue rows
# rho_{c,n}(V) = Res_{a_c}(V w^{-n-1} dz), n = K-J..K, on deg V < sK, over F_p.
# Lemma rigid: every scramble with the skeleton relation at n = K-J..K has these rows up to scalars,
# and scaling rows does not change the relation dimension. Conclusion of cor:nodesign: dimension 1.
import itertools, random, sys
def inv(a,p): return pow(a%p,p-2,p)
def series_inv(f,N,p):
    g=[0]*N; g[0]=inv(f[0],p)
    for k in range(1,N):
        s=sum(f[i]*g[k-i] for i in range(1,min(k,len(f)-1)+1))%p
        g[k]=(-s*g[0])%p
    return g
def mul(f,g,N,p):
    h=[0]*N
    for i,a in enumerate(f[:N]):
        if a:
            for j,b in enumerate(g[:N-i]): h[i+j]=(h[i+j]+a*b)%p
    return h
def rho_row(places,c,n,ncols,p):
    a=places[c]; N=n+1
    # w_c(t+a) = prod_{b!=c} (t + a - a_b)
    wc=[1]
    for b,ab in enumerate(places):
        if b==c: continue
        wc=mul(wc,[(a-ab)%p,1],N,p)+[0]*0
        wc=(wc+[0]*N)[:N]
    iw=series_inv(wc,N,p)
    pw=[1]+[0]*(N-1)
    for _ in range(n+1): pw=mul(pw,iw,N,p)
    row=[]
    # (t+a)^i expansion
    for i in range(ncols):
        binom=[0]*N; 
        from math import comb
        for k in range(min(i,N-1)+1): binom[k]=comb(i,k)*pow(a,i-k,p)%p
        row.append(mul(binom,pw,N,p)[n])
    return row
def rank(M,p):
    M=[r[:] for r in M]; r=0; cols=len(M[0]) if M else 0
    for col in range(cols):
        piv=next((i for i in range(r,len(M)) if M[i][col]%p),None)
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]; iv=inv(M[r][col],p)
        M[r]=[x*iv%p for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][col]: f=M[i][col]; M[i]=[(x-f*y)%p for x,y in zip(M[i],M[r])]
        r+=1
    return r
def reldim(places,J,K,p):
    s=len(places); rows=[rho_row(places,c,n,s*K,p) for c in range(s) for n in range(K-J,K+1)]
    return len(rows)-rank(rows,p)
p,s,J,K=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4])
print("Faure places", list(range(s)), "dim", reldim(list(range(s)),J,K,p))
random.seed(1); found=0
for trial in range(int(sys.argv[5])):
    pl=random.sample(range(p),s); d=reldim(pl,J,K,p)
    if d>1:
        print("places",pl,"dim",d); found+=1
        if found>=3: break
print("trials done, found",found)
