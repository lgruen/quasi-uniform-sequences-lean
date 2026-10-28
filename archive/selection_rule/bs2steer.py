"""convert a brick-star cfg of the research build programs (bs_steer format) to the steer_rule/sp cfg format (lambda as in bs_steer2)."""
import sys
L=[l.split() for l in open(sys.argv[1]) if l.strip()]
p,a0,a1,a2,th=map(int,L[0]); a=[a0,a1,a2]
k=[[0]*3 for _ in range(3)]; v=list(map(int,L[1][1:])); k[1][0],k[2][0],k[0][1],k[2][1],k[0][2],k[1][2]=v
W=[[None]*3 for _ in range(3)]
for t in L[2:5]:
    cp=int(t[1]); o1,o2=(cp+1)%3,(cp+2)%3; x,y=min(o1,o2),max(o1,o2); n=list(map(int,t[2:8]))
    W[cp][cp]=(n[0],n[1]); W[x][cp]=(n[2],n[3]); W[y][cp]=(n[4],n[5])
inv=lambda z: pow(z%p,p-2,p)
wp=lambda c: (lambda r:[r:=r*(a[c]-a[e])%p for e in range(3) if e!=c][-1])(1)
lam=[1]+[k[c][0]*wp(c)*(a[0]-a[c])*inv(th)%p for c in (1,2)]
o=[f"s 3 p {p} theta {th} brick -1 mode bs","places "+" ".join(map(str,a)),"rho "+" ".join(map(str,lam))]
for c in range(3): o.append("kappa_row "+" ".join(str(k[c][j]) for j in range(3)))
for cp in range(3): o.append(f"win {cp} "+" ".join(f"{W[c][cp][0]} {W[c][cp][1]}" for c in range(3)))
open(sys.argv[2],'w').write("\n".join(o)+"\n")
