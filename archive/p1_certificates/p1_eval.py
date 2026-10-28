# evaluate the audit's G(u) (p1.py, exec'd) EXACTLY at the certificates u* of the authors' evaluator for s = 3..7
import sys, math
from fractions import Fraction as F
import os; os.chdir(os.path.dirname(os.path.abspath(__file__))); src=open("p1.py").read(); exec(src.split('for s in (3,4,5):')[0])
cert={3:F(2934559,10**6),4:F(3495097,10**6),5:F(197527,62500),6:F(2270329,500000),7:F(1280189,250000)}
for s,u in cert.items():
    m,g,gam=setup(s); umin=max(1/(2*gam[t]) for t in range(1,s)); G,Ks=Gfun(s,u,m,g,gam)
    print(f's={s} u*={u} > umin {u>umin}  G(u*)<1: {G<1} (1-G = {float(1-G):.3e})  P_1 = {float(Ks*u**s):.6g}  C\'_s = K u* G = {float(Ks)**(1/s)*float(u)*float(G):.3f}')
