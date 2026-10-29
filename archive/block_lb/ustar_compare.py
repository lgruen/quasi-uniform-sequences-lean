"""ustar_compare.py -- data check of the designs U*_4, ..., U*_7 (Appendix app:verification): the files
block_lb/ustar<s>.txt agree entry by entry with U*_s rebuilt by block_lb/ustar_independent.py, an independent
implementation of the definition of U*_s in the nets paper [Gru26geo] (def:Ustar there), and with the designs of
block_lb/ustar_finite.json (F_{s-1} = 0 there). Prints a*_s and the largest off-diagonal entry max |M^(j)[c][d]|.
    python3 block_lb/ustar_compare.py [DIR]        (from the archive root; DIR defaults to block_lb)
Exit status 1 if an entry differs.
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ustar_independent import run
D_DIR = sys.argv[1] if len(sys.argv) > 1 else 'block_lb'
def load(path):
    t=open(path).read().split(); s=int(t[0]); vals=list(map(int,t[1:]))
    F=[[[vals[(n*s+i)*s+j] for j in range(s)] for i in range(s)] for n in range(s-1)]
    return s,F
J = json.load(open(os.path.join(D_DIR, 'ustar_finite.json')))
nbad = 0
for s in range(4,8):
    places,E=run(s)
    n=s-2
    M=[[[0]*s for _ in range(s)] for j in range(n+1)]
    for di,d in enumerate(places):
        rows,Es=E[d]
        for j in range(n+1):
            for ri,c in enumerate(rows):
                M[j][places.index(c)][di]=Es[j][ri]
    alpha=[sum(max(abs(M[j][c][d]) for j in range(n+1)) for d in range(s) if d!=c) for c in range(s)]
    Fm=[[[ (M[k][i][j]-(M[k-1][i][j] if k else 0)) if i!=j else (-alpha[i] if k==0 else 0) for j in range(s)] for i in range(s)] for k in range(n+1)]
    s2,Ff=load(os.path.join(D_DIR, f'ustar{s}.txt'))
    diff=sum(1 for k in range(n+1) for i in range(s) for j in range(s) if Fm[k][i][j]!=Ff[k][i][j])
    G = J[str(s)]['F']
    same_json = (G[:s-1] == Ff) and all(x == 0 for r in G[s-1] for x in r)
    nbad += diff + (not same_json)
    print('s',s,'a*',max(alpha),'maxentry',max(abs(M[j][c][d]) for j in range(n+1) for c in range(s) for d in range(s) if c!=d),'entries differing from file:',diff, 'file == ustar_finite.json:', same_json)
print('ALL AGREE' if nbad == 0 else 'DIFFERENCES FOUND')
sys.exit(1 if nbad else 0)
