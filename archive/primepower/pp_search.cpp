// pp_search.cpp -- the exact search of the Lean stage for prop:primepower (it found the rows of tab:primepower with the
// best f; computation unchanged). Build (from the archive root): g++ -O2 -std=c++17 -o bin/pp_search primepower/pp_search.cpp
// Usage: pp_search pb p r s [fidx] | pp_search lin p r s fidx | pp_search any p r s fidx
// Exact beta_q(k) of prop:primepower (one-digit, one-coordinate bound of lem:cert on the staggered
// coordinate), for arbitrary digit codes of F_q.  Elements are represented in the power basis of a monic
// irreducible f (rep = sum c_i p^i).  A digit code is a bijection enc: rep -> {0..q-1} with enc(0)=0.
// beta*q = min over steps of max(0, min_r |e* q + enc(r+sigma) - enc(r)| - 1), sigma = sum_i e_i w_i Delta_i,
// Delta_i in Dset = { enc^-1((enc y + 1) mod q) - y : y }.
// Modes:
//   pb   p r s            : every monic irreducible f of degree r, power-basis code; best beta*q over weights
//   lin  p r s fidx       : f = fidx-th irreducible; every ordered basis b (code = digits of coordinates in b)
//   any  p r s fidx       : every bijective code with enc(0)=0 (only tiny q)
// Weights: all (q-1)^(s-1) vectors up to permutation (w0<=w1<=...).  Early exit when value <= current best.
#include <vector>
#include <set>
#include <string>
#include <functional>
#include <numeric>
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <climits>
using namespace std;
int p, r, q, s;
vector<vector<int>> ADD, MUL;
vector<int> NEG;
vector<int> dec(int c){ vector<int> v(r); for(int i=0;i<r;i++){ v[i]=c%p; c/=p;} return v; }
int encv(const vector<int>&v){ int c=0, m=1; for(int i=0;i<r;i++){ c+=((v[i]%p+p)%p)*m; m*=p;} return c; }
bool irred(const vector<int>& f){ // brute: no monic factor of degree 1..r/2
  for(int d=1; d<=r/2; d++){ int nd=1; for(int i=0;i<d;i++) nd*=p;
    for(int c=0;c<nd;c++){ vector<int> g(d+1); int t=c; for(int i=0;i<d;i++){ g[i]=t%p; t/=p;} g[d]=1;
      vector<int> a=f; // a mod g
      for(int k=(int)a.size()-1;k>=d;k--){ int co=a[k]%p; if(!co) continue; for(int i=0;i<=d;i++) a[k-d+i]=((a[k-d+i]-co*g[i])%p+p)%p; }
      bool z=true; for(int i=0;i<d;i++) if(a[i]%p) z=false; if(z) return false; } }
  return true; }
void mkfield(const vector<int>& f){
  ADD.assign(q, vector<int>(q)); MUL.assign(q, vector<int>(q)); NEG.assign(q,0);
  for(int x=0;x<q;x++){ auto a=dec(x); vector<int> na(r); for(int i=0;i<r;i++) na[i]=(p-a[i])%p; NEG[x]=encv(na);
    for(int y=0;y<q;y++){ auto b=dec(y); vector<int> c(r); for(int i=0;i<r;i++) c[i]=(a[i]+b[i])%p; ADD[x][y]=encv(c);
      vector<long> pr(2*r-1,0); for(int i=0;i<r;i++) for(int j=0;j<r;j++) pr[i+j]=(pr[i+j]+a[i]*b[j])%p;
      for(int d=2*r-2; d>=r; d--){ long co=pr[d]%p; if(!co) continue; for(int i=0;i<=r;i++) pr[d-r+i]=((pr[d-r+i]-co*f[i])%p+p)%p; }
      vector<int> m(r); for(int i=0;i<r;i++) m[i]=pr[i]; MUL[x][y]=encv(m); } } }
// G[e+1][sigma]
vector<int> G[3]; vector<int> Dset;
void mkG(const vector<int>& enc, const vector<int>& decd){
  for(int e=-1;e<=1;e++){ G[e+1].assign(q,0);
    for(int sg=0; sg<q; sg++){ long best=LONG_MAX; for(int x=0;x<q;x++){ long v=labs((long)e*q + enc[ADD[x][sg]] - enc[x]); if(v<best) best=v; }
      G[e+1][sg]= (int)max(0L, best-1); } }
  set<int> D; for(int y=0;y<q;y++){ int z=decd[(enc[y]+1)%q]; D.insert(ADD[z][NEG[y]]); }
  Dset.assign(D.begin(), D.end()); }
// beta for weights w (size s-1), with cutoff: return as soon as value <= cut
int betaw(const vector<int>& w, int cut){
  int b = min(G[0][0], G[2][0]);
  // N = reachable sigma with nonzero e'
  vector<char> N(q,0), N2(q);
  for(size_t i=0;i<w.size();i++){
    vector<int> P; for(int d: Dset){ int t=MUL[w[i]][d]; P.push_back(t); P.push_back(NEG[t]); }
    fill(N2.begin(), N2.end(), 0);
    for(int x=0;x<q;x++) if(N[x]){ N2[x]=1; for(int t: P) N2[ADD[x][t]]=1; }
    for(int t: P) N2[t]=1;
    N.swap(N2);
  }
  for(int x=0;x<q;x++) if(N[x]){ int v=min(G[0][x], min(G[1][x], G[2][x])); if(v<b){ b=v; if(b<=cut) return b; } }
  return b; }
int bestOverWeights(vector<int>& arg){
  int best=0; arg.clear(); int n=s-1; vector<int> w(n,1);
  while(true){ int v=betaw(w,best); if(v>best){ best=v; arg=w; }
    int i=n-1; while(i>=0 && w[i]==q-1) i--; if(i<0) break; w[i]++; for(int j=i+1;j<n;j++) w[j]=w[i]; }
  return best; }
string fstr(const vector<int>& f){ string o; for(int i=r;i>=0;i--) if(f[i]){ if(!o.empty()) o+="+"; if(f[i]!=1||i==0) o+=to_string(f[i]); if(i>=1) o+="x"; if(i>=2) o+="^"+to_string(i);} return o; }
int main(int argc, char** argv){
  string mode=argv[1]; p=atoi(argv[2]); r=atoi(argv[3]); s=atoi(argv[4]); q=1; for(int i=0;i<r;i++) q*=p;
  vector<vector<int>> irr; for(int c=0;c<q;c++){ vector<int> f(r+1); int t=c; for(int i=0;i<r;i++){f[i]=t%p;t/=p;} f[r]=1; if(irred(f)) irr.push_back(f); }
  if(mode=="pb"){
    int top=-1;
    int only = argc>5 ? atoi(argv[5]) : -1; int idx=-1;
    for(auto& f: irr){ idx++; if(only>=0 && idx!=only) continue; mkfield(f); vector<int> enc(q), de(q); for(int x=0;x<q;x++){enc[x]=x; de[x]=x;} mkG(enc,de);
      vector<int> arg; int b=bestOverWeights(arg); top=max(top,b);
      printf("s=%d q=%d f=%s best=%d/%d k=", s, q, fstr(f).c_str(), b, q); for(int x: arg) printf("%d ", x); printf("\n"); }
    printf("MAX s=%d q=%d %d/%d\n", s,q,top,q); return 0; }
  int fidx = atoi(argv[5]); mkfield(irr[fidx]);
  if(mode=="lin"){ // ordered bases b_0..b_{r-1} (as reps); code of y = digits of coordinates of y in b
    long cnt=0, pos=0; int top=0; vector<int> bas(r); vector<int> topb;
    // enumerate ordered bases by DFS with span check
    function<void(int, vector<char>&)> rec = [&](int i, vector<char>& span){
      if(i==r){ cnt++; vector<int> enc(q), de(q);
        for(int c=0;c<q;c++){ auto x=dec(c); int y=0; for(int j=0;j<r;j++) for(int t=0;t<x[j];t++) y=ADD[y][bas[j]]; de[c]=y; enc[y]=c; }
        mkG(enc,de); vector<int> arg; int b=bestOverWeights(arg); if(b>0) pos++; if(b>top){top=b; topb=bas;} return; }
      for(int v=1; v<q; v++) if(!span[v]){ bas[i]=v; vector<char> ns(q,0); for(int x=0;x<q;x++) if(span[x]){ int y=x; for(int t=0;t<p;t++){ ns[y]=1; y=ADD[y][v]; } }
        rec(i+1, ns); } };
    vector<char> sp(q,0); sp[0]=1; rec(0, sp);
    printf("lin s=%d q=%d f=%s bases=%ld positive=%ld max=%d/%d basis=", s,q,fstr(irr[fidx]).c_str(),cnt,pos,top,q); for(int x: topb) printf("%d ",x); printf("\n");
    return 0; }
  if(mode=="any"){ vector<int> perm(q-1); iota(perm.begin(), perm.end(), 1); long cnt=0, pos=0; int top=0; vector<int> topc;
    do { vector<int> enc(q), de(q); enc[0]=0; de[0]=0; for(int i=0;i<q-1;i++){ de[i+1]=perm[i]; enc[perm[i]]=i+1; }
      mkG(enc,de); vector<int> arg; int b=bestOverWeights(arg); cnt++; if(b>0) pos++; if(b>top){top=b; topc=de;} } while(next_permutation(perm.begin(), perm.end()));
    printf("any s=%d q=%d codes=%ld positive=%ld max=%d/%d dec=", s,q,cnt,pos,top,q); for(int x: topc) printf("%d ",x); printf("\n"); return 0; }
}
