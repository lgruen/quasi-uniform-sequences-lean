// beta_q(k) of prop:primepower, power-basis code of F_p[x]/(f); max over all monic irreducible f of degree r and all
// weights k in (F_q^*)^{s-1}.  usage: pp_best_audit p r s     (prints the best overall; with the
// environment variable V set also the best per f). Written by the audit of the Lean stage (independent field arithmetic).
// Build (from the archive root): g++ -O2 -std=c++17 -o bin/pp_best_audit primepower/pp_best_audit.cpp
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
using namespace std;
int p,r,q,s;
vector<int> ADD, NEG, MUL; vector<int> gapT[3]; vector<int> Ds;
int dg(int a,int i){ for(int t=0;t<i;t++) a/=p; return a%p; }
bool build(const vector<int>& f){ // f[0..r], f[r]=1
  ADD.assign(q*q,0); NEG.assign(q,0); MUL.assign(q*q,0);
  for(int a=0;a<q;a++){ int na=0,pw=1; for(int i=0;i<r;i++){ na+=((p-dg(a,i))%p)*pw; pw*=p;} NEG[a]=na;
    for(int b=0;b<q;b++){ int c=0; pw=1; for(int i=0;i<r;i++){ c+=((dg(a,i)+dg(b,i))%p)*pw; pw*=p;} ADD[a*q+b]=c;
      vector<long long> pr(2*r,0); for(int i=0;i<r;i++) for(int j=0;j<r;j++) pr[i+j]+= (long long)dg(a,i)*dg(b,j);
      for(int d=2*r-2; d>=r; d--){ long long cc=pr[d]%p; if(cc) for(int i=0;i<=r;i++) pr[d-r+i]-=cc*f[i]; }
      int m=0; pw=1; for(int i=0;i<r;i++){ m+=(int)(((pr[i]%p)+p)%p)*pw; pw*=p;} MUL[a*q+b]=m; }}
  for(int a=1;a<q;a++){ bool inv=false; for(int b=1;b<q;b++) if(MUL[a*q+b]==1){inv=true;break;} if(!inv) return false; }
  return true;
}
int beta(const vector<int>& k){
  int best=q; int e[8];
  int tot=1; for(int i=0;i<s;i++) tot*=3;
  for(int code=0;code<tot;code++){ int x=code; bool any=false; for(int i=0;i<s;i++){e[i]=x%3-1;x/=3; if(e[i])any=true;} if(!any) continue;
    int mov[8],m=0; for(int c=0;c<s-1;c++) if(e[c]) mov[m++]=c;
    int nd=1; for(int t=0;t<m;t++) nd*=r;
    for(int dd=0;dd<nd;dd++){ int y=dd, sg=0; for(int t=0;t<m;t++){ int c=mov[t]; int D=Ds[y%r]; y/=r; int tt=MUL[k[c]*q+D]; if(e[c]<0) tt=NEG[tt]; sg=ADD[sg*q+tt]; }
      int g=gapT[e[s-1]+1][sg]; if(g<best){best=g; if(best==0) return 0;} } }
  return best;
}
int main(int argc,char**argv){
  p=atoi(argv[1]); r=atoi(argv[2]); s=atoi(argv[3]); q=1; for(int i=0;i<r;i++) q*=p;
  Ds.clear(); { int c=0,pw=1; for(int t=0;t<r;t++){ c+=pw; pw*=p; Ds.push_back(c);} }
  int overall=-1; int nf=0;
  int nfc=1; for(int i=0;i<r;i++) nfc*=p;
  for(int fc=0; fc<nfc; fc++){ vector<int> f(r+1); int x=fc; for(int i=0;i<r;i++){f[i]=x%p;x/=p;} f[r]=1;
    if(f[0]==0) continue; if(!build(f)) continue; nf++;
    for(int t=0;t<3;t++){ gapT[t].assign(q,0); int e=t-1; for(int sg=0;sg<q;sg++){ int mn=1<<30; for(int R=0;R<q;R++){ int v=e*q+ADD[R*q+sg]-R; if(v<0)v=-v; mn=min(mn,v);} gapT[t][sg]=max(0,mn-1);} }
    int bestf=-1; vector<int> k(s-1,1), bk;
    while(true){ int b=beta(k); if(b>bestf){bestf=b; bk=k;}
      int i=0; while(i<s-1 && ++k[i]==q){k[i]=1;i++;} if(i==s-1) break; }
    if(getenv("V")){ printf("f="); for(int i=r;i>=0;i--) printf("%d ",f[i]); printf(": %d/%d k=",bestf,q); for(int v:bk) printf("%d ",v); printf("\n"); }
    overall=max(overall,bestf);
  }
  printf("p=%d r=%d s=%d q=%d: %d irreducible f, best beta = %d/%d\n",p,r,s,q,nf,overall,q);
}
