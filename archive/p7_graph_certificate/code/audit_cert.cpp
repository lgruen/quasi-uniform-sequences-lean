// audit_cert.cpp -- second program for thm:p7 (audit, own code): LB(w) of lem:cert (j = 1) over per-column triple sets.
// stdin: p, then for c=0..2: n_c followed by n_c triples (o x1 x2). X_d feeds coord c+d.
#include <cstdio>
#include <vector>
#include <cstdlib>
#include <algorithm>
#include <array>
using namespace std;
int p; int Tp[3][64]; // Tp[e+1][D]
int main(){
  if(scanf("%d",&p)!=1) return 1;
  for(int e=-1;e<=1;e++) for(int D=0;D<p;D++){ int best=1<<30;
    for(int r=0;r<p;r++){ int v=abs(e*p+((r+D)%p)-r)-1; if(v<0)v=0; best=min(best,v);} Tp[e+1][D]=best; }
  vector<vector<array<int,3>>> F(3);
  for(int c=0;c<3;c++){int n;scanf("%d",&n);F[c].resize(n);for(auto&t:F[c])scanf("%d %d %d",&t[0],&t[1],&t[2]);}
  long best=1L<<60; int be[3]={0,0,0}; array<int,3> bt[3];
  for(int e0=-1;e0<=1;e0++)for(int e1=-1;e1<=1;e1++)for(int e2=-1;e2<=1;e2++){
    int e[3]={e0,e1,e2}; if(!e0&&!e1&&!e2) continue;
    // iterate over triples for columns in support
    vector<int> sup; for(int c=0;c<3;c++) if(e[c]) sup.push_back(c);
    vector<size_t> idx(sup.size(),0);
    vector<size_t> lim; for(int c:sup) lim.push_back(F[c].size());
    bool any=true; for(auto L:lim) if(!L) any=false; if(!any) continue;
    while(true){
      int D[3]={0,0,0};
      for(size_t k=0;k<sup.size();k++){ int c1=sup[k]; auto&t=F[c1][idx[k]];
        D[c1]+=e[c1]*t[0]; D[(c1+1)%3]+=e[c1]*t[1]; D[(c1+2)%3]+=e[c1]*t[2]; }
      long S=0; for(int c=0;c<3;c++){ int d=((D[c]%p)+p)%p; int v=Tp[e[c]+1][d]; S+=(long)v*v; }
      if(S<best){best=S; for(int c=0;c<3;c++) be[c]=e[c]; for(size_t k=0;k<sup.size();k++) bt[sup[k]]=F[sup[k]][idx[k]]; for(int c=0;c<3;c++) if(!e[c]) bt[c]={-1,-1,-1};}
      size_t k=0; while(k<sup.size()){ if(++idx[k]<lim[k]) break; idx[k]=0; k++; } if(k==sup.size()) break;
    }
  }
  printf("minS %ld  LB %.6f  step (%d,%d,%d) triples",best,  __builtin_sqrt((double)best)/p, be[0],be[1],be[2]);
  for(int c=0;c<3;c++) printf(" [%d %d %d]",bt[c][0],bt[c][1],bt[c][2]); printf("\n");
}
