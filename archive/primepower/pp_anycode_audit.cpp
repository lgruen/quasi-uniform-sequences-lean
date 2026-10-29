// s=3 (or s=2): beta over EVERY digit code enc (bijection F_q -> {0..q-1}, enc(0)=0) and all weights.
// Field F_q = F_p[x]/(f) for one fixed irreducible f (all fields of order q are isomorphic; all codes are enumerated).
// usage: pp_anycode_audit p r s f_0 f_1 ... f_r  (coefficients of f low -> high, f_r = 1). Written by the audit of the
// Lean stage. Build (from the archive root): g++ -O2 -std=c++17 -o bin/pp_anycode_audit primepower/pp_anycode_audit.cpp
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
using namespace std;
int p,r,q,s; vector<int> ADD,NEG,MUL;
int dg(int a,int i){ for(int t=0;t<i;t++) a/=p; return a%p; }
void build(const vector<int>& f){
  ADD.assign(q*q,0); NEG.assign(q,0); MUL.assign(q*q,0);
  for(int a=0;a<q;a++){ int na=0,pw=1; for(int i=0;i<r;i++){ na+=((p-dg(a,i))%p)*pw; pw*=p;} NEG[a]=na;
    for(int b=0;b<q;b++){ int c=0; pw=1; for(int i=0;i<r;i++){ c+=((dg(a,i)+dg(b,i))%p)*pw; pw*=p;} ADD[a*q+b]=c;
      vector<long long> pr(2*r,0); for(int i=0;i<r;i++) for(int j=0;j<r;j++) pr[i+j]+=(long long)dg(a,i)*dg(b,j);
      for(int d=2*r-2; d>=r; d--){ long long cc=pr[d]%p; if(cc) for(int i=0;i<=r;i++) pr[d-r+i]-=cc*f[i]; }
      int m=0; pw=1; for(int i=0;i<r;i++){ m+=(int)(((pr[i]%p)+p)%p)*pw; pw*=p;} MUL[a*q+b]=m; }}
}
int main(int argc,char**argv){
  p=atoi(argv[1]); r=atoi(argv[2]); s=atoi(argv[3]); q=1; for(int i=0;i<r;i++) q*=p;
  vector<int> f(r+1); for(int i=0;i<=r;i++) f[i]=atoi(argv[4+i]); build(f);
  vector<int> perm(q-1); for(int i=0;i<q-1;i++) perm[i]=i+1;
  long long ncodes=0; int overall=-1;
  do{ ncodes++;
    vector<int> enc(q), dec(q); enc[0]=0; for(int el=1; el<q; el++) enc[el]=perm[el-1]; for(int el=0;el<q;el++) dec[enc[el]]=el;
    vector<int> D; vector<char> inD(q,0);
    for(int y=0;y<q;y++){ int d=ADD[dec[(enc[y]+1)%q]*q+NEG[y]]; if(!inD[d]){inD[d]=1; D.push_back(d);} }
    vector<int> gap[3]; for(int t=0;t<3;t++){ gap[t].assign(q,0); int e=t-1; for(int sg=0;sg<q;sg++){ int mn=1<<30; for(int R=0;R<q;R++){ int v=e*q+enc[ADD[R*q+sg]]-enc[R]; if(v<0)v=-v; mn=min(mn,v);} gap[t][sg]=max(0,mn-1);} }
    int bestcode=-1;
    vector<int> k(s-1,1);
    while(true){
      int best=q; int e[4]; int tot=1; for(int i=0;i<s;i++) tot*=3;
      for(int code=0; code<tot && best>0; code++){ int x=code; bool any=false; for(int i=0;i<s;i++){e[i]=x%3-1;x/=3;if(e[i])any=true;} if(!any) continue;
        int mov[4],m=0; for(int c=0;c<s-1;c++) if(e[c]) mov[m++]=c;
        int nd=1; for(int t=0;t<m;t++) nd*=D.size();
        for(int dd=0; dd<nd && best>0; dd++){ int y=dd, sg=0; for(int t=0;t<m;t++){ int c=mov[t]; int Dv=D[y%D.size()]; y/=D.size(); int tt=MUL[k[c]*q+Dv]; if(e[c]<0) tt=NEG[tt]; sg=ADD[sg*q+tt]; }
          best=min(best,gap[e[s-1]+1][sg]); } }
      bestcode=max(bestcode,best);
      int i=0; while(i<s-1 && ++k[i]==q){k[i]=1;i++;} if(i==s-1) break; }
    overall=max(overall,bestcode);
  } while(next_permutation(perm.begin(),perm.end()));
  printf("q=%d s=%d: %lld codes, best beta over all codes and weights = %d/%d\n",q,s,ncodes,overall,q);
}
