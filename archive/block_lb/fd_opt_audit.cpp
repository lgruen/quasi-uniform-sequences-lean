// Does some integer diagonal delta (same at every depth: M^(j)[c][c] = -delta_c) satisfy the hypothesis of Lemma lem:signclass
// with the constant A?
// Axis steps force 0<=delta_c<=A, so the search space [0,A]^s is the whole space. Backtracking over coordinates;
// after fixing delta_0..delta_k, every step whose moving set has max index k is checked.
// usage (from the archive root): bin/fd_opt_audit block_lb/ustar<s>.txt A (the diagonal of the file is ignored).
// Build: g++ -O2 -std=c++17 -o bin/fd_opt_audit block_lb/fd_opt_audit.cpp
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <set>
#include <algorithm>
using namespace std;
int s, A; long long F[12][12][12], M[12][12][12];
struct Step{int mask; int r[12];};
vector<vector<Step>> byMax;
int d[12]; long long nodes=0;
bool ok(const Step& st){
  int nb=0;
  for(int i=0;i<s;i++) if(st.mask>>i&1){ if(d[i]>=st.r[i]){ nb++; if(d[i]<=st.r[i]+A) return true; } }
  return nb>=2;
}
bool rec(int k){
  if(k==s) return true;
  for(int v=0; v<=A; v++){ d[k]=v; nodes++; bool good=true;
    for(auto&st:byMax[k]) if(!ok(st)){good=false;break;}
    if(good && rec(k+1)) return true; }
  return false;
}
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); fscanf(f,"%d",&s); A=atoi(argv[2]);
  for(int n=0;n<s-1;n++)for(int i=0;i<s;i++)for(int c=0;c<s;c++)fscanf(f,"%lld",&F[n][i][c]);
  for(int c=0;c<s;c++) for(int n=0;n<s-1;n++) F[n][c][c]=0;  // diagonal handled separately (sigma_i = -e_i d_i + R_i)
  for(int i=0;i<s;i++)for(int c=0;c<s;c++){long long a=0;for(int j=0;j<s-1;j++){a+=F[j][i][c];M[j][i][c]=a;}}
  byMax.assign(s,{});
  set<vector<int>> seen;
  int e[12],j[12]; long long tot3=1; for(int i=0;i<s;i++) tot3*=3;
  for(long long code=1;code<tot3;code++){
    long long x=code; int first=-1; for(int i=0;i<s;i++){e[i]=x%3-1;x/=3;if(e[i]&&first<0)first=i;}
    if(first<0||e[first]!=1) continue;
    int mov[12],k=0,mask=0,mx=0; for(int i=0;i<s;i++) if(e[i]){mov[k++]=i;mask|=1<<i;mx=i;}
    long long nj=1; for(int t=0;t<k;t++) nj*=(s-1);
    for(long long jj=0;jj<nj;jj++){ long long y=jj; for(int t=0;t<k;t++){j[mov[t]]=y%(s-1);y/=(s-1);}
      Step st; st.mask=mask; vector<int> key={mask};
      for(int i=0;i<s;i++){ st.r[i]=0; if(!(mask>>i&1)) continue;
        long long R=0; for(int t=0;t<k;t++){int c=mov[t]; if(c!=i) R+=e[c]*M[j[c]][i][c];}
        // sigma_i = -e_i d_i + R_i ; backward iff e_i sigma_i <= 0 iff e_i R_i <= d_i ; |sigma_i| = d_i - e_i R_i
        st.r[i]=(int)(e[i]*R); key.push_back(st.r[i]); }
      if(seen.insert(key).second) byMax[mx].push_back(st);
    }}
  // put 2-moving steps first within each group (cheap pruning)
  for(auto&g:byMax) stable_sort(g.begin(),g.end(),[](const Step&a,const Step&b){return __builtin_popcount(a.mask)<__builtin_popcount(b.mask);});
  bool r=rec(0);
  printf("s=%d A=%d : %s (nodes %lld)", s, A, r?"FOUND":"none in [0,A]^s", nodes);
  if(r){printf(" delta="); for(int i=0;i<s;i++) printf("%d ",d[i]);} printf("\n");
}
