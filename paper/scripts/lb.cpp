// Independent auditor implementation of the one-digit relaxation LB(F) of lem:cert (j=1, prime p)
// for a design with off-diagonal entries from a ustar file and a chosen diagonal of F_0 (deeper diagonals 0).
// usage: lb file p d0 d1 ... (d = -F_0[c][c]); if no d given, keep the file's diagonal.
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <cmath>
#include <climits>
using namespace std;
int s; long long F[12][12][12], M[12][12][12];
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); fscanf(f,"%d",&s);
  for(int n=0;n<s-1;n++)for(int i=0;i<s;i++)for(int c=0;c<s;c++)fscanf(f,"%lld",&F[n][i][c]);
  long long p=atoll(argv[2]);
  if(argc>3){ for(int c=0;c<s;c++){F[0][c][c]=-atoll(argv[3+c]); for(int n=1;n<s-1;n++)F[n][c][c]=0;} }
  for(int i=0;i<s;i++)for(int c=0;c<s;c++){long long a=0;for(int j=0;j<s-1;j++){a+=F[j][i][c];M[j][i][c]=a;}}
  // gap table by brute force definition: g(e,sig)=max(0,min_R |e p + ((R+sig) mod p) - R| - 1)
  vector<long long> g[3]; for(int t=0;t<3;t++) g[t].assign(p,0);
  bool brute = p<=3000;
  for(int t=0;t<3;t++){int e=t-1; for(long long sg=0;sg<p;sg++){
     long long best;
     if(brute){best=LLONG_MAX; for(long long R=0;R<p;R++){long long v=e*p+((R+sg)%p)-R; if(v<0)v=-v; if(v<best)best=v;}}
     else { // closed form (validated against brute for p<=3000 in separate run)
       if(e==0) best = min(sg,p-sg);
       else if(e==1) best = sg==0? p: sg;
       else best = sg==0? p: p-sg; }
     g[t][sg]= best-1>0? best-1:0; }}
  // enumerate e in {-1,0,1}^s up to sign (first nonzero = +1), carry depths per moving coord in [0,s-2]
  long long best=LLONG_MAX; long long cnt=0;
  int e[12], j[12];
  long long tot3=1; for(int i=0;i<s;i++) tot3*=3;
  for(long long code=1; code<tot3; code++){
    long long x=code; int first=-1; for(int i=0;i<s;i++){e[i]=x%3-1; x/=3; if(e[i]!=0&&first<0)first=i;}
    if(first<0 || e[first]!=1) continue;
    int mov[12],k=0; for(int i=0;i<s;i++) if(e[i]) mov[k++]=i;
    long long nj=1; for(int t=0;t<k;t++) nj*=(s-1);
    for(long long jj=0;jj<nj;jj++){
      long long y=jj; for(int t=0;t<k;t++){j[mov[t]]=y%(s-1); y/=(s-1);}
      long long sum=0;
      for(int i=0;i<s;i++){ long long sig=0; for(int t=0;t<k;t++){int c=mov[t]; sig+=e[c]*M[j[c]][i][c];}
        sig%=p; if(sig<0) sig+=p; long long gg=g[e[i]+1][sig]; sum+=gg*gg; if(sum>=best) break;}
      cnt++; if(sum<best){ best=sum; if(getenv("DBG")){printf("new best %lld e=",sum); for(int i=0;i<s;i++)printf("%d,",e[i]); printf(" j="); for(int i=0;i<s;i++)printf("%d,",e[i]?j[i]:-1); printf("\n");}} }
  }
  printf("s=%d p=%lld  p-p*LB = %.4f  (LB = %.6f) configs=%lld\n", s,p, p-sqrt((double)best), sqrt((double)best)/p, cnt);
}
