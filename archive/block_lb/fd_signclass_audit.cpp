// A(delta): least A such that every step (e, carry depths) has a backward moving coordinate with |sigma|<=A or two
// backward moving coordinates (integer sigma). Also S = max row sum of max_j |M^(j)| and integer threshold
// p0 = least p > S with (p-A-1)^2 <= 2(p-S-1)^2 (Lemma lem:signclass). usage (from the archive root):
// bin/fd_signclass_audit block_lb/ustar<s>.txt [d0..d_{s-1}]. Build: g++ -O2 -std=c++17 -o bin/fd_signclass_audit block_lb/fd_signclass_audit.cpp
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <algorithm>
using namespace std;
int s; long long F[12][12][12], M[12][12][12];
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); fscanf(f,"%d",&s);
  for(int n=0;n<s-1;n++)for(int i=0;i<s;i++)for(int c=0;c<s;c++)fscanf(f,"%lld",&F[n][i][c]);
  if(argc>2){ for(int c=0;c<s;c++){F[0][c][c]=-atoll(argv[2+c]); for(int n=1;n<s-1;n++)F[n][c][c]=0;} }
  for(int i=0;i<s;i++)for(int c=0;c<s;c++){long long a=0;for(int j=0;j<s-1;j++){a+=F[j][i][c];M[j][i][c]=a;}}
  long long A=0; bool inf=false; int e[12],j[12]; long long tot3=1; for(int i=0;i<s;i++) tot3*=3;
  long long worstcode=-1;
  for(long long code=1;code<tot3;code++){
    long long x=code; int first=-1; for(int i=0;i<s;i++){e[i]=x%3-1;x/=3; if(e[i]&&first<0)first=i;}
    if(first<0||e[first]!=1) continue;
    int mov[12],k=0; for(int i=0;i<s;i++) if(e[i]) mov[k++]=i;
    long long nj=1; for(int t=0;t<k;t++) nj*=(s-1);
    for(long long jj=0;jj<nj;jj++){ long long y=jj; for(int t=0;t<k;t++){j[mov[t]]=y%(s-1);y/=(s-1);}
      int nb=0; long long mn=LLONG_MAX;
      for(int t=0;t<k;t++){int i=mov[t]; long long sig=0; for(int u=0;u<k;u++){int c=mov[u]; sig+=e[c]*M[j[c]][i][c];}
        if(e[i]*sig<=0){nb++; mn=min(mn, llabs(sig));}}
      if(nb>=2) continue; if(nb==0){inf=true; continue;} if(mn>A){A=mn;}
    }}
  long long S=0; for(int i=0;i<s;i++){long long r=0; for(int c=0;c<s;c++){long long b=0; for(int jj=0;jj<s-1;jj++) b=max(b,llabs(M[jj][i][c])); r+=b;} S=max(S,r);}
  long long p0=S+1; while(!((p0-A-1)*(p0-A-1) <= 2*(p0-S-1)*(p0-S-1))) p0++;
  printf("s=%d A=%lld%s S=%lld integer threshold p>=%lld\n",s,A,inf?" (some step has NO backward coord => INF)":"",S,p0);
}
