// mdist.cpp -- toroidal minimum-distance tools (general dimension s); used by practice/j_check.py.
//   mdist drops in.bin s Nmax out.txt   : running minimum delta^2(P_[N]) for every N = 2..Nmax (prefixes of the
//                                         sequence, in order); writes the drop events "N d2" (delta^2 of P_[N] for all
//                                         N' in [N, next event)), last line "END Nmax".
//   mdist nn in.bin s N out.bin         : toroidal nearest-neighbour distance of each of the first N points (float64).
// in.bin = row-major float64 points in [0,1)^s.  Exact (no approximation): uniform cell grid G^s, a query scans every
// cell that can contain a point closer than the current radius (incremental: radius = current running minimum).
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <vector>
#include <string>
#include <algorithm>
typedef long long ll;
static int S; static ll G; static std::vector<double> X;
static inline double tdist2(ll a, ll b){ double s=0; for(int c=0;c<S;c++){ double d=fabs(X[a*S+c]-X[b*S+c]); if(d>0.5) d=1-d; s+=d*d; } return s; }
static inline ll cellof(ll a, int c){ ll k=(ll)(X[a*S+c]*G); return k>=G? G-1: (k<0?0:k); }
struct Grid { std::vector<ll> head, nxt; void init(ll ncell, ll n){ head.assign(ncell,-1); nxt.assign(n,-1); }
  void add(ll a){ ll id=0; for(int c=0;c<S;c++) id=id*G+cellof(a,c); nxt[a]=head[id]; head[id]=a; } };
// scan all cells within k (per dim, wrapped; all G if 2k+1>=G) of point a's cell; returns min d2 to others (excluding a)
static double scan(Grid&g, ll a, ll k, double best){
  ll base[8]; ll lo[8], cnt[8]; for(int c=0;c<S;c++){ base[c]=cellof(a,c); if(2*k+1>=G){ lo[c]=0; cnt[c]=G; } else { lo[c]=base[c]-k; cnt[c]=2*k+1; } }
  ll idx[8]={0};
  while(true){ ll id=0; for(int c=0;c<S;c++){ ll v=((lo[c]+idx[c])%G+G)%G; id=id*G+v; }
    for(ll b=g.head[id]; b>=0; b=g.nxt[b]) if(b!=a){ double d=tdist2(a,b); if(d<best) best=d; }
    int c=S-1; while(c>=0){ if(++idx[c]<cnt[c]) break; idx[c]=0; c--; } if(c<0) break; }
  return best; }
int main(int argc,char**argv){
  if(argc<6){ fprintf(stderr,"usage: mdist drops|nn in.bin s N out\n"); return 1; }
  std::string mode=argv[1]; S=atoi(argv[3]); ll N=atoll(argv[4]);
  FILE*f=fopen(argv[2],"rb"); X.resize(N*S); if((ll)fread(X.data(),sizeof(double),N*S,f)!=N*S){ fprintf(stderr,"short read\n"); return 2; } fclose(f);
  G=(ll)floor(pow((double)N,1.0/S)+1e-9); if(G<1) G=1; ll nc=1; for(int c=0;c<S;c++) nc*=G;
  Grid g; g.init(nc,N);
  if(mode=="drops"){ FILE*o=fopen(argv[5],"w"); fprintf(o,"# N d2  (running min of toroidal squared distance over prefixes; s=%d)\n",S);
    double best=1e300; g.add(0);
    for(ll j=1;j<N;j++){ double r=sqrt(std::min(best,(double)S*0.25)); ll k=(ll)ceil(r*G)+1;
      double nb=scan(g,j,k,best); if(nb<best){ best=nb; fprintf(o,"%lld %.17g\n",j+1,best); } g.add(j); }
    fprintf(o,"END %lld\n",N); fclose(o); printf("drops: N=%lld final delta=%.6g c=%.6f\n",N,sqrt(best),sqrt(best)*pow((double)N,1.0/S)); }
  else if(mode=="nn"){ for(ll a=0;a<N;a++) g.add(a); std::vector<double> out(N);
    for(ll a=0;a<N;a++){ double best=1e300; ll k=1; while(true){ best=scan(g,a,k,best); if(best<=((double)k/G)*((double)k/G) || 2*k+1>=G) break; k++; } out[a]=sqrt(best); }
    FILE*o=fopen(argv[5],"wb"); fwrite(out.data(),sizeof(double),N,o); fclose(o);
    double mn=*std::min_element(out.begin(),out.end()); printf("nn: N=%lld min=%.6g c=%.6f\n",N,mn,mn*pow((double)N,1.0/S)); }
  return 0; }
