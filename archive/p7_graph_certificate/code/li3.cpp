// li3.cpp -- third program for thm:p7: level-invariant 3D laws on mu_3: exact certificate LB_K from the K-independent law (prop:LI).
// Symmetric scramble L_c = L_0 diag(zeta^{ck}), omega_j = theta^j w^{-j-1} Q(w)^{-1} dt.  Column triple at carry length l:
//   O^(l)  = sum_{n=1..l}   o_n,  o_n = -theta^n [w^n](H Q),            H = (1+tau+tau^2)/3, tau=(1+w)^{1/3}
//   X_d^(l)= sum_{n=0..l-1} x_n,  x_n = -theta^{n+1}/3 [w^n](Q/(tau-zeta^d)),  d=1,2 (coordinate c'+d of column c')
// LB_K = min over e in {-1,0,1}^3\0 (mod +-), lengths l_c' <= K (c' in supp e) of sqrt(sum_c T(e_c, Delta_c)^2),
//   Delta_c = e_c O(l_c) + sum_{c' != c} e_c' X_{(c-c') mod 3}(l_c').   (the certificate of lem:cert, j = 1, via prop:LI)
// modes:
//   eval p theta N  Q1 Q2 ... (Q_0=1; missing Q's = 0)      -> LB_K for K=1..N
//   dfs  p theta N tau budget seed [order]                   -> deepest K with LB_K >= tau for all K, law printed
//   scan p N tau budget seed                                 -> dfs for every theta, summary
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <vector>
#include <string>
#include <algorithm>
#include <random>
#include <chrono>
#include <array>
using namespace std;
typedef long long ll;
int p, z; vector<double> T1sq, T0sq; // T(1,D)^2 ; T(0,D)^2 ; T(-1,D)=T(1,-D)
static inline int md(ll x){ x%=p; if(x<0)x+=p; return (int)x; }
ll pw(ll a, ll e){ ll r=1; a=md(a); while(e){ if(e&1) r=r*a%p; a=a*a%p; e>>=1;} return r; }
ll inv(ll a){ return pw(a,p-2); }
double Tfun(int e,int D){ double best=9; for(int r=0;r<p;r++){ int q=(r+D)%p; double v=fabs(e+(double)(q-r)/p)-1.0/p; best=min(best,max(v,0.0)); } return best; }
ll binom_small(int n,int k){ if(k<0||k>n) return 0; ll r=1; for(int i=0;i<k;i++){ r=r*((n-i)%p)%p; r=r*inv(i+1)%p; } return r; }
int Nmax; vector<ll> H, g1, g2; ll theta;
void setup(int N){
  Nmax=N+2; int r=(p-1)/3; int d0=p-r, d1=p-1-r;
  vector<ll> tau(Nmax);
  for(int n=0;n<Nmax;n++){ ll v=1; int m=n, i=0; while(m){ int ni=m%p; int di=(i==0)?d0:d1; if(ni>di){v=0;break;} v=v*binom_small(di,ni)%p; m/=p; i++; } tau[n]=v; }
  vector<ll> tau2(Nmax,0); for(int i=0;i<Nmax;i++) for(int j=0;i+j<Nmax;j++) tau2[i+j]=(tau2[i+j]+tau[i]*tau[j])%p;
  // sanity: tau^3 = 1+w
  for(int n=0;n<Nmax;n++){ ll s=0; for(int i=0;i<=n;i++) s=(s+tau2[i]*tau[n-i])%p; ll want=(n<=1)?1:0; if(s!=want){ fprintf(stderr,"tau check failed n=%d\n",n); exit(1);} }
  H.assign(Nmax,0); ll i3=inv(3); for(int n=0;n<Nmax;n++) H[n]=((n==0)+tau[n]+tau2[n])%p*i3%p;
  auto ser_inv=[&](vector<ll> a){ vector<ll> o(Nmax,0); ll i0=inv(a[0]); o[0]=i0; for(int n=1;n<Nmax;n++){ ll acc=0; for(int k=1;k<=n;k++) acc=(acc+a[k]*o[n-k])%p; o[n]=md(-acc*i0); } return o; };
  vector<ll> a=tau; a[0]=md(a[0]-z); g1=ser_inv(a); a=tau; a[0]=md(a[0]-(ll)z*z); g2=ser_inv(a);
}
struct Tri{ int o,x1,x2; };
// value of a step given triples per column (nullptr = not in support)
double stepval(const int e[3], const Tri* t[3]){
  double tot=0;
  for(int c=0;c<3;c++){
    ll D=0;
    if(e[c]) D+= e[c]*t[c]->o;
    for(int c2=0;c2<3;c2++){ if(c2==c||!e[c2]) continue; int d=((c-c2)%3+3)%3; D+= e[c2]*(d==1? t[c2]->x1 : t[c2]->x2); }
    int Dm=md(D);
    tot += e[c]==0 ? T0sq[Dm] : (e[c]>0 ? T1sq[Dm] : T1sq[md(-D)]);
  }
  return tot;
}
vector<array<int,3>> steps;
// min over combos that use triple 'nt' at least once, others from 'S' (plus nt)
double newmin(const vector<Tri>& S, const Tri& nt, double stopbelow){
  double best=9;
  vector<const Tri*> all; for(auto&t:S) all.push_back(&t); all.push_back(&nt);
  int n=all.size();
  for(auto&es:steps){
    int e[3]={es[0],es[1],es[2]};
    int sup[3], ns=0; for(int c=0;c<3;c++) if(e[c]) sup[ns++]=c;
    const Tri* t[3]={nullptr,nullptr,nullptr};
    if(ns==1){ t[sup[0]]=&nt; best=min(best,stepval(e,t)); }
    else if(ns==2){
      for(int i=0;i<n;i++){ t[sup[0]]=&nt; t[sup[1]]=all[i]; best=min(best,stepval(e,t)); t[sup[0]]=all[i]; t[sup[1]]=&nt; best=min(best,stepval(e,t)); if(best<stopbelow) return best; }
    } else {
      for(int i=0;i<n;i++) for(int j=0;j<n;j++){
        t[0]=&nt; t[1]=all[i]; t[2]=all[j]; best=min(best,stepval(e,t));
        t[0]=all[i]; t[1]=&nt; t[2]=all[j]; best=min(best,stepval(e,t));
        t[0]=all[i]; t[1]=all[j]; t[2]=&nt; best=min(best,stepval(e,t));
        if(best<stopbelow) return best; }
    }
  }
  return best;
}
// state
vector<ll> Q; vector<int> Os, X1s, X2s; // partial sums by length (index l)
ll o_coef(int l){ ll s=0; for(int k=0;k<=l;k++) s=(s+H[l-k]*Q[k])%p; return md(-pw(theta,l)*s); }
ll x_coef(int n,const vector<ll>&g){ ll s=0; for(int k=0;k<=n;k++) s=(s+g[n-k]*Q[k])%p; return md(-pw(theta,n+1)*inv(3)%p*s); }
bool contains(const vector<Tri>&S,const Tri&t){ for(auto&u:S) if(u.o==t.o&&u.x1==t.x1&&u.x2==t.x2) return true; return false; }
void init_steps(){ steps.clear(); for(int a=-1;a<=1;a++)for(int b=-1;b<=1;b++)for(int c=-1;c<=1;c++){ if(!a&&!b&&!c) continue; int f=a?a:(b?b:c); if(f<0) continue; steps.push_back({a,b,c}); } }
int main(int argc,char**argv){
  string mode=argv[1]; p=atoi(argv[2]);
  for(int g=2;g<p;g++){ ll x=pw(g,(p-1)/3); if(x!=1){z=x;break;} }
  T1sq.resize(p); T0sq.resize(p); for(int D=0;D<p;D++){ double a=Tfun(1,D), b=Tfun(0,D); T1sq[D]=a*a; T0sq[D]=b*b; }
  init_steps();
  if(mode=="eval"){
    theta=atoi(argv[3]); int N=atoi(argv[4]); setup(N+2);
    Q.assign(N+3,0); Q[0]=1; for(int i=5;i<argc && i-4<=N+1;i++) Q[i-4]=md(atoll(argv[i]));
    vector<Tri> S; double lbsq=9; int O=0, X1=0, X2=0;
    for(int K=1;K<=N;K++){
      O=md(O+o_coef(K)); X1=md(X1+x_coef(K-1,g1)); X2=md(X2+x_coef(K-1,g2));
      Tri nt{O,X1,X2};
      if(!contains(S,nt)){ lbsq=min(lbsq,newmin(S,nt,-1)); S.push_back(nt); }
      if(K<=12 || K%20==0 || K==N) printf("K=%d LB_K=%.4f  triple(O,X1,X2)=(%d,%d,%d) distinct=%zu\n",K,sqrt(lbsq),O>p/2?O-p:O,X1>p/2?X1-p:X1,X2>p/2?X2-p:X2,S.size());
    }
    return 0;
  }
  if(mode=="dfs"||mode=="scan"){
    int ai=3; vector<ll> thetas;
    if(mode=="dfs"){ thetas.push_back(atoi(argv[ai++])); } else for(int t=1;t<p;t++) thetas.push_back(t);
    int N=atoi(argv[ai++]); double tau=atof(argv[ai++]); ll budget=atoll(argv[ai++]); int seed=atoi(argv[ai++]);
    setup(N+2); double tsq=tau*tau-1e-12;
    int globalbest=0; ll bestth=-1; vector<ll> bestQ;
    for(ll th: thetas){
      theta=th; mt19937 rng(seed);
      // DFS iterative
      Q.assign(N+3,0); Q[0]=1;
      vector<vector<int>> cand(N+2); vector<int> ci(N+2,0);
      vector<vector<Tri>> Sst(N+2); vector<array<int,3>> ps(N+2);
      ps[0]={0, (int)x_coef(0,g1), (int)x_coef(0,g2)}; // X^(1) partial = x_0 (O^(0)=0)
      // ps[l] = (O^(l), X1^(l+1), X2^(l+1)) after choosing Q_l ; ps[0] uses Q_0=1
      // level K check uses triple (O^(K), X^(K)) = (ps[K].o, ps[K-1].x)
      ll nodes=0; int depth=0, best=0; vector<ll> bQ;
      auto expand=[&](int l){ // candidates for Q_l, l>=1, given Q_0..Q_{l-1}; triple at length l = (O^(l), X^(l))
        cand[l].clear(); ci[l]=0;
        vector<int> order(p); for(int i=0;i<p;i++) order[i]=i; shuffle(order.begin(),order.end(),rng);
        for(int q: order){ Q[l]=q; int O=md(ps[l-1][0]+o_coef(l)); Tri nt{O, ps[l-1][1], ps[l-1][2]};
          bool ok;
          if(contains(Sst[l-1],nt)) ok=true; else ok = newmin(Sst[l-1],nt,tsq) >= tsq;
          if(ok) cand[l].push_back(q); }
        Q[l]=0;
      };
      Sst[0].clear(); int l=1; expand(1);
      while(l>=1 && nodes<budget){
        if(ci[l]>=(int)cand[l].size()){ l--; continue; }
        int q=cand[l][ci[l]++]; Q[l]=q; nodes++;
        int O=md(ps[l-1][0]+o_coef(l)); Tri nt{O, ps[l-1][1], ps[l-1][2]};
        Sst[l]=Sst[l-1]; if(!contains(Sst[l],nt)) Sst[l].push_back(nt);
        ps[l]={O, md(ps[l-1][1]+x_coef(l,g1)), md(ps[l-1][2]+x_coef(l,g2))};
        if(l>best){ best=l; bQ.assign(Q.begin(),Q.begin()+l+1); }
        if(l==N) break;
        l++; for(int k=l;k<=N;k++) Q[k]=0; expand(l);
      }
      if(mode=="dfs" || best>globalbest){ }
      if(best>globalbest){ globalbest=best; bestth=th; bestQ=bQ; }
      if(mode=="scan" && best==N && getenv("FIRST")) { printf("  theta=%lld: K=%d N\n",th,best); break; }
      if(mode=="dfs") printf("p=%d zeta=%d theta=%lld tau=%.3f: deepest K=%d (%s, nodes=%lld)\n",p,z,th,tau,best, best==N?"reached N":(nodes>=budget?"budget":"EXHAUSTED: tree finite"),nodes);
      else if(best>=N/2 || th==thetas.back()) {}
      if(mode=="scan") printf("  theta=%lld: K=%d %s\n",th,best,best==N?"N":(nodes>=budget?"budget":"exh"));
    }
    printf("best: p=%d theta=%lld K=%d Q=",p,bestth,globalbest); for(ll q:bestQ) printf("%lld ",q); printf("\n");
  }
}
