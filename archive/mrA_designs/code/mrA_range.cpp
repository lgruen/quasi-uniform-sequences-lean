// lexrule.cpp -- the explicit rule MR(s,p) of the earlier version of the paper ("multinomial mixed radix" LEX design), no covering search.
// Frame a_c = c, theta = (s-1)!/g, gauge rho_c = (s-1-c)!/H_c (sp convention), H_c = h_1...h_c. Upper crosses
//   kappa_{c<-j} = (-1)^{s-1-c} m_{cj} h_{c+1}...h_j / g,  m_{cj} = (s-1)!/(c!(s-1-j)!(j-c)).
// Windows by Lemma WS in every column j (row 0 wraps with W = |kappa_{0j}|; rows t = 1..j-1 sweep in this order with
// 2W+1 >= N_{t-1} nu_t), own M_j = the WS number N (a certificate, PROOF), lower crosses full, own [-(X+M-1),-X].
// LB_lex = min_c (p - 2X_c - M_c)/p  (Lemma LEX).  Heights:
//   rule A ("formula"): h_t = max(1, round(gamma_t p / C)), C from row 0 balance (closed form);
//   rule B ("arith"):   heights minimising max_c (2X_c+M_c) over a grid h_t in [hA_t/3, 3 hA_t]  (arithmetic only).
// usage: lexrule s p A|B out.cfg      (prints LB_lex; write cfg for sp_check)
#include "../../common/hd_common.h"
#include <climits>
#include <functional>
#include <algorithm>
#include <cmath>
static int S;
static ll fact(int n){ ll r=1; for(int i=2;i<=n;i++) r*=i; return r; }
static ll gcdl(ll a,ll b){ while(b){ ll t=a%b; a=b; b=t; } return llabs(a); }
static std::vector<std::vector<ll>> m; static ll g;
struct R { std::vector<ll> h; std::vector<std::vector<ll>> kap,W; std::vector<ll> M; ll cost=LLONG_MAX; };
static bool design(R& D){ // fills kappa, WS windows, M; returns false if some kappa >= p/2 or a window/own overflows
  D.kap.assign(S,std::vector<ll>(S,0)); D.W.assign(S,std::vector<ll>(S,0)); D.M.assign(S,1);
  for(int c=0;c<S;c++) for(int j=c+1;j<S;j++){ __int128 k=m[c][j]/g; for(int i=c+1;i<=j;i++){ k*=D.h[i]; if(k>(P-1)/2) return false; } D.kap[c][j]=((S-1-c)%2? -(ll)k:(ll)k); }
  for(int j=1;j<S;j++){ ll N=0; for(int t=0;t<j;t++){ ll nu=llabs(D.kap[t][j]);
      if(t==0){ D.W[0][j]=nu; ll L=2*nu+1; if(L>=P) return false; N=1+(P-L+nu-1)/nu; }
      else { ll need=(N*nu-1+1)/2; ll Wt=std::max(nu,need); if(2*Wt+1>=P) return false; D.W[t][j]=Wt; N=N-1+(P+nu-1)/nu; } }
    if(N>P) return false; D.M[j]=N; }
  ll cost=0; for(int c=0;c<S;c++){ ll X=0; for(int e=c+1;e<S;e++) X+=D.W[c][e]; cost=std::max(cost,2*X+D.M[c]); } D.cost=cost; return true; }

// mrA_range.cpp -- copy-and-extend of the research program lexrule.cpp (not archived): rule MR-A (closed-form heights)
// for EVERY prime in [lo,hi]; Theorem MR: Gamma < p => valid design with LB >= (p-Gamma)/p.  Prints failures + summary.
// usage: mrA_range s lo hi
static bool isprime(ll n){ if(n<2) return false; for(ll d=2;d*d<=n;d++) if(n%d==0) return false; return true; }
int main(int argc,char**argv){
  S=atoi(argv[1]); ll lo=atoll(argv[2]), hi=atoll(argv[3]);
  m.assign(S,std::vector<ll>(S,0)); g=0; for(int c=0;c<S;c++) for(int j=c+1;j<S;j++){ m[c][j]=fact(S-1)/(fact(c)*fact(S-1-j)*(j-c)); g=gcdl(g,m[c][j]); }
  std::vector<double> gam(S,0); for(int t=1;t<S;t++){ double x=0; for(int j=t+1;j<S;j++) x+=(double)m[t][j]/m[t-1][j]; gam[t]=x+(double)g/m[t-1][t]; }
  ll np=0,nf=0,lastf=-1,firstok=-1; double minlb=2; ll pmin=-1;
  for(ll p=lo;p<=hi;p++){ if(!isprime(p)) continue; P=p; np++;
    double lp=std::log(2.0*m[0][S-1]/g); for(int t=1;t<S;t++) lp+=std::log(gam[t]*P); double C=std::exp(lp/S);
    R A; A.h.assign(S,1); for(int t=1;t<S;t++) A.h[t]=std::max<ll>(1,llround(gam[t]*P/C));
    bool ok=design(A)&&A.cost<P;
    if(!ok){ nf++; lastf=p; if(nf<=40) printf("FAIL %lld\n",p); }
    else { if(firstok<0) firstok=p; double lb=(double)(P-A.cost)/P; if(lb<minlb){ minlb=lb; pmin=p; } } }
  printf("s=%d [%lld,%lld]: primes %lld, MR-A failures %lld (last %lld), first ok %lld, min LBlex %.4f at %lld\n",S,lo,hi,np,nf,lastf,firstok,minlb,pmin);
}
