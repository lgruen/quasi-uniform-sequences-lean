// audit_jit.cpp -- audit program: lambda_jit(Lambda_v)^2 = min_{0!=a in Z^s, v.a=0 mod p} sum_i ((|a_i|-1)_+)^2  (geo prop:S1E)
// Independent re-implementation. Enumerate a_0..a_{s-2} in [-B,B] (B = 1,2,...), a_{s-1} = centred solution of v.a=0
// (the centred lift minimises (|a_{s-1}|-1)_+ among the lifts). Termination: a vector with |a_i|>B for some i<s-1 has
// jit^2 >= B^2, so once best <= B^2 the value is exact.  Also lambda_inf (max-norm minimum) by the same scheme.
// usage: jit p s v0,...,v_{s-1}           (v given)
//        jit p s kor                      (v = (rho,...,rho^{s-1},-1), rho = floor(p^{1/s}))
//        jit p s search NMAX seed         (max over v=(x,-1), x in (F_p^*)^{s-1}: exhaustive if (p-1)^{s-1} <= NMAX else NMAX random)
#include <cstdio>
#include <climits>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <vector>
#include <random>
#include <string>
using namespace std; typedef long long ll;
ll P; int s;
static ll md(ll a){ a%=P; if(a<0)a+=P; return a; }
static ll pw(ll b,ll e){ b=md(b); ll r=1; while(e){ if(e&1) r=r*b%P; b=b*b%P; e>>=1; } return r; }
// returns jit2 exactly, or a value <= cut as soon as one is found (cut<0: no cutoff). linf optional.
static ll jit2(const vector<ll>& v, ll cut, ll* linf){
  ll il=pw(v[s-1],P-2); vector<ll> c(s-1); for(int i=0;i<s-1;i++) c[i]=md(-v[i]*il);
  ll best=LLONG_MAX, bi=LLONG_MAX; // a' = 0 gives a_last in pZ\0: jit2 (p-1)^2, linf p
  best=(P-1)*(P-1); bi=P;
  vector<ll> a(s-1);
  for(ll B=1;;B++){
    // enumerate the shell max|a_i| == B (i<s-1)
    for(int i=0;i<s-1;i++) a[i]=-B;
    while(true){
      ll mx=0; for(int i=0;i<s-1;i++) mx=max(mx,llabs(a[i]));
      if(mx==B){ ll t=0; for(int i=0;i<s-1;i++) t+=c[i]*md(a[i]); t%=P; if(t>P/2) t-=P;
        ll j=0, li=llabs(t); if(llabs(t)>1) j=(llabs(t)-1)*(llabs(t)-1);
        for(int i=0;i<s-1;i++){ ll x=llabs(a[i]); if(x>1) j+=(x-1)*(x-1); if(x>li) li=x; }
        if(j<best) best=j; if(li<bi) bi=li;
        if(cut>=0 && best<=cut) return best; }
      int i=0; while(i<s-1){ if(a[i]<B){ a[i]++; break; } a[i]=-B; i++; } if(i==s-1) break;
    }
    if(best<=B*B && bi<=B+1){ if(linf) *linf=bi; return best; }
    if(B>P){ if(linf) *linf=bi; return best; }
  }
}
int main(int argc,char**argv){
  P=atoll(argv[1]); s=atoi(argv[2]); ll rho=1; while(true){ ll t=1; for(int i=0;i<s;i++) t*=(rho+1); if(t<P) rho++; else break; }
  double sc=pow((double)P,-1.0/s);
  vector<ll> v(s);
  if(!strcmp(argv[3],"kor")){ ll t=rho; for(int i=0;i<s-1;i++){ v[i]=md(t); t*=rho; } v[s-1]=P-1; }
  else if(!strcmp(argv[3],"search")){
    ll NMAX=atoll(argv[4]); mt19937_64 rng(atoi(argv[5])); double tot=pow((double)(P-1),s-1); bool exh=tot<=NMAX; ll n=exh?(ll)tot:NMAX;
    ll best=-1; vector<ll> bv(s); vector<ll> w(s); w[s-1]=P-1;
    for(ll it=0;it<n;it++){
      if(exh){ ll x=it; for(int i=0;i<s-1;i++){ w[i]=1+x%(P-1); x/=(P-1); } } else for(int i=0;i<s-1;i++) w[i]=1+rng()%(P-1);
      ll j=jit2(w,best,nullptr); if(j>best){ best=jit2(w,-1,nullptr); bv=w; }
    }
    ll li; ll j=jit2(bv,-1,&li);
    printf("p=%lld s=%d %s(%lld v): best v=(",P,s,exh?"EXHAUSTIVE":"RANDOM",n); for(int i=0;i<s;i++) printf("%lld%s",bv[i],i<s-1?",":")");
    printf(" jit2=%lld lambda_jit=%.4f linf=%lld  bound p^{-1/s}lambda_jit=%.6f\n",j,sqrt((double)j),li,sqrt((double)j)*sc); return 0;
  } else { string t(argv[3]); size_t i=0; int k=0; while(i<t.size()&&k<s){ size_t j=t.find(',',i); if(j==string::npos) j=t.size(); v[k++]=md(atoll(t.substr(i,j-i).c_str())); i=j+1; } }
  ll li; ll j=jit2(v,-1,&li);
  printf("p=%lld s=%d rho=%lld v=(",P,s,rho); for(int i=0;i<s;i++) printf("%lld%s",v[i],i<s-1?",":")");
  printf(" jit2=%lld lambda_jit=%.4f linf=%lld  bound=%.6f  (rho-1)p^{-1/s}=%.6f  1-2p^{-1/s}=%.6f\n",j,sqrt((double)j),li,sqrt((double)j)*sc,(rho-1)*sc,1-2*sc);
}
