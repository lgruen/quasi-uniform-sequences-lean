// lat.cpp -- lambda_jit(Lambda_v) = min_{0 != a in Z^s, v.a = 0 mod p} || (|a| - 1)_+ ||_2   (nets paper prop:S1E)
// and lambda_inf, lambda_2. Exact by enumeration of a_0..a_{s-2} in [-B,B], a_{s-1} = centred solution (v_{s-1} unit).
// usage: lat p s v0,..,v_{s-1}            -> values for this v
//        lat p s kor                      -> Korobov v = (rho, rho^2, ..., rho^{s-1}, -1), rho = floor(p^{1/s})
//        lat p s search NRAND seed        -> best lambda_jit over v = (x_1..x_{s-1}, -1): exhaustive if p^{s-1} <= NRAND else random
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <vector>
#include <string>
#include <random>
#include <thread>
using namespace std; typedef long long ll;
ll P; int s;
static inline ll md(ll a){ a%=P; if(a<0)a+=P; return a; }
static ll pw(ll b,ll e){ b=md(b); ll r=1; while(e){ if(e&1) r=r*b%P; b=b*b%P; e>>=1;} return r; }
struct Res{ double jit2, l2sq; ll linf; };
// returns jit^2 (integer), lambda_2^2, lambda_inf ; cutoff: stop early if jit2 < cut (for search)
static Res eval(const vector<ll>& v, double cut=-1){
  ll ilast=pw(v[s-1],P-2); vector<ll> c(s-1); for(int i=0;i<s-1;i++) c[i]=md(-v[i]*ilast); // a_last = sum c_i a_i
  Res r{1e18,1e18,(ll)1e18};
  for(int B=2;;B++){ // enumerate |a_i|<=B for i<s-1
    vector<ll> a(s-1,-B); bool done=false; double best=r.jit2; ll bestinf=r.linf; double bestl2=r.l2sq;
    while(!done){
      bool nz=false; for(auto x:a) if(x) nz=true;
      ll al=0; for(int i=0;i<s-1;i++) al+=c[i]*md(a[i]); al%=P; if(al>P/2) al-=P;
      if(nz||al){ double j2=0,l2=0; ll li=0; for(int i=0;i<s-1;i++){ ll x=llabs(a[i]); l2+=x*x; li=max(li,x); if(x>1) j2+=(x-1)*(x-1); } ll x=llabs(al); l2+=x*x; li=max(li,x); if(x>1) j2+=(x-1)*(x-1);
        if(j2<best) best=j2; if(l2<bestl2) bestl2=l2; if(li<bestinf) bestinf=li; if(cut>=0 && best<cut) { r.jit2=best; return r; } }
      int i=0; while(i<s-1){ if(a[i]<B){a[i]++; break;} a[i]=-B; i++; } if(i==s-1) done=true;
    }
    r.jit2=best; r.l2sq=bestl2; r.linf=bestinf;
    // any vector with |a|_inf > B: if the max is among first s-1 coords, ||(|a|-1)+|| >= B; l2 >= B+1.  last coord centred
    double rb=B; if(r.jit2<=rb*rb && r.l2sq<=(B+1.0)*(B+1.0) && r.linf<=B+1) return r;
    if(B>P/2) return r;
  }
}
int main(int argc,char**argv){
  P=atoll(argv[1]); s=atoi(argv[2]); ll rho=(ll)floor(pow((double)P,1.0/s)+1e-9); while((double)pow((double)(rho+1),s)<=P) rho++; while(pow((double)rho,s)>P) rho--;
  double sc=pow((double)P,-1.0/s);
  if(!strcmp(argv[3],"kor")){ vector<ll> v(s); ll t=rho; for(int i=0;i<s-1;i++){ v[i]=md(t); t*=rho; } v[s-1]=md(-1); Res r=eval(v);
    printf("p=%lld s=%d Korobov rho=%lld: lambda_inf=%lld lambda_2=%.4f lambda_jit=%.4f  -> sep bound p^{-1/s}lambda_jit=%.4f (rho-1)p^{-1/s}=%.4f\n",P,s,rho,r.linf,sqrt(r.l2sq),sqrt(r.jit2),sqrt(r.jit2)*sc,(rho-1)*sc); return 0; }
  if(!strcmp(argv[3],"search")){ ll NR=atoll(argv[4]); unsigned seed=atoi(argv[5]); double tot=pow((double)P,s-1);
    int T=10; vector<double> bj(T,-1); vector<vector<ll>> bv(T);
    bool exh = tot<=NR; ll total = exh? (ll)tot : NR;
    vector<thread> th; for(int t=0;t<T;t++) th.emplace_back([&,t](){ mt19937_64 rng(seed*1000+t); vector<ll> v(s);
      for(ll it=t; it<total; it+=T){ if(exh){ ll x=it; for(int i=0;i<s-1;i++){ v[i]=x%P; x/=P; } } else for(int i=0;i<s-1;i++) v[i]=rng()%P;
        v[s-1]=P-1; bool ok=true; for(int i=0;i<s-1;i++) if(!v[i]) ok=false; if(!ok) continue;
        Res r=eval(v, bj[t]>0? bj[t]*bj[t]*0.999999 : -1); if(bj[t]<0 || r.jit2>bj[t]*bj[t]+1e-9){ bj[t]=sqrt(r.jit2); bv[t]=v; } } });
    for(auto&x:th) x.join(); int bt=0; for(int t=1;t<T;t++) if(bj[t]>bj[bt]) bt=t; if(bv[bt].empty()){ printf("no valid v\n"); return 0; }
    Res r=eval(bv[bt]); printf("p=%lld s=%d %s(%lld): best v=(",P,s,exh?"EXHAUSTIVE":"RANDOM",total); for(int i=0;i<s;i++) printf("%lld%s",bv[bt][i],i<s-1?",":""); printf(") lambda_inf=%lld lambda_2=%.4f lambda_jit=%.4f -> sep bound %.4f\n",r.linf,sqrt(r.l2sq),sqrt(r.jit2),sqrt(r.jit2)*sc); return 0; }
  vector<ll> v; { string t(argv[3]); size_t i=0; while(i<t.size()){ size_t j=t.find(',',i); if(j==string::npos) j=t.size(); v.push_back(md(atoll(t.substr(i,j-i).c_str()))); i=j+1; } }
  Res r=eval(v); printf("p=%lld s=%d v given: lambda_inf=%lld lambda_2=%.4f lambda_jit=%.4f -> sep bound %.4f\n",P,s,r.linf,sqrt(r.l2sq),sqrt(r.jit2),sqrt(r.jit2)*sc);
}
