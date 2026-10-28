// Audit program: adversarial random frame generator (own code). One frame per line, bases ';'-separated, coeffs low->high.
// usage: gen3 p "e1,e2,..." count seed mode
//  mode 0: random bases, random nonzero leading coefficient (non-monic)
//  mode 1: every base of degree>=2 is FORCED reducible with a repeated factor: const * f^r * g  (deg f>=1, r>=2)
//  mode 2: base 0 is const*(X-a)^e (pure power of a linear factor), others random non-monic
//  mode 3: base 0 random non-monic; others are distinct linear factors X-a (Theta = many linear factors)
#include <vector>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <random>
#include <cstdint>
using namespace std; typedef vector<int64_t> V; static int64_t p; static mt19937_64 rng;
static int64_t M(int64_t a){ a%=p; return a<0?a+p:a; }
static int64_t IV(int64_t a){ int64_t r=1,b=M(a),e=p-2; while(e){ if(e&1) r=r*b%p; b=b*b%p; e>>=1;} return r; }
static void tr(V&a){ while(!a.empty()&&a.back()==0) a.pop_back(); }
static V mulp(const V&a,const V&b){ if(a.empty()||b.empty()) return V(); V r(a.size()+b.size()-1,0); for(size_t i=0;i<a.size();i++) for(size_t j=0;j<b.size();j++) r[i+j]=M(r[i+j]+a[i]*b[j]); tr(r); return r; }
static V modp(V a,const V&b){ tr(a); int d=b.size()-1; int64_t il=IV(b.back()); for(int i=(int)a.size()-1;i>=d;i--){ int64_t c=M(a[i]*il); if(!c) continue; for(int j=0;j<=d;j++) a[i-d+j]=M(a[i-d+j]-c*b[j]); } tr(a); return a; }
static int gdeg(V a,V b){ tr(a); tr(b); while(!b.empty()){ V r=modp(a,b); a=b; b=r; } return (int)a.size()-1; }
static V rnd(int e,bool monic){ V a(e+1); for(int i=0;i<e;i++) a[i]=rng()%p; a[e]= monic?1:1+rng()%(p-1); return a; }
int main(int argc,char**argv){ p=atoll(argv[1]); vector<int> E; { string s=argv[2]; size_t i=0; while(i<s.size()){ size_t j=s.find(',',i); if(j==string::npos) j=s.size(); E.push_back(atoi(s.substr(i,j-i).c_str())); i=j+1; } }
  int cnt=atoi(argv[3]); rng.seed(atoll(argv[4])); int mode=atoi(argv[5]); int s=E.size(); int made=0; long tries=0;
  while(made<cnt && tries<200000){ tries++; vector<V> B(s);
    for(int c=0;c<s;c++){ int e=E[c];
      if(mode==1 && e>=2){ int df=1+rng()%(e/2); int r=2+rng()%(e/df-1); if(df*r>e) r=e/df; int dg_=e-df*r; V f=rnd(df,true); V b{1+(int64_t)(rng()%(p-1))}; for(int k=0;k<r;k++) b=mulp(b,f); if(dg_>0) b=mulp(b,rnd(dg_,true)); B[c]=b; }
      else if(mode==2 && c==0){ int64_t a=rng()%p; V b{1+(int64_t)(rng()%(p-1))}; for(int k=0;k<e;k++) b=mulp(b,V{M(-a),1}); B[c]=b; }
      else if(mode==3 && c>0){ B[c]=V{(int64_t)(rng()%p),1}; }
      else B[c]=rnd(e,false); }
    bool ok=true; for(int i=0;i<s&&ok;i++) for(int j=i+1;j<s&&ok;j++) if(gdeg(B[i],B[j])>0) ok=false;
    if(!ok) continue; made++;
    for(int c=0;c<s;c++){ for(size_t i=0;i<B[c].size();i++) printf("%lld%s",(long long)B[c][i],i+1<B[c].size()?",":""); printf("%s",c+1<s?";":"\n"); } }
  if(made<cnt) fprintf(stderr,"only %d frames\n",made);
}
