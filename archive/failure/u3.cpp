// Audit program: FRESH, self-contained checker of the explicit close pairs behind thm:nonqu / cor:halton.
// Written from scratch (no poly.hpp, no audit/hw.cpp, no deg/*). Builds the witness DIRECTLY from the theorem's
// formula D_q = c^{-1} rho b^{qz} S_{qN} Theta^{qk} (no seed/lift route), computes N and k itself by brute force,
// and evaluates the two points from GHS26 Def. 1 (b(X)-adic expansion, coefficient of X^{e-1} most significant),
// either exactly (full expansion, small m) or modulo b_c^{K_c} with guard digits (digits beyond K_c contribute
// < p^{-e_c K_c} <= p^{-L-G}).  Distances: Euclidean, non-torus (GHS26 Sec. 1).
// usage: u3 p "frame" c0 wmax Lmax [kmult=1] [G=12] [full=0]
//   frame: bases separated by ';', coefficients low->high separated by ','  (e.g. "1,0,1;2,1,1")
// prints one line per w: params, carry/zero pattern checks, deg checks, dist*p^L vs sqrt(s+3), sep=dist*p^{m/s}.
#include <vector>
#include <string>
#include <sstream>
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <cstdint>
#include <algorithm>
#include <numeric>
using namespace std;
typedef vector<int64_t> V;
static int64_t p;
static int64_t M(int64_t a){ a%=p; return a<0?a+p:a; }
static int64_t PW(int64_t a,int64_t e){ int64_t r=1; a=M(a); while(e){ if(e&1) r=r*a%p; a=a*a%p; e>>=1;} return r; }
static int64_t IV(int64_t a){ return PW(a,p-2); }
static void tr(V&a){ while(!a.empty()&&a.back()==0) a.pop_back(); }
static int dg(const V&a){ return (int)a.size()-1; }
static V mulp(const V&a,const V&b){ if(a.empty()||b.empty()) return V(); vector<unsigned __int128> r(a.size()+b.size()-1,0);
  for(size_t i=0;i<a.size();i++) if(a[i]) for(size_t j=0;j<b.size();j++) r[i+j]+=(unsigned __int128)(a[i]*b[j]);
  V o(r.size()); for(size_t i=0;i<r.size();i++) o[i]=(int64_t)(r[i]%(unsigned __int128)p); tr(o); return o; }
static V addp(const V&a,const V&b){ V r(max(a.size(),b.size()),0); for(size_t i=0;i<a.size();i++) r[i]=a[i]; for(size_t i=0;i<b.size();i++) r[i]=M(r[i]+b[i]); tr(r); return r; }
static V scp(V a,int64_t c){ for(auto&x:a) x=M(x*c); tr(a); return a; }
static void dvm(V a,const V&b,V&q,V&r){ tr(a); int n=dg(a), d=dg(b); int64_t il=IV(b.back()); q.assign(max(0,n-d+1),0);
  for(int i=n;i>=d;i--){ int64_t c=M(a[i]*il); if(!c) continue; q[i-d]=c; for(int j=0;j<=d;j++) a[i-d+j]=M(a[i-d+j]-c*b[j]); }
  tr(a); tr(q); r=a; }
static V modp(const V&a,const V&m){ V q,r; dvm(a,m,q,r); return r; }
static V mulm(const V&a,const V&b,const V&m){ return modp(mulp(a,b),m); }
static V powm(V a,int64_t e,const V&m){ V r{1}; r=modp(r,m); a=modp(a,m); while(e){ if(e&1) r=mulm(r,a,m); e>>=1; if(e) a=mulm(a,a,m);} return r; }
static V powp(V a,int64_t e){ V r{1}; while(e){ if(e&1) r=mulp(r,a); e>>=1; if(e) a=mulp(a,a);} return r; }
static bool isconst(const V&a){ return dg(a)<=0; }
static bool isone(const V&a){ return a.size()==1&&a[0]==1; }
// geometric sum S_n = sum_{j<n} b^j  mod m  (doubling; no division by b-1)
static pair<V,V> geo(const V&b,int64_t n,const V&m){ // returns (S_n, b^n) mod m
  if(n==0) return {V(),modp(V{1},m)};
  auto h=geo(b,n/2,m); V S=addp(h.first,mulm(h.first,h.second,m)); V B=mulm(h.second,h.second,m);
  if(n&1){ S=addp(modp(V{1},m),mulm(b,S,m)); B=mulm(B,b,m); }
  return {modp(S,m),B}; }
// b-adic digits per Def. 1: returns base-p digit string (most significant first) of the first K b-digits of n
static vector<int> digs(V n,const V&b,int K){ int e=dg(b); vector<int> out; out.reserve((size_t)K*e);
  for(int j=0;j<K;j++){ V q,r; dvm(n,b,q,r); for(int i=e-1;i>=0;i--) out.push_back(i<(int)r.size()?(int)r[i]:0); n=q; }
  return out; }
// exact |x-y| * p^L from two digit strings of equal length T (positions 1..T): normalised signed difference
static long double absdiff_scaled(const vector<int>&a,const vector<int>&b,int64_t L){ size_t T=a.size(); vector<int64_t> d(T);
  for(size_t i=0;i<T;i++) d[i]=a[i]-b[i];
  for(int pass=0;pass<2;pass++){ vector<int64_t> r(T); int64_t carry=0;
    for(int i=(int)T-1;i>=0;i--){ int64_t v=d[i]+carry; int64_t rr=((v%p)+p)%p; carry=(v-rr)/p; r[i]=rr; }
    if(carry<0){ for(auto&x:d) x=-x; continue; }
    // value = sum r[i] p^{-(i+1)};  times p^L
    long double acc=0; for(size_t i=0;i<T;i++) if(r[i]){ long double ex=(long double)L-(long double)(i+1); if(ex>60) return 1e30L; acc+= r[i]*powl((long double)p,ex); }
    return acc; }
  return 0; }
int main(int argc,char**argv){
  if(argc<6){ fprintf(stderr,"usage\n"); return 1; }
  p=atoll(argv[1]); string fs=argv[2]; int c0=atoi(argv[3]); int wmax=atoi(argv[4]); int64_t Lmax=atoll(argv[5]);
  int64_t kmult=argc>6?atoll(argv[6]):1; int G=argc>7?atoi(argv[7]):12; int full=argc>8?atoi(argv[8]):0;
  vector<V> B; { stringstream ss(fs); string t; while(getline(ss,t,';')){ V b; stringstream s2(t); string u; while(getline(s2,u,',')) b.push_back(M(atoll(u.c_str()))); tr(b); B.push_back(b);} }
  int s=B.size(); for(auto&b:B) if(dg(b)<1){ printf("BADFRAME deg<1\n"); return 1; }
  // pairwise coprimality (Euclid)
  for(int i=0;i<s;i++) for(int j=i+1;j<s;j++){ V a=B[i], c=B[j]; while(!c.empty()){ V r=modp(a,c); a=c; c=r; } if(dg(a)>0){ printf("BADFRAME not coprime %d %d\n",i,j); return 1; } }
  V b=B[c0]; int e=dg(b); int64_t E=1; for(auto&x:B) E=E/std::gcd(E,(int64_t)dg(x))*dg(x);
  V Th{1}; for(int c=0;c<s;c++) if(c!=c0) Th=mulp(Th,powp(B[c],E/dg(B[c])));
  V R=mulp(addp(V{1},scp(b,p-1)),Th);
  // N: brute-force multiplicative order of b mod R
  V bb=modp(b,R), cur=bb; int64_t N=1; while(!isone(cur)){ cur=mulm(cur,bb,R); if(++N>3000000){ printf("SKIP N>3e6\n"); return 0; } }
  // k0: least k>=1 with Theta^k == const mod b^N
  V bN=powp(b,N); V th=modp(Th,bN), tk=th; int64_t k0=1; while(!isconst(tk)){ tk=mulm(tk,th,bN); if(++k0>3000000){ printf("SKIP k0>3e6\n"); return 0; } }
  if(tk.empty()){ printf("ERROR Theta^k0 == 0 mod b^N\n"); return 1; }
  if(getenv("CTRL")&&atoi(getenv("CTRL"))==1&&N>1) N--; /* negative control: wrong N */
  int64_t k=k0*kmult; if(getenv("CTRL")&&atoi(getenv("CTRL"))==2) k=k0*kmult+1; /* control: Theta^k not const */ while((E/e)*(k+1)<N) k+=k0; int64_t cc=PW(tk[0],k/k0); // Theta^k == cc mod b^N
  int64_t z=(E/e)*(k+1)-N;
  printf("p=%lld s=%d c0=%d e=%d E=%lld degR=%d N=%lld k0=%lld k=%lld c=%lld z=%lld\n",(long long)p,s,c0,e,(long long)E,dg(R),(long long)N,(long long)k0,(long long)k,(long long)cc,(long long)z);
  int64_t q=1; int fails=0; bool scr=getenv("SCR")!=nullptr; uint64_t scrseed=scr?strtoull(getenv("SCR"),0,10):0; int64_t su=scr?1+(int64_t)((scrseed*2654435761ULL)%(uint64_t)(p-1)):1; if(scr) printf("SCR u=%lld seed=%llu\n",(long long)su,(unsigned long long)scrseed);
  for(int w=0;w<=wmax;w++,q*=p){
    int64_t L=q*E*(k+1), m=q*(s*E*(k+1)-(s-1)*E);
    if(L>Lmax){ printf("w=%d L=%lld > Lmax: not run\n",w,(long long)L); break; }
    int64_t degD=(e-1)+e*q*z+e*(q*N-1)+q*k*dg(Th);
    bool ok=true; string why;
    if(degD!=m-1){ ok=false; why+=" degD!=m-1"; }
    V rho(e,1);
    double sum2=0; bool fullmode = full && m<=4000;
    V Dfull, yfull;
    // y_q = (p-1)[rho_{e-1} b^{qz} + rho b^{qz+1} S_{qN-1}]  built in full (deg < L)
    { V rhoe1(max(e-1,0),1); tr(rhoe1); V bz=powp(b,q*z); V S{}; V bj=mulp(bz,b); for(int64_t j=0;j<q*N-1;j++){ S=addp(S,bj); bj=mulp(bj,b); }
      yfull=scp(addp(mulp(rhoe1,bz),mulp(rho,S)),p-1); }
    if(dg(yfull)>=m){ ok=false; why+=" deg y>=m"; }
    if(fullmode){ V S{}; V bj{1}; for(int64_t j=0;j<q*N;j++){ S=addp(S,bj); bj=mulp(bj,b);}
      Dfull=scp(mulp(mulp(mulp(rho,powp(b,q*z)),S),powp(Th,q*k)),IV(cc)); if(dg(Dfull)!=m-1){ ok=false; why+=" full degD"; } }
    long double tot=0;
    for(int c=0;c<s;c++){
      int ec=dg(B[c]); int Kc=(int)((L+G+ec-1)/ec); V Mc=powp(B[c],Kc);
      V D;
      if(fullmode) D=modp(Dfull,Mc);
      else { auto gs=geo(modp(b,Mc),q*N,Mc); V t=mulm(gs.first,powm(b,q*z,Mc),Mc); t=mulm(t,powm(Th,q*k,Mc),Mc); t=mulm(t,modp(rho,Mc),Mc); D=scp(t,IV(cc)); }
      V y=modp(yfull,Mc), x=addp(y,D); x=modp(x,Mc);
      auto dD=digs(D,B[c],Kc);
      if(scr){ x=scp(x,IV(su)); y=scp(y,IV(su)); } // Cor U-S: pair rescaled by u^{-1}
      auto dx=digs(x,B[c],Kc), dy=digs(y,B[c],Kc);
      if(scr){ size_t T=dx.size(); auto apply=[&](vector<int>&d){ vector<int> o(T);
          for(size_t i=0;i<T;i++){ if(c==c0 && !getenv("SCRC0")){ o[i]=(int)M((int64_t)d[i]*su); continue; }
            unsigned __int128 acc=0; for(size_t j=0;j<=i;j++){ uint64_t h=((uint64_t)c*1000003ULL+i)*0x9E3779B97F4A7C15ULL ^ (j*0xC2B2AE3D27D4EB4FULL+scrseed); h^=h>>31; h*=0xBF58476D1CE4E5B9ULL; h^=h>>29;
              int64_t Lij = (j==i)? 1+(int64_t)(h%(uint64_t)(p-1)) : (int64_t)(h%(uint64_t)p); acc+=(unsigned __int128)(Lij*d[j]); }
            o[i]=(int)(acc%(unsigned __int128)p); } d=o; }; apply(dx); apply(dy); }
      if(c==c0){ for(int64_t i=0;i<L;i++){ int want=(i<e*q*z)?0:1; if(dD[i]!=want){ ok=false; why+=" carry@"+to_string(i); break; } } }
      else { for(int64_t i=0;i<L;i++) if(dD[i]!=0){ ok=false; why+=" zero@c"+to_string(c)+":"+to_string(i); break; } }
      long double a=absdiff_scaled(dx,dy,L); if(c==c0 && !(a>0)) { ok=false; why+=" c0 equal"; }
      tot+=a*a;
    }
    long double r=sqrtl(tot); long double sep=r*powl((long double)p,(long double)m/s-(long double)L);
    bool dok = r<sqrtl((long double)s+3);
    if(!(ok&&dok)) fails++;
    printf("w=%d q=%lld L=%lld m=%lld def=%lld dist*p^L=%.4Lf (<%.3f %s) sep=%.3Le %s%s%s\n",w,(long long)q,(long long)L,(long long)m,(long long)(s*L-m),r,sqrt(s+3.0),dok?"OK":"VIOL",sep,ok?"patterns OK":"FAIL",why.c_str(),fullmode?" [full]":" [mod]");
  }
  printf("RESULT %s\n",fails?"FAIL":"PASS");
}
