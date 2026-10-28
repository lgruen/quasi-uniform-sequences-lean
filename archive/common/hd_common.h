// hd_common.h -- general-s helpers for brick-star (0,s)-sequences, s = 4, 5.
// F_p arithmetic; p*f_1 of rem:onedigit in INTEGERS; exact window certificate (lem:cert, j = 1) for product
// integer-interval windows in any s; line-covering checkers for k = s-1 cross coordinates:
//   (a) cover_brute   : bitmap of Z_p^k (validation only, tiny p);
//   (b) cover_sweep   : EXACT, recursive slab sweep (k = 1, 2 closed form / dynamic gap count; k >= 3 recursion);
//   (c) cover_lattice : SUFFICIENT (PROOF), fundamental parallelepiped of the lattice L' = {(o,x): x = o v mod p}
//                       inside the box [0,M) x prod [0,L_j)  (a lemma of the research notes).
// Covering question (Prop CW_s (ii)): for all sigma in Z_p^k there is j in [0,M) with sigma + j v in prod [0, L_c).
// Equivalently the boxes  B_j = prod_c [-j v_c, -j v_c + L_c)  (j < M) cover the torus Z_p^k.
#pragma once
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <string>
#include <random>
typedef long long ll;
static ll P;
static inline ll md(ll a){ a%=P; if(a<0) a+=P; return a; }
static inline ll mulm(ll a,ll b){ return P<(1LL<<31)? (ll)((unsigned long long)a*(unsigned long long)b%(unsigned long long)P) : (ll)((__int128)a*b%P); } // a,b in [0,P)
static inline ll pw(ll a,ll e){ ll r=1; a=md(a); while(e){ if(e&1) r=mulm(r,a); a=mulm(a,a); e>>=1; } return r; }
static inline ll inv(ll a){ return pw(a,P-2); }
static inline ll cen(ll a){ a=md(a); return a>P/2? a-P: a; }
// p * f_1(e, sigma)  (integer; rem:onedigit, prime p, one geometric digit)
static inline ll pf1(int e, ll sg){
  ll r=md(sg);
  if(e==0){ ll c=std::min(r,P-r); return c>0? c-1 : 0; }
  if(e<0) r=md(-sg);
  return r==0? P-1 : r-1;
}
// min of p*f_1(e, .) over the integer interval [lo,hi]
static inline ll pf1min(int e, ll lo, ll hi){
  if(hi-lo+1>=P) return 0;
  if(e<0){ ll t=lo; lo=-hi; hi=-t; e=1; }
  if(e>0){ ll k=lo+md(1-lo); if(k<=hi) return 0; return pf1(1,lo); }
  for(ll r=-1;r<=1;r++){ ll k=lo+md(r-lo); if(k<=hi) return 0; }
  return std::min(pf1(0,lo),pf1(0,hi));
}
struct IW { ll lo,hi; };
// steps e in {-1,0,1}^s \ 0 up to sign (first nonzero = +1)
static std::vector<std::vector<int>> steps_s(int s){ std::vector<std::vector<int>> R; int n=1; for(int i=0;i<s;i++) n*=3;
  for(int k=0;k<n;k++){ std::vector<int> e(s); int x=k; for(int i=0;i<s;i++){ e[i]=x%3-1; x/=3; }
    int f=0; for(int i=0;i<s;i++) if(e[i]){ f=e[i]; break; } if(f==1) R.push_back(e); } return R; }
// Window certificate: S[c][cp] = window (integer interval) of column cp in coordinate c (own: c==cp).
// returns minS = min_e sum_c (p f_1min)^2 (integer); LB = sqrt(minS)/p.  worst = binding step.
static ll window_minS(int s, const std::vector<std::vector<IW>>& S, std::vector<int>* worst=nullptr){
  static std::vector<std::vector<int>> ST; static int sST=-1; if(sST!=s){ ST=steps_s(s); sST=s; }
  ll best=-1;
  for(auto&e:ST){ ll tot=0;
    for(int c=0;c<s;c++){ ll lo=0,hi=0; for(int cp=0;cp<s;cp++) if(e[cp]){ if(e[cp]>0){ lo+=S[c][cp].lo; hi+=S[c][cp].hi; } else { lo-=S[c][cp].hi; hi-=S[c][cp].lo; } }
      ll m=pf1min(e[c],lo,hi); tot+=m*m; if(best>=0 && tot>=best) break; }
    if(best<0||tot<best){ best=tot; if(worst) *worst=e; } }
  return best; }

// ---------------- covering: brute force (validation) ----------------
// v[k] residues, L[k] arc lengths (arcs [0,L)), returns minimal M <= cap or -1.  k <= 4, p^k <= ~2e7.
static ll cover_brute(int k, const std::vector<ll>& v, const std::vector<ll>& L, ll cap){
  ll N=1; for(int i=0;i<k;i++) N*=P; std::vector<char> cov(N,0); ll left=N;
  for(ll j=0;j<cap;j++){ // box with corner t = -j v
    ll t[6]; for(int c=0;c<k;c++) t[c]=md(-j*v[c]);
    ll Lc[6]; for(int c=0;c<k;c++) Lc[c]=std::min(L[c],P);
    // iterate over box points
    ll idx[6]={0,0,0,0,0,0};
    while(true){ ll id=0; for(int c=0;c<k;c++) id=id*P+(t[c]+idx[c])%P; if(!cov[id]){ cov[id]=1; left--; }
      int c=k-1; while(c>=0){ idx[c]++; if(idx[c]<Lc[c]) break; idx[c]=0; c--; } if(c<0) break; }
    if(left==0) return j+1; }
  return -1; }

// ---------------- covering: exact slab sweep ----------------
// corners: flat array, box b has corner T[b*k + c]; lengths L[c]; returns true iff the boxes cover Z_p^k.
struct GapSet { // multiset of residues on Z_p with count of cyclic gaps > Lg
  std::map<ll,int> cnt; ll bad=0, Lg;
  ll gap(ll a, ll b) const { ll g=md(b-a); return g==0? P : g; }
  void ins(ll c){ auto it=cnt.find(c); if(it!=cnt.end()){ it->second++; return; }
    if(cnt.empty()){ cnt[c]=1; bad=(P>Lg)?1:0; return; }
    auto nx=cnt.upper_bound(c); if(nx==cnt.end()) nx=cnt.begin();
    auto pv=cnt.lower_bound(c); if(pv==cnt.begin()) pv=std::prev(cnt.end()); else pv=std::prev(pv);
    bad-= gap(pv->first,nx->first)>Lg; bad+= gap(pv->first,c)>Lg; bad+= gap(c,nx->first)>Lg; cnt[c]=1; }
  void del(ll c){ auto it=cnt.find(c); if(it->second>1){ it->second--; return; }
    if(cnt.size()==1){ cnt.clear(); bad=0; return; }
    auto nx=std::next(it); if(nx==cnt.end()) nx=cnt.begin(); auto pv= it==cnt.begin()? std::prev(cnt.end()) : std::prev(it);
    bad-= gap(pv->first,c)>Lg; bad-= gap(c,nx->first)>Lg; cnt.erase(it); bad+= gap(pv->first,nx->first)>Lg; }
  bool covered() const { return !cnt.empty() && bad==0; }
};
static bool cover1(const std::vector<ll>& t, ll L){ if(t.empty()) return false; if(L>=P) return true;
  std::vector<ll> u=t; std::sort(u.begin(),u.end()); u.erase(std::unique(u.begin(),u.end()),u.end());
  for(size_t i=0;i+1<u.size();i++) if(u[i+1]-u[i]>L) return false; return (u[0]+P-u.back())<=L; }
static bool cover_rec(int k, const std::vector<ll>& T, const ll* L);
// k = 2: sweep along coordinate 0 with a dynamic gap set in coordinate 1
static bool cover2(const std::vector<ll>& T, const ll* L){
  size_t n=T.size()/2; if(n==0) return false;
  if(L[0]>=P){ std::vector<ll> t(n); for(size_t b=0;b<n;b++) t[b]=T[2*b+1]; return cover1(t,L[1]); }
  GapSet G; G.Lg=L[1];
  std::vector<std::pair<ll,ll>> ev; ev.reserve(2*n); // (pos, +/-(b+1)) ; removals first at equal pos
  for(size_t b=0;b<n;b++){ ll t0=T[2*b]; if(md(-t0)<L[0]) G.ins(T[2*b+1]);
    if(t0!=0) ev.push_back({t0,(ll)(b+1)}); ll r=(t0+L[0])%P; if(r!=0) ev.push_back({r,-(ll)(b+1)}); }
  if(!G.covered()) return false;
  std::sort(ev.begin(),ev.end(),[](const std::pair<ll,ll>&x,const std::pair<ll,ll>&y){ if(x.first!=y.first) return x.first<y.first; return x.second<y.second; });
  size_t i=0; while(i<ev.size()){ ll x=ev[i].first; while(i<ev.size()&&ev[i].first==x){ ll b=llabs(ev[i].second)-1; if(ev[i].second<0) G.del(T[2*b+1]); else G.ins(T[2*b+1]); i++; }
    if(!G.covered()) return false; }
  return true; }
// k >= 3: sweep along coordinate 0; at each event position test the active boxes in the remaining k-1 coordinates
static bool cover_rec(int k, const std::vector<ll>& T, const ll* L){
  if(k==1){ return cover1(T,L[0]); }
  if(k==2) return cover2(T,L);
  size_t n=T.size()/k; if(n==0) return false;
  std::vector<ll> sub; sub.reserve(T.size());
  auto proj=[&](const std::vector<size_t>& act){ sub.clear(); for(size_t b:act) for(int c=1;c<k;c++) sub.push_back(T[b*k+c]); return cover_rec(k-1,sub,L+1); };
  if(L[0]>=P){ std::vector<size_t> act(n); for(size_t b=0;b<n;b++) act[b]=b; return proj(act); }
  std::vector<ll> pos; pos.push_back(0); for(size_t b=0;b<n;b++){ pos.push_back(T[b*k]); pos.push_back((T[b*k]+L[0])%P); }
  std::sort(pos.begin(),pos.end()); pos.erase(std::unique(pos.begin(),pos.end()),pos.end());
  // active set maintained incrementally
  std::vector<ll> where(n,-1); std::vector<size_t> act;
  auto add=[&](size_t b){ if(where[b]>=0) return; where[b]=act.size(); act.push_back(b); };
  auto rem=[&](size_t b){ if(where[b]<0) return; size_t w=where[b]; size_t last=act.back(); act[w]=last; where[last]=w; act.pop_back(); where[b]=-1; };
  std::vector<std::vector<std::pair<int,size_t>>> evs(pos.size());
  auto pidx=[&](ll x){ return (size_t)(std::lower_bound(pos.begin(),pos.end(),x)-pos.begin()); };
  for(size_t b=0;b<n;b++){ ll t0=T[b*k]; if(md(-t0)<L[0]) add(b); evs[pidx(t0)].push_back({1,b}); evs[pidx((t0+L[0])%P)].push_back({0,b}); }
  for(size_t q=0;q<pos.size();q++){
    if(q>0){ for(auto&e:evs[q]) if(e.first==0) rem(e.second); for(auto&e:evs[q]) if(e.first==1) add(e.second); }
    if(!proj(act)) return false; }
  return true; }
// Build corners for column data (v, L) and the first M boxes; coordinates permuted so L ascending (outer = smallest).
static bool cover_test(int k, const std::vector<ll>& v, const std::vector<ll>& L, ll M){
  std::vector<int> ord(k); for(int i=0;i<k;i++) ord[i]=i; std::sort(ord.begin(),ord.end(),[&](int a,int b){ return L[a]<L[b]; });
  std::vector<ll> T((size_t)M*k); ll Ls[6]; for(int c=0;c<k;c++) Ls[c]=std::min(L[ord[c]],P);
  for(ll j=0;j<M;j++) for(int c=0;c<k;c++) T[(size_t)j*k+c]=mulm(md(-j),md(v[ord[c]]));
  return cover_rec(k,T,Ls); }
// minimal M (exact) by galloping + bisection on the monotone predicate; lo = counting bound. -1 if > cap.
static ll cover_min(int k, const std::vector<ll>& v, const std::vector<ll>& L, ll cap, ll guess=0){
  double vol=1; for(int c=0;c<k;c++) vol*= (double)std::min(L[c],P)/P; ll lo=(ll)ceil(1.0/vol - 1e-9); if(lo<1) lo=1;
  if(lo>cap) return -1;
  ll hi = guess>lo? guess : 2*lo; if(hi>cap) hi=cap;
  while(!cover_test(k,v,L,hi)){ if(hi>=cap) return -1; lo=hi+1; hi=std::min(cap,2*hi); }
  while(lo<hi){ ll m=(lo+hi)/2; if(cover_test(k,v,L,m)) hi=m; else lo=m+1; }
  return lo; }
// sampled LOWER bound on the minimal M: for sampled positions x of the smallest-L coordinate, minimal prefix of the boxes
// active at x that covers the remaining (k-1)-torus.  (exact for the sampled slabs; a lower bound for the full M)
static ll cover_min_sampled(int k, const std::vector<ll>& v, const std::vector<ll>& L, ll cap, const std::vector<ll>& xs){
  int o=0; for(int c=1;c<k;c++) if(L[c]<L[o]) o=c;
  std::vector<int> rest; for(int c=0;c<k;c++) if(c!=o) rest.push_back(c);
  std::sort(rest.begin(),rest.end(),[&](int a,int b){ return L[a]<L[b]; });
  ll Ls[6]; for(int i=0;i<k-1;i++) Ls[i]=std::min(L[rest[i]],P);
  ll Mmax=0; ll vo=md(v[o]);
  std::vector<ll> js; std::vector<ll> T;
  for(ll x:xs){ js.clear(); ll y=md(x); // position x covered by box j iff (x + j v_o) mod p < L_o
    for(ll j=0;j<cap;j++){ if(y<L[o]) js.push_back(j); y+=vo; if(y>=P) y-=P; }
    auto test=[&](size_t m){ T.clear(); for(size_t q=0;q<m;q++){ ll j=js[q]; for(int c:rest) T.push_back(mulm(md(-j),md(v[c]))); } return cover_rec(k-1,T,Ls); };
    if(js.empty()||!test(js.size())) return -1;
    size_t lo=1, hi=js.size(); while(lo<hi){ size_t m=(lo+hi)/2; if(test(m)) hi=m; else lo=m+1; }
    Mmax=std::max(Mmax,js[lo-1]+1); }
  return Mmax; }

// ---------------- covering: lattice parallelepiped criterion (sufficient) ----------------
// Lemma LP: if the lattice L' = Z(1,v) + pZ^k (in Z^{k+1}, coordinate 0 = own index o) has a basis b_1..b_{k+1} with
// S_j := sum_i |b_i[j]| <= L_j (j = 1..k) then every set of M >= S_0 consecutive own values covers.
// We search a basis by weighted LLL + greedy l1-column-sum descent; returns the certified M (= S_0) or -1.
static ll cover_lattice(int k, const std::vector<ll>& v, const std::vector<ll>& L, double Mtarget, std::vector<std::vector<ll>>* basis=nullptr){
  int n=k+1; std::vector<std::vector<ll>> B(n,std::vector<ll>(n,0)); B[0][0]=1; for(int c=0;c<k;c++) B[0][c+1]=cen(v[c]);
  for(int c=0;c<k;c++) B[c+1][c+1]=P;
  std::vector<long double> wgt(n); wgt[0]=1.0L/Mtarget; for(int c=0;c<k;c++) wgt[c+1]=1.0L/(long double)L[c];
  auto dot=[&](const std::vector<ll>&x,const std::vector<ll>&y){ long double s=0; for(int j=0;j<n;j++) s+=(long double)x[j]*y[j]*wgt[j]*wgt[j]; return s; };
  // LLL (delta = 0.99), floating Gram-Schmidt recomputed (n <= 6: cheap)
  for(int it=0; it<2000; it++){
    std::vector<std::vector<long double>> Bs(n,std::vector<long double>(n)), mu(n,std::vector<long double>(n,0)); std::vector<long double> nb(n);
    for(int i=0;i<n;i++){ for(int j=0;j<n;j++) Bs[i][j]=B[i][j]*wgt[j];
      for(int l=0;l<i;l++){ long double d=0; for(int j=0;j<n;j++) d+=(long double)B[i][j]*wgt[j]*Bs[l][j]; mu[i][l]=d/nb[l]; for(int j=0;j<n;j++) Bs[i][j]-=mu[i][l]*Bs[l][j]; }
      nb[i]=0; for(int j=0;j<n;j++) nb[i]+=Bs[i][j]*Bs[i][j]; }
    bool changed=false;
    for(int i=1;i<n && !changed;i++){
      for(int l=i-1;l>=0;l--){ ll q=llroundl(mu[i][l]); if(q){ for(int j=0;j<n;j++) B[i][j]-=q*B[l][j]; changed=true; } }
      if(changed) break;
      if(nb[i] < (0.99L - mu[i][i-1]*mu[i][i-1])*nb[i-1]){ std::swap(B[i],B[i-1]); changed=true; } }
    if(!changed) break; }
  // greedy descent on F = max_j S_j * wgt_j (l1 column sums, weighted)
  auto F=[&](){ long double f=0; for(int j=0;j<n;j++){ long double s=0; for(int i=0;i<n;i++) s+=llabs(B[i][j]); f=std::max(f,s*wgt[j]); } return f; };
  long double cur=F();
  for(int it=0; it<500; it++){ bool imp=false;
    for(int i=0;i<n;i++) for(int l=0;l<n;l++) if(i!=l) for(int sg=-1;sg<=1;sg+=2){
      for(int j=0;j<n;j++) B[i][j]+=sg*B[l][j]; long double f=F(); if(f<cur-1e-15L){ cur=f; imp=true; } else for(int j=0;j<n;j++) B[i][j]-=sg*B[l][j]; }
    if(!imp) break; }
  ll S[8]; for(int j=0;j<n;j++){ S[j]=0; for(int i=0;i<n;i++) S[j]+=llabs(B[i][j]); }
  for(int c=0;c<k;c++) if(S[c+1]>L[c]) return -1;
  if(basis) *basis=B;
  return S[0]; }
// minimal certified M over a scan of the target weight
static ll cover_lattice_best(int k, const std::vector<ll>& v, const std::vector<ll>& L){
  double vol=1; for(int c=0;c<k;c++) vol*=(double)L[c]/P; double M0=1.0/vol; ll best=-1;
  for(double r=1.0;r<=64;r*=1.25){ ll m=cover_lattice(k,v,L,M0*r); if(m>0 && (best<0||m<best)) best=m; }
  return best; }

// ---------------- covering: exact minimal M in ONE pass (sliding window over the hit set) ----------------
// Outer coordinate o0 (smallest arc). Box j is active in the slab x = -t v_0 iff (j - t) lies in the p-periodic hit set
// J0 = { i : i v_0 mod p < L_0 }; by translation invariance the slab is covered iff the boxes {-i v' : i in J0 cap [s, s+M)}
// cover the (k-1)-torus (s = -t). Hence M* = max over consecutive hits h_prev < h of (e(h) - h_prev), e(h) = least e with
// J0 cap [h, e] covering; e(h) is nondecreasing in h -> two pointers.  Returns M* (<= cap) or -1.  (PROOF of the
// reduction of the research notes; validated against cover_min and brute force.)
static ll cover_min_fast(int k, const std::vector<ll>& v, const std::vector<ll>& L, ll cap){
  int o=0; for(int c=1;c<k;c++) if(L[c]<L[o]) o=c;
  if(L[o]>=P){ // every box active everywhere: reduce dimension
    if(k==1) return 1; std::vector<ll> v2,L2; for(int c=0;c<k;c++) if(c!=o){ v2.push_back(v[c]); L2.push_back(L[c]); } return cover_min_fast(k-1,v2,L2,cap); }
  ll v0=md(v[o]); if(v0==0) return -1;
  if(k==1){ // hits only: M* = max gap between consecutive hits (cyclic) -- the first coordinate alone
    std::vector<ll> hs; for(ll i=0;i<P;i++) if(mulm(i,v0)<L[o]) hs.push_back(i); ll g=0; for(size_t q=0;q<hs.size();q++){ ll nx= q+1<hs.size()? hs[q+1] : hs[0]+P; g=std::max(g,nx-hs[q]); } return g<=cap? g : -1; }
  std::vector<int> rest; for(int c=0;c<k;c++) if(c!=o) rest.push_back(c);
  std::sort(rest.begin(),rest.end(),[&](int a,int b){ return L[a]<L[b]; });
  ll Ls[6]; for(int i=0;i<k-1;i++) Ls[i]=std::min(L[rest[i]],P);
  // hits in [0, P + cap]
  std::vector<ll> hs; { ll y=0; for(ll i=0;i<=P+cap;i++){ if(y<L[o]) hs.push_back(i); y+=v0; if(y>=P) y-=P; } }
  size_t nh0=0; while(nh0<hs.size() && hs[nh0]<P) nh0++; if(nh0==0) return -1;
  std::vector<ll> cor; cor.reserve((size_t)(P+cap)*(k-1)/1); // corners of hit i: -i v'
  auto corner=[&](ll i, std::vector<ll>& T){ for(int c:rest) T.push_back(mulm(md(-i),md(v[c]))); };
  std::vector<ll> T; ll Mstar=0; size_t e=0; // window = hits[q..e)
  for(size_t q=0;q<nh0;q++){
    if(e<q) e=q;
    while(true){ T.clear(); for(size_t z=q;z<e;z++) corner(hs[z],T);
      bool ok = e>q && cover_rec(k-1,T,Ls);
      if(ok) break;
      if(e>=hs.size()) return -1; e++; if(hs[e-1]-hs[q]+1>cap) return -1; }
    ll hprev = q>0? hs[q-1] : hs[nh0-1]-P; // previous hit (periodic)
    Mstar=std::max(Mstar, hs[e-1]-hprev); if(Mstar>cap) return -1; }
  return Mstar; }
