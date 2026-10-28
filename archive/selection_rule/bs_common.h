// bs_common.h -- shared helpers for the brick-star build: F_p arithmetic, the one-digit certificate
// f_1 (paper rem:onedigit), exact line covering (prop:cover3 (ii) for a product window), window certificate (lem:cert j=1).
#pragma once
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <vector>
#include <set>
#include <algorithm>
#include <string>
typedef long long ll;
static ll P;
static inline ll md(ll a){ a%=P; if(a<0) a+=P; return a; }
static inline ll pw(ll a,ll e){ ll r=1; a=md(a); while(e){ if(e&1) r=r*a%P; a=a*a%P; e>>=1; } return r; }
static inline ll inv(ll a){ return pw(a,P-2); }
static inline ll cen(ll a){ a=md(a); return a>P/2? a-P: a; }
// f_1(e, sigma) of rem:onedigit, in cell units (prime p, one geometric digit)
static inline double f1(int e, ll sg){
  ll r=md(sg);
  if(e==0){ ll c=std::min(r,P-r); return c>0? (double)(c-1)/P : 0.0; }
  if(e<0) r=md(-sg);
  return r==0? (double)(P-1)/P : (double)(r-1)/P;
}
// residue set as bitmap
typedef std::vector<char> RSet;
static RSet interval_set(ll lo, ll hi){ RSet s(P,0); for(ll x=lo;x<=hi;x++) s[md(x)]=1; return s; }
static RSet sumset(const RSet&a, const RSet&b){ RSet c(P,0); std::vector<ll> ai; for(ll i=0;i<P;i++) if(a[i]) ai.push_back(i);
  std::vector<ll> bi; for(ll i=0;i<P;i++) if(b[i]) bi.push_back(i);
  if((ll)ai.size()*(ll)bi.size() > 50LL*P){ // dense: use word trick via repeated rotation
    for(ll x:ai) for(ll y:bi) c[(x+y)%P]=1; } else for(ll x:ai) for(ll y:bi) c[(x+y)%P]=1;
  return c; }
static RSet negset(const RSet&a){ RSet b(P,0); for(ll i=0;i<P;i++) if(a[i]) b[md(-i)]=1; return b; }
// Decoupled window certificate (lem:cert, j=1): S[c][cp] = set of responses of column cp in coordinate c (own c==cp).
// Returns LB (uncapped) and worst step.
static double window_LB(const RSet S[3][3], int*worst=nullptr){
  double best=1e9;
  for(int e0=-1;e0<=1;e0++)for(int e1=-1;e1<=1;e1++)for(int e2=-1;e2<=1;e2++){
    int e[3]={e0,e1,e2}; if(!e0&&!e1&&!e2) continue; int f=e0?e0:(e1?e1:e2); if(f<0) continue;
    double tot=0;
    for(int c=0;c<3;c++){ RSet acc; bool init=false;
      for(int cp=0;cp<3;cp++){ if(!e[cp]) continue; RSet t = e[cp]>0? S[c][cp] : negset(S[c][cp]);
        if(!init){ acc=t; init=true; } else acc=sumset(acc,t); }
      double m=1e9; for(ll x=0;x<P;x++) if(acc[x]) m=std::min(m,f1(e[c],x)); tot+=m*m; }
    double v=sqrt(tot); if(v<best){ best=v; if(worst){ worst[0]=e0;worst[1]=e1;worst[2]=e2; } } }
  return best; }
// Exact line covering: does U_{o=0}^{M-1} (X - o*k) = F_p^2 with X=[-W1,W1]x[-W2,W2]?  Returns minimal M (<=cap) or -1.
// Method (independent of the bitmap covering check of the research programs): for each y1, the o with y1 - o k1 in [-W1,W1] are
// collected in increasing order; the arcs  -o k2 + [-W2,W2] must cover the circle Z/p. Minimal M(y1) = first o at which
// they do (tracked with a sorted set of arc centres and the count of gaps > 2W2+1). M = max_y1 M(y1).
static ll min_cover(ll k1, ll k2, ll W1, ll W2, ll cap){
  k1=md(k1); k2=md(k2); ll need=2*W2+1; if(need>=P){ /* coordinate 2 trivially covered */ }
  ll Mmax=0;
  std::vector<ll> run; // reused
  for(ll y1=0;y1<P;y1++){
    std::set<ll> cs; ll badgaps=0; bool covered=false; ll o;
    // gaps: number of consecutive centre pairs (cyclic) with distance > need; with one centre gap = P
    for(o=0;o<cap;o++){
      ll v=md(y1-o*k1); ll vc=v>P/2? v-P: v; if(vc<-W1||vc>W1) continue;
      ll c=md(-o*k2);
      if(need>=P){ covered=true; break; }
      if(cs.empty()){ cs.insert(c); badgaps=1; /* the single gap P > need */ }
      else if(!cs.count(c)){
        auto it=cs.lower_bound(c); ll nx = (it==cs.end())? *cs.begin()+P : *it; ll pv = (it==cs.begin())? *cs.rbegin()-P : *std::prev(it);
        if(cs.size()==1){ nx=*cs.begin(); pv=*cs.begin(); if(nx<c) nx+=P; if(pv>c) pv-=P; }
        ll old=nx-pv; if(old>need) badgaps--; if(c-pv>need) badgaps++; if(nx-c>need) badgaps++;
        cs.insert(c); }
      if(badgaps==0){ covered=true; break; } }
    if(!covered) return -1;
    Mmax=std::max(Mmax,o+1); if(Mmax>=cap) return -1; }
  return Mmax; }
// min_cover restricted to the rows y1 in ys (a LOWER bound for the exact minimal M if ys is a subset; exact if ys = all).
static ll min_cover_rows(ll k1, ll k2, ll W1, ll W2, ll cap, const std::vector<ll>& ys){
  k1=md(k1); k2=md(k2); ll need=2*W2+1; ll Mmax=0;
  for(ll y1:ys){ std::set<ll> cs; ll badgaps=0; bool covered=false; ll o;
    for(o=0;o<cap;o++){ ll v=md(y1-o*k1); ll vc=v>P/2? v-P: v; if(vc<-W1||vc>W1) continue;
      if(need>=P){ covered=true; break; } ll c=md(-o*k2);
      if(cs.empty()){ cs.insert(c); badgaps=1; }
      else if(!cs.count(c)){ auto it=cs.lower_bound(c); ll nx=(it==cs.end())? *cs.begin()+P : *it; ll pv=(it==cs.begin())? *cs.rbegin()-P : *std::prev(it);
        if(cs.size()==1){ nx=*cs.begin(); pv=*cs.begin(); if(nx<c) nx+=P; if(pv>c) pv-=P; }
        if(nx-pv>need) badgaps--; if(c-pv>need) badgaps++; if(nx-c>need) badgaps++; cs.insert(c); }
      if(badgaps==0){ covered=true; break; } }
    if(!covered) return -1; Mmax=std::max(Mmax,o+1); if(Mmax>=cap) return -1; }
  return Mmax; }
// f_1 minimum over an integer interval [lo,hi] (closed form)
static double f1min_int(int e, ll lo, ll hi){
  if(hi-lo+1>=P) return 0.0;
  if(e<0){ ll t=lo; lo=-hi; hi=-t; e=1; }
  if(e>0){ // fatal residue 1
    ll k=lo+md(1-lo); if(k<=hi) return 0.0; return f1(1,lo); }
  // e=0: zero if contains a residue in {-1,0,1}
  for(ll r=-1;r<=1;r++){ ll k=lo+md(r-lo); if(k<=hi) return 0.0; }
  return std::min(f1(0,lo),f1(0,hi)); }
struct IW { ll lo,hi; };
static double window_LB_int(const IW S[3][3], int*worst=nullptr){
  double best=1e9;
  for(int e0=-1;e0<=1;e0++)for(int e1=-1;e1<=1;e1++)for(int e2=-1;e2<=1;e2++){
    int e[3]={e0,e1,e2}; if(!e0&&!e1&&!e2) continue; int f=e0?e0:(e1?e1:e2); if(f<0) continue; double tot=0;
    for(int c=0;c<3;c++){ ll lo=0,hi=0; for(int cp=0;cp<3;cp++) if(e[cp]){ if(e[cp]>0){ lo+=S[c][cp].lo; hi+=S[c][cp].hi; } else { lo-=S[c][cp].hi; hi-=S[c][cp].lo; } }
      double m=f1min_int(e[c],lo,hi); tot+=m*m; }
    double v=sqrt(tot); if(v<best){ best=v; if(worst){worst[0]=e0;worst[1]=e1;worst[2]=e2;} } }
  return best; }
