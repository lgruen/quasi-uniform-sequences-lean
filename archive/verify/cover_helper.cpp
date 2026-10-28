// cover_helper.cpp -- exact line-covering oracle for the archive verifier (verify_designs.py).
// Question (Prop CW_s (ii), reduced as in Lemma WS): given p, an own run length M and d narrow cross coordinates with
// residues k_r and arc lengths L_r (1 <= L_r < p), is it true that for EVERY sigma in Z_p^d some o in {0,..,M-1} has
// sigma_r + o*k_r in [0, L_r) (mod p) for all r?  (Translation invariance: only M, k_r, L_r matter.)
// Methods: d = 1 direct (max cyclic gap of the arc starts); d = 2 event sweep over sigma_1 with a multiset of active
// sigma_2-arc starts and a counter of cyclic gaps > L_2 (exact); d >= 3 recursive brute force over sigma_1..sigma_{d-1}
// with candidate filtering, last coordinate by the gap test (exact).  Brute force for d = 2 too when p <= 400
// (cross-check of the sweep; a disagreement aborts).
// stdin: one query per line "p d M k_1 L_1 ... k_d L_d";  stdout: one line per query "1" (covers) or "0".
#include <cstdio>
#include <vector>
#include <set>
#include <algorithm>
typedef long long ll;
static ll P;
static ll md(ll a){ a%=P; return a<0? a+P : a; }
static bool gaps_ok(std::vector<ll> st, ll L){ // arcs [st_i, st_i+L) cover Z_p ?
  if(st.empty()) return false; std::sort(st.begin(),st.end()); st.erase(std::unique(st.begin(),st.end()),st.end());
  ll mg=st[0]+P-st.back(); for(size_t i=0;i+1<st.size();i++) mg=std::max(mg,st[i+1]-st[i]); return mg<=L; }
static bool cover1(ll M,ll k,ll L){ std::vector<ll> st; for(ll o=0;o<M;o++) st.push_back(md(-o*k)); return gaps_ok(st,L); }
static bool sweep2(ll M,ll k1,ll L1,ll k2,ll L2){
  std::vector<ll> A(M),B(M); for(ll o=0;o<M;o++){ A[o]=md(-o*k1); B[o]=md(-o*k2); }
  std::vector<std::vector<ll>> ins(P),rem(P);
  for(ll o=0;o<M;o++){ ins[A[o]].push_back(o); rem[(A[o]+L1)%P].push_back(o); }
  std::multiset<ll> S; ll bad=0;
  auto gap=[&](ll a,ll b)->ll{ ll g=md(b-a); return g==0? P : g; };
  auto nbrs=[&](std::multiset<ll>::iterator it, ll& pv, ll& nx){ auto n=std::next(it); nx= n==S.end()? *S.begin() : *n; pv= it==S.begin()? *S.rbegin() : *std::prev(it); };
  auto add=[&](ll b){ if(S.empty()){ S.insert(b); bad=(P>L2); return; }
    auto it=S.insert(b); ll pv,nx; nbrs(it,pv,nx);
    if(S.size()==2){ bad=(gap(pv,b)>L2)+(gap(b,nx)>L2); return; }
    bad-= (gap(pv,nx)>L2); bad+= (gap(pv,b)>L2)+(gap(b,nx)>L2); };
  auto del=[&](ll b){ auto it=S.find(b); if(S.size()==1){ S.erase(it); bad=0; return; }
    ll pv,nx; nbrs(it,pv,nx); bad-= (gap(pv,b)>L2)+(gap(b,nx)>L2); S.erase(it);
    if(S.size()==1){ bad=(P>L2); return; } bad+= (gap(pv,nx)>L2); };
  for(ll o=0;o<M;o++) if(md(0-A[o])<L1) add(B[o]);
  if(S.empty()||bad) return false;
  for(ll g=1;g<P;g++){ for(ll o:rem[g]) del(B[o]); for(ll o:ins[g]) add(B[o]); if(S.empty()||bad) return false; }
  return true; }
static int D; static std::vector<ll> K,L; static std::vector<std::vector<ll>> SH;
static bool rec(int r,const std::vector<ll>& cand){
  if(r==D-1){ std::vector<ll> st; st.reserve(cand.size()); for(ll i:cand) st.push_back(md(-SH[r][i])); return gaps_ok(st,L[r]); }
  std::vector<ll> nc; nc.reserve(cand.size());
  for(ll y=0;y<P;y++){ nc.clear(); for(ll i:cand) if(md(y+SH[r][i])<L[r]) nc.push_back(i); if(nc.empty()) return false; if(!rec(r+1,nc)) return false; }
  return true; }
static bool brute(ll M){ SH.assign(D,std::vector<ll>(M)); for(int r=0;r<D;r++) for(ll o=0;o<M;o++) SH[r][o]=md(o*K[r]);
  std::vector<ll> all(M); for(ll o=0;o<M;o++) all[o]=o; return rec(0,all); }
int main(){
  ll p; while(scanf("%lld",&p)==1){ P=p; ll M; scanf("%d %lld",&D,&M); K.assign(D,0); L.assign(D,0);
    for(int r=0;r<D;r++){ scanf("%lld %lld",&K[r],&L[r]); K[r]=md(K[r]); }
    bool ok;
    if(M<=0) ok=false; else if(D==0) ok=true; else if(D==1) ok=cover1(M,K[0],L[0]);
    else if(D==2){ ok=sweep2(M,K[0],L[0],K[1],L[1]); if(P<=400){ bool b=brute(M); if(b!=ok){ printf("DISAGREE\n"); fflush(stdout); return 3; } } }
    else ok=brute(M);
    printf("%d\n",ok?1:0); fflush(stdout); }
  return 0; }
