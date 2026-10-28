// indep_range.cpp -- audit: independent per-prime check of the explicit s=3 brick-star rules A/B.
// Does NOT use the n-table of Lemma R: kappa is computed in F_p from places, gauges g_c(0), theta = th0*T
// via prop:LI(c); all residues are classified from their F_p values. Checks per prime:
//  (i) -kappa in its cross arc (Prop CW_s (i)); Lemma WS numbers (own code; compressed columns doubled, Lemma D);
//  Lemma W side conditions (D),(N) as needed by its proof; Lemma W value; and the EXACT window certificate
//  (lem:cert j=1 over the product windows, closed-form f_1 minima over integer intervals), independent of Lemma W.
// usage: indep_range A|B pmin pmax pthr
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <vector>
#include <algorithm>
typedef long long ll; typedef __int128 LL;
static ll md(ll a, ll p){ a%=p; return a<0?a+p:a; }
static ll pw(ll a, ll e, ll p){ ll r=1; a=md(a,p); while(e){ if(e&1) r=(LL)r*a%p; a=(LL)a*a%p; e>>=1;} return r; }
static ll iv(ll a, ll p){ return pw(md(a,p),p-2,p); }
static ll fr(ll n, ll d, ll p){ return (LL)md(n,p)*iv(d,p)%p; }
static ll cen(ll x, ll p){ x=md(x,p); return x>p/2? x-p : x; }
static ll cdiv(ll a, ll b){ return a>=0? (a+b-1)/b : -((-a)/b); }
// p*min f_1(e, sigma) over residues of the integer interval [lo,hi]
static ll minf1(int e, ll lo, ll hi, ll p){
  if(e==-1){ ll t=lo; lo=-hi; hi=-t; e=1; }
  ll len=hi-lo+1; if(len>=p) return 0; ll a=md(lo,p);
  if(e==1){ if(md(1-a,p)<len) return 0; return a==0? p-1 : a-1; }
  if(md(-a,p)<len) return 0;
  ll b=a+len-1; ll ga=std::min(a,p-a)-1, gb=std::min(b,p-b)-1; ll g=std::min(ga,gb); return g<0?0:g;
}
static ll wsN(std::vector<ll> nu, std::vector<ll> L, ll p){
  std::vector<int> o(nu.size()); for(size_t i=0;i<o.size();i++) o[i]=i;
  std::stable_sort(o.begin(),o.end(),[&](int x,int y){ return nu[x]>nu[y]; });
  ll n1=nu[o[0]], l1=L[o[0]]; if(n1<1 || n1>l1 || l1>p) return -1;
  ll N=1+cdiv(p-l1,n1);
  for(size_t t=1;t<o.size();t++){ ll nt=nu[o[t]]; if(nt<1 || (LL)N*nt>L[o[t]]) return -1; N=N-1+cdiv(p,nt); }
  return N;
}
int main(int argc, char** argv){
  if(argc<5){ fprintf(stderr,"usage\n"); return 1; }
  bool A = argv[1][0]=='A'; ll pmin=atoll(argv[2]), pmax=atoll(argv[3]), pthr=atoll(argv[4]);
  // design data (the rule of Theorem thm:A3), as rationals num/den
  ll an[3], ad[3], gn[3], gd[3], th0, un, ud, wbn,wbd, wcn,wcd, wxn,wxd; int b;
  if(A){ ll a_[3]={0,1,-5}; for(int i=0;i<3;i++){an[i]=a_[i];ad[i]=1;} gn[0]=24;gd[0]=5; gn[1]=1;gd[1]=1; gn[2]=-2;gd[2]=5;
    th0=900; un=11; ud=400000; b=1; wbn=1;wbd=50; wcn=7;wcd=200; wxn=1;wxd=10; }
  else { ll a_[3]={0,1,2}; for(int i=0;i<3;i++){an[i]=a_[i];ad[i]=1;} gn[0]=1;gd[0]=1; gn[1]=-56;gd[1]=1; gn[2]=6;gd[2]=1;
    th0=84; un=891; ud=78400000; b=0; wbn=27;wbd=1000; wcn=1;wcd=200; wxn=1;wxd=10; }
  std::vector<char> comp(pmax+1,0); for(ll i=2;i*i<=pmax;i++) if(!comp[i]) for(ll j=i*i;j<=pmax;j+=i) comp[j]=1;
  ll cnt=0,nfail=0,firstfail=-1,lastfail=-1; double minW=9,minX=9; ll argW=-1,argX=-1; double maxloss=0; ll argloss=-1;
  LL minW2num=-1; ll minW2p=0; ll cntWltX=0; ll cnt_brickbind=0;
  int C[2]; { int k=0; for(int c=0;c<3;c++) if(c!=b) C[k++]=c; }
  for(ll p=std::max(pmin,(ll)7); p<=pmax; p++){ if(comp[p]) continue; cnt++;
    ll T=(ll)((LL)un*p/ud); if(T%2==0) T--; bool ok = T>=1;
    ll Bbc=(ll)((LL)wbn*p/wbd), Bcc=(ll)((LL)wcn*p/wcd), Bcb=(ll)((LL)wxn*p/wxd), h=(p+1)/2;
    ll K[3][3]={{0}}; ll a[3], g[3];
    for(int c=0;c<3;c++){ a[c]=fr(an[c],ad[c],p); g[c]=fr(gn[c],gd[c],p); }
    ll theta=(LL)th0*T%p;
    for(int c=0;c<3;c++) for(int d=0;d<3;d++) if(c!=d){ ll wd=1; for(int e=0;e<3;e++) if(e!=d) wd=(LL)wd*md(a[d]-a[e],p)%p;
      ll den=(LL)g[d]*wd%p*md(a[d]-a[c],p)%p; K[c][d]=(LL)theta*g[c]%p*iv(den,p)%p; }
    // windows: centre/half-width of cross (c<-d)
    ll ctr[3][3], hw[3][3];
    for(int c=0;c<3;c++) for(int d=0;d<3;d++) if(c!=d){
      if(d==b){ ctr[c][d]=0; hw[c][d]=Bbc; } else if(c==b){ ctr[c][d]=h; hw[c][d]=Bcb; } else { ctr[c][d]=0; hw[c][d]=Bcc; } }
    // (i): -kappa in arc
    if(ok) for(int c=0;c<3;c++) for(int d=0;d<3;d++) if(c!=d){ ll x=cen(-K[c][d]-ctr[c][d],p); if(llabs(x)>hw[c][d]) ok=false; }
    ll Mb=-1, M[3]={0,0,0};
    if(ok){ std::vector<ll> nu,L; for(int j:C){ nu.push_back(llabs(cen(K[j][b],p))); L.push_back(2*Bbc+1);} Mb=wsN(nu,L,p); if(Mb<0) ok=false; }
    if(ok) for(int i:C){ std::vector<ll> nu,L; for(int c=0;c<3;c++) if(c!=i){ nu.push_back(llabs(cen(2*K[c][i],p))); L.push_back(2*hw[c][i]+1);}
      ll N=wsN(nu,L,p); if(N<0){ ok=false; break; } M[i]=2*N-1; }
    if(!ok){ nfail++; if(firstfail<0) firstfail=p; lastfail=p; continue; }
    ll Mx=std::max(M[C[0]],M[C[1]]); ll Aoff=Bcc+Bbc;
    // Lemma W proof needs: A+M-1+Bcc+Bbc <= p-1 and (p-1)/2-Bcb-Mb >= 1, (p+1)/2+Bcb <= p-1
    bool okW = (Aoff+Mx-1+Bcc+Bbc<=p-1) && ((p-1)/2-Bcb-Mb>=1) && ((p+1)/2+Bcb<=p-1);
    ll b1=p-Mb, b2=p-Aoff-Mx-Bbc, b3=p-1-2*Bcb-2*Mb, b4=p-Aoff-Mx-Bcc-Bbc;
    LL W2 = std::min((LL)4*b1*b1, std::min((LL)4*b2*b2+(LL)b3*b3, (LL)8*b4*b4)); // = 4p^2 LB_W^2
    if(!okW || b2<0||b3<0||b4<0 || W2<=0){ nfail++; if(firstfail<0) firstfail=p; lastfail=p; continue; }
    // exact window certificate
    ll lo[3][3], hi[3][3];
    for(int d=0;d<3;d++){ if(d==b){ lo[d][d]=-(Mb-1); hi[d][d]=0; } else { lo[d][d]=-(Aoff+M[d]-1); hi[d][d]=-Aoff; }
      for(int c=0;c<3;c++) if(c!=d){ lo[c][d]=ctr[c][d]-hw[c][d]; hi[c][d]=ctr[c][d]+hw[c][d]; } }
    LL X2=-1;
    for(int e0=-1;e0<=1;e0++) for(int e1=-1;e1<=1;e1++) for(int e2=-1;e2<=1;e2++){
      int e[3]={e0,e1,e2}; if(!e0&&!e1&&!e2) continue; int f=e0?e0:(e1?e1:e2); if(f<0) continue;
      LL tot=0; for(int c=0;c<3;c++){ ll L_=0,H_=0; for(int d=0;d<3;d++) if(e[d]){ if(e[d]>0){L_+=lo[c][d];H_+=hi[c][d];} else {L_-=hi[c][d];H_-=lo[c][d];} }
        ll m=minf1(e[c],L_,H_,p); tot+=(LL)m*m; }
      if(X2<0||tot<X2) X2=tot; }
    double LBW=sqrt((double)W2)/(2.0*p), LBX=sqrt((double)X2)/p;
    if((double)W2 > 4.0*(double)X2*(1+1e-12)) cntWltX++;  // Lemma W must not exceed the exact value
    if(LBW<minW){ minW=LBW; argW=p; minW2num=W2; minW2p=p; }
    if(LBX<minX){ minX=LBX; argX=p; }
    if(b1*b1*4==W2) cnt_brickbind++;
    if(p>=pthr){ double loss=(1-LBW)*p; if(loss>maxloss){ maxloss=loss; argloss=p; } }
  }
  // exact test of min LB_W >= 0.6437: 4p^2 LB^2 >= 4 p^2 0.6437^2  <=> W2*10^8 >= 4 p^2 * 6437^2
  bool ge6437 = minW2num>=0 && (LL)minW2num*100000000 >= (LL)4*minW2p*minW2p*6437*6437;
  printf("rule %s primes=%lld fails=%lld first_fail=%lld last_fail=%lld | min LB_W=%.7f at %lld (>=0.6437 exactly: %s) | min exact-window LB=%.7f at %lld | LemmaW>exact count=%lld | brick-axis binding count=%lld | max (1-LB_W)p for p>=%lld: %.3f at %lld\n",
    A?"A":"B",cnt,nfail,firstfail,lastfail,minW,argW,ge6437?"yes":"no",minX,argX,cntWltX,cnt_brickbind,pthr,maxloss,argloss);
}
