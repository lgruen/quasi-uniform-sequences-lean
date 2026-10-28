// audit_fq.cpp -- INDEPENDENT audit of Proposition prop:primepower: the residue design over F_Q, Q = p^r (own field code).
// enc: element sum c_i b^i (b root of the given monic irreducible f) <-> code sum c_i p^i  (power basis).
// usage:
//   fq p r f0,f1,..,f_{r-1}(monic, low->high; "all" = every monic irreducible) s beta
//        -> exhaustive max over k in (F_Q^*)^{s-1} of beta_Q(k) (lem:cert j=1, coordinate * only, carry rule
//           rem:F4carry: a step changes the finest digit by any Delta in D_r = {Delta(y)}).
//   fq p r f s sep Nmax k1,k2,... -> residue design (places codes 0..s-1 shifted if needed, star = s-1, theta=1)
//           with weights k (codes); frozen identity on points; t=0 cell occupancy at full levels; exact torus
//           delta(P_[N]) for every N <= Nmax; sep at full levels vs beta_Q(k).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <vector>
#include <string>
#include <algorithm>
#include <cstdint>
#include <array>
using namespace std; typedef long long ll;
int p,r,Q; vector<int> f; vector<vector<int>> ADD, MUL; vector<int> NEG, INV;
static vector<int> dec(int x){ vector<int> d(r); for(int i=0;i<r;i++){ d[i]=x%p; x/=p; } return d; }
static int encv(const vector<int>&d){ int x=0; for(int i=r-1;i>=0;i--) x=x*p+d[i]; return x; }
static bool irreducible(const vector<int>& g){ // monic degree r over F_p: no factor of degree 1..r/2 (trial division)
  auto rem=[&](vector<int> a,const vector<int>& b){ while(a.size()>=b.size()){ int c=a.back(); if(c){ int sh=a.size()-b.size(); for(size_t i=0;i<b.size();i++) a[sh+i]=((a[sh+i]-c*b[i])%p+p)%p; } a.pop_back(); } return a; };
  vector<int> G=g; G.push_back(1);
  for(int d=1;d<=r/2;d++){ int tot=1; for(int i=0;i<d;i++) tot*=p; for(int u=0;u<tot;u++){ vector<int> h(d+1); int x=u; for(int i=0;i<d;i++){ h[i]=x%p; x/=p; } h[d]=1; auto rr=rem(G,h); bool z=true; for(int c:rr) if(c) z=false; if(z) return false; } }
  return true; }
static void buildField(){ Q=1; for(int i=0;i<r;i++) Q*=p; ADD.assign(Q,vector<int>(Q)); MUL.assign(Q,vector<int>(Q)); NEG.assign(Q,0); INV.assign(Q,0);
  for(int x=0;x<Q;x++){ auto a=dec(x); for(int y=0;y<Q;y++){ auto b=dec(y); vector<int> s(r); for(int i=0;i<r;i++) s[i]=(a[i]+b[i])%p; ADD[x][y]=encv(s);
      vector<int> pr(2*r,0); for(int i=0;i<r;i++) for(int j=0;j<r;j++) pr[i+j]=(pr[i+j]+a[i]*b[j])%p;
      for(int d=2*r-1;d>=r;d--){ int c=pr[d]; if(!c) continue; pr[d]=0; for(int i=0;i<r;i++) pr[d-r+i]=((pr[d-r+i]-c*f[i])%p+p)%p; } // b^r = -sum f_i b^i
      pr.resize(r); MUL[x][y]=encv(pr); } }
  for(int x=0;x<Q;x++){ for(int y=0;y<Q;y++){ if(ADD[x][y]==0) NEG[x]=y; if(MUL[x][y]==1) INV[x]=y; } }
  // sanity: field axioms spot check
  for(int x=1;x<Q;x++) if(MUL[x][INV[x]]!=1){ fprintf(stderr,"not a field\n"); exit(2);} }
static inline int ad(int a,int b){ return ADD[a][b]; } static inline int mu(int a,int b){ return MUL[a][b]; } static inline int sb(int a,int b){ return ADD[a][NEG[b]]; }
vector<array<double,3>> F1; vector<int> DR; // F1[sigma][e+1]

static void buildF1(){ F1.assign(Q,{0,0,0}); for(int sg=0;sg<Q;sg++) for(int e=-1;e<=1;e++){ int mn=1<<30; for(int R=0;R<Q;R++){ int v=abs(e*Q+ADD[R][sg]-R); mn=min(mn,v); } F1[sg][e+1]=max(0,mn-1)/(double)Q; }
  vector<int> seen(Q,0); DR.clear(); for(int y=0;y<Q;y++){ int d=sb((y+1)%Q,y); if(!seen[d]){ seen[d]=1; DR.push_back(d);} } }
static double betaQ(const vector<int>& k){ int n=k.size(); double best=1e9; int tot=1; for(int i=0;i<n;i++) tot*=3;
  for(int t=0;t<tot;t++){ vector<int> e(n); int x=t; for(int i=0;i<n;i++){ e[i]=x%3-1; x/=3; }
    // enumerate Delta choices for moving coords
    vector<int> mv; for(int i=0;i<n;i++) if(e[i]) mv.push_back(i);
    int nd=1; for(size_t i=0;i<mv.size();i++) nd*=DR.size();
    for(int u=0;u<nd;u++){ int y=u; int sg=0; for(int i:mv){ int dd=DR[y%DR.size()]; y/=DR.size(); int term=mu(k[i],dd); sg= e[i]>0? ad(sg,term): sb(sg,term); }
      for(int es=-1;es<=1;es++){ if(t==(tot-1)/2 && es==0) continue; // e = 0 entirely
        double v=F1[sg][es+1]; if(v<best) best=v; } } }
  return best; }
int main(int argc,char**argv){ p=atoi(argv[1]); r=atoi(argv[2]); string fs=argv[3]; int s=atoi(argv[4]); string mode=argv[5];
  vector<vector<int>> polys;
  if(fs=="all"){ int tot=1; for(int i=0;i<r;i++) tot*=p; for(int u=0;u<tot;u++){ vector<int> g(r); int x=u; for(int i=0;i<r;i++){ g[i]=x%p; x/=p; } if(g[0]==0) continue; if(irreducible(g)) polys.push_back(g); } }
  else { vector<int> g; size_t i=0; while(i<fs.size()){ size_t j=fs.find(',',i); if(j==string::npos) j=fs.size(); g.push_back(atoi(fs.substr(i,j-i).c_str())); i=j+1; } if(!irreducible(g)){ fprintf(stderr,"not irreducible\n"); return 1;} polys.push_back(g); }
  if(mode=="beta"){
    for(auto&g:polys){ f=g; buildField(); buildF1(); int n=s-1; vector<int> k(n,1); double best=-1; vector<int> bk;
      while(true){ double v=betaQ(k); if(v>best+1e-12){ best=v; bk=k; } int i=0; while(i<n && k[i]==Q-1){ k[i]=1; i++; } if(i==n) break; k[i]++; }
      printf("Q=%d f=(",Q); for(int c:g) printf("%d ",c); printf("1) s=%d |D_r|=%zu max beta_Q = %.6f = %g/%d  at k=(",s,DR.size(),best,best*Q,Q); for(int c:bk) printf("%d ",c); printf(")\n"); }
    return 0; }
  if(mode=="sep"){ f=polys[0]; buildField(); buildF1(); ll Nmax=atoll(argv[6]); vector<int> kw; { string ks=argv[7]; size_t i=0; while(i<ks.size()){ size_t j=ks.find(',',i); if(j==string::npos) j=ks.size(); kw.push_back(atoi(ks.substr(i,j-i).c_str())); i=j+1; } }
    int star=s-1; vector<int> a(s); for(int c=0;c<s;c++) a[c]=c; // codes 0..s-1 (distinct elements)
    double beta=betaQ(kw); int m=0; { ll t=1; while(t<Nmax){ t*=Q; m++; } }
    int D=1; { double t=1; while(t<pow(2.0,56)){ t*=Q; D++; } } D=max(D,m+2);
    // series ops over F_Q, length D
    auto smul=[&](const vector<int>&x,const vector<int>&y){ vector<int> z(D,0); for(int i=0;i<D;i++) if(x[i]) for(int j=0;i+j<D;j++) if(y[j]) z[i+j]=ad(z[i+j],mu(x[i],y[j])); return z; };
    auto sinv=[&](const vector<int>&x){ vector<int> z(D,0); int i0=INV[x[0]]; z[0]=i0; for(int n=1;n<D;n++){ int t=0; for(int j=1;j<=n;j++) t=ad(t,mu(x[j],z[n-j])); z[n]=mu(NEG[t],i0); } return z; };
    vector<int> mu_c(s,0); for(int c=0;c<star;c++) mu_c[c]=NEG[INV[kw[c]]];
    vector<vector<vector<int>>> C(s, vector<vector<int>>(D, vector<int>(m+1,0)));
    for(int c=0;c<s;c++){ vector<int> W(D,0); W[0]=1; for(int b=0;b<s;b++) if(b!=c){ vector<int> t(D,0); t[0]=sb(a[c],a[b]); t[1]=1; W=smul(W,t); }
      vector<int> Wi=sinv(W); vector<int> cur(D,0); cur[0]=1; if(c!=star){ vector<int> t(D,0); t[0]=sb(a[c],a[star]); t[1]=1; cur=smul(sinv(t),Wi); }
      for(int n=0;n<D;n++){ // C[n][k] = mu_c [t^n] (t+a_c)^k * cur   (theta = 1)
        vector<int> pk(D,0); pk[0]=1; vector<int> lin(D,0); lin[0]=a[c]; lin[1]=1;
        for(int k=0;k<=m;k++){ int t=0; for(int j=0;j<=n;j++) t=ad(t,mu(pk[j],cur[n-j])); C[c][n][k]= (c!=star)? mu(mu_c[c],t): t; pk=smul(pk,lin); }
        cur=smul(cur,Wi); } }
    // frozen identity at matrix level for K < D-1 (columns < sK <= m)
    long mf=0; for(int K=1;K<D-1 && s*K<=m;K++) for(int j=0;j<s*K;j++){ int t=0; for(int c=0;c<star;c++) t=ad(t,mu(kw[c],C[c][K-1][j])); if(t!=C[star][K][j]) mf++; }
    printf("Q=%d s=%d k=(",Q,s); for(int x:kw) printf("%d ",x); printf(") beta_Q(k)=%.6f  matrix frozen-identity fails=%ld (D=%d m=%d)\n",beta,mf,D,m);
    // points
    vector<double> X((size_t)Nmax*s); vector<int> dig(s*D,0), vd(m+1,0); vector<double> pp(D);
    vector<ll> lv; { ll t=1; while(true){ ll t2=t; bool ok=true; for(int i=0;i<s;i++){ if(t2>Nmax/Q+1){ ok=false; break;} t2*=Q; } if(!ok||t2>Nmax) break; t=t2; lv.push_back(t); } }
    long ff=0, fc=0; int KL=lv.size(); vector<uint32_t> cellcode((size_t)Nmax*s*(KL>0?KL:1),0);
    for(ll v=0;v<Nmax;v++){
      for(int c=0;c<s;c++){ double x=0; for(int n=D-1;n>=0;n--) x=(x+dig[c*D+n])/Q; X[(size_t)v*s+c]=x; }
      for(int K=1;K<=KL;K++) if(v<lv[K-1]) for(int c=0;c<s;c++){ uint32_t cc=0; for(int n=0;n<K;n++) cc=cc*Q+dig[c*D+n]; cellcode[((size_t)v*s+c)*KL+K-1]=cc; }
      for(size_t K=1;K<=lv.size()+1 && (int)K<D;K++){ ll NK= (K<=lv.size())? lv[K-1] : lv.empty()? 1: lv.back()*(ll)pow(Q,s); if(v>=NK) continue; int t=0; for(int c=0;c<star;c++) t=ad(t,mu(kw[c],dig[c*D+K-1])); fc++; if(t!=dig[star*D+K]) ff++; }
      // increment index digits (base-Q code), field change Delta at each changed digit
      int l=0; while(true){ if(l>m) break; int old=vd[l]; int nw=(old+1)%Q; int dl=sb(nw,old); vd[l]=nw; for(int c=0;c<s;c++) for(int n=0;n<D;n++) if(C[c][n][l]) dig[c*D+n]=ad(dig[c*D+n],mu(dl,C[c][n][l])); if(nw!=0) break; l++; }
    }
    printf("frozen identity on points: checks=%ld fails=%ld\n",fc,ff);
    // t=0 at full levels: cell occupancy
    for(size_t K=1;K<=lv.size();K++){ ll G=1; for(size_t i=0;i<K;i++) G*=Q; vector<char> occ(lv[K-1],0); long dup=0; for(ll v=0;v<lv[K-1];v++){ ll id=0; for(int c=0;c<s;c++){ ll q=cellcode[((size_t)v*s+c)*KL+K-1]; id=id*G+q; } if(occ[id]) dup++; occ[id]=1; } printf("level K=%zu: cells with 2 points=%ld\n",K,dup); }
    // incremental delta for all N (static grid)
    ll G=(ll)floor(pow((double)Nmax,1.0/s)+1e-9); if(G<1) G=1; ll ncell=1; for(int i=0;i<s;i++) ncell*=G;
    vector<uint32_t> start(ncell+1,0), ord(Nmax); vector<ll> cid(Nmax);
    for(ll v=0;v<Nmax;v++){ ll id=0; for(int c=0;c<s;c++){ ll q=(ll)(X[(size_t)v*s+c]*G); if(q>=G) q=G-1; id=id*G+q; } cid[v]=id; start[id+1]++; }
    for(ll i=0;i<ncell;i++) start[i+1]+=start[i]; { vector<uint32_t> pos(start.begin(),start.end()-1); for(ll v=0;v<Nmax;v++) ord[pos[cid[v]]++]=v; }
    auto dist2=[&](ll u,ll v){ double d2=0; for(int c=0;c<s;c++){ double d=fabs(X[(size_t)u*s+c]-X[(size_t)v*s+c]); if(d>0.5) d=1-d; d2+=d*d; } return d2; };
    double dc2=1e30, minsep=1e30; ll argN=0; vector<double> atLv(lv.size()+1,0);
    for(ll u=1;u<Nmax;u++){ double dc=sqrt(dc2); ll R=(dc>1)?G:(ll)ceil(dc*G); double cand=dc2; bool brute=(2*R+1>=G)||pow(2.0*R+1,s)>=(double)u;
      if(brute){ for(ll v=0;v<u;v++){ double d=dist2(u,v); if(d<cand) cand=d; } }
      else { vector<ll> cc(s); ll id=cid[u]; for(int c=s-1;c>=0;c--){ cc[c]=id%G; id/=G; } ll tot=1; for(int i=0;i<s;i++) tot*=(2*R+1);
        for(ll o=0;o<tot;o++){ ll t=o,nid=0; for(int c=0;c<s;c++){ ll dl=t%(2*R+1)-R; t/=(2*R+1); nid=nid*G+(((cc[c]+dl)%G+G)%G); } for(uint32_t ii=start[nid];ii<start[nid+1];ii++){ ll v=ord[ii]; if(v>=u) break; double d=dist2(u,v); if(d<cand) cand=d; } } }
      if(cand<dc2){ dc2=cand; double sp=sqrt(dc2)*pow((double)(u+1),1.0/s); if(sp<minsep){ minsep=sp; argN=u+1; } }
      for(size_t K=1;K<=lv.size();K++) if(u+1==lv[K-1]) atLv[K]=sqrt(dc2); }
    for(size_t K=1;K<=lv.size();K++){ double sp=atLv[K]*pow((double)Q,K); printf("  level K=%zu N=%lld: sep=%.6f  %s\n",K,lv[K-1],sp, sp+1e-12>=min(1.0,beta)?"OK":"*** VIOLATION ***"); }
    int Kf=lv.size(); printf("  min_N sep(P_[N]) = %.6f at N=%lld ; delta(P_[Nmax])*Q^{K+1}=%.6f (>= beta? %s)\n",minsep,argN,sqrt(dc2)*pow((double)Q,Kf+1), sqrt(dc2)*pow((double)Q,Kf+1)+1e-12>=beta?"OK":"VIOLATION");
    return 0; }
  return 1; }
