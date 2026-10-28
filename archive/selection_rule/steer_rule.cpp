// steer_rule.cpp -- copy-and-extend of the research program steer_centre.cpp: DETERMINISTIC tie-broken
// steering rules among the ADMISSIBLE own values (Prop CW_s / prop:steer: any admissible choice keeps the certificate,
// so the window certificate is unchanged by construction; only the actual point set changes).
// Law and kernels identical to steer_centre.cpp (prop:LI(c), prop:depthdir); only the selection differs.
//   mode cenhi : most central own value w.r.t. the EXACT centre (lo+hi)/2 of the own window (compare |2o-(lo+hi)|),
//                ties -> the larger own value (closer to 0 = smaller |own|; own windows lie in [-(p-1),0])
//   mode cenlo : same, ties -> the smaller own value
//   mode near0 : the largest admissible own value (closest to 0 from below)
//   mode psimin: the smallest admissible digit psi_{c',l} in {0,..,p-1}   ("lexicographic")
//   mode lb1   : depth 1: over ALL combinations of admissible depth-1 own values of the s columns, maximise the exact
//                lem:cert (j=1) certificate of the ACTUAL level-1 responses D(1) (own O^(1), crosses X^(1) = -kappa);
//                ties -> cenhi ranks (column 0 first); depths >= 2: cenhi
//   mode own   : legacy steer_centre/hd_steer behaviour (C++ integer centre, unstable sort) -- reference only
//   mode force:v0,..,v_{s-1}: depth-1 own values forced (exhaustive depth-1 scan), deeper cenhi
// usage: steer_rule cfg N out_prefix mode      writes out_prefix_series.txt / _partial.txt (hv_dump input)
#include "../common/hd_common.h"
#include <sstream>
#include <functional>
static int s; static ll th; static std::vector<ll> a,lam; static std::vector<std::vector<ll>> kap; static std::vector<std::vector<IW>> Wn;
static int NN,N;
static bool inI(ll x, IW I){ ll t=I.lo+md(x-I.lo); return t<=I.hi; }
static ll repr(ll x, IW I){ return I.lo+md(x-I.lo); } // representative in window (if admissible)
struct Col { std::vector<ll> wh; std::vector<std::vector<ll>> chi; std::vector<int> xs; };
static std::vector<ll> smul(const std::vector<ll>&x,const std::vector<ll>&y){ std::vector<ll> z(NN,0); for(int i=0;i<NN;i++) if(x[i]) for(int j=0;i+j<NN;j++) if(y[j]) z[i+j]=(z[i+j]+mulm(x[i],y[j]))%P; return z; }
static Col prep(int cp){
  Col C; ll A=a[cp]; std::vector<ll> d; for(int e=0;e<s;e++) if(e!=cp) d.push_back(md(A-a[e]));
  std::vector<ll> poly(1,1); for(ll de:d){ std::vector<ll> q(poly.size()+1,0); for(size_t i=0;i<poly.size();i++){ q[i]=(q[i]+mulm(poly[i],de))%P; q[i+1]=(q[i+1]+poly[i])%P; } poly=q; }
  std::vector<ll> cj(s+1,0); for(int j=1;j<=s;j++) cj[j]=poly[j-1]; ll iw1=inv(cj[1]);
  std::vector<ll> u(NN,0); u[1]=iw1;
  for(int n=2;n<NN;n++){ std::vector<ll> U=u; for(int i=n;i<NN;i++) U[i]=0; std::vector<ll> Pw=U; ll sacc=0; for(int j=2;j<=s;j++){ Pw=smul(Pw,U); sacc=(sacc+mulm(cj[j],Pw[n]))%P; } u[n]=md(-mulm(sacc,iw1)); }
  { std::vector<ll> Pw=u, t(NN,0); for(int i=0;i<NN;i++) t[i]=mulm(cj[1],u[i]); for(int j=2;j<=s;j++){ Pw=smul(Pw,u); for(int i=0;i<NN;i++) t[i]=(t[i]+mulm(cj[j],Pw[i]))%P; }
    for(int n=1;n<NN;n++) if(t[n]!=(n==1)){ printf("reversion error\n"); exit(8); } }
  C.wh.assign(NN,0); std::vector<ll> Pw(NN,0); Pw[0]=1; for(int j=1;j<=s;j++){ for(int i=0;i<NN;i++) C.wh[i]=(C.wh[i]+mulm(cj[j],Pw[i]))%P; Pw=smul(Pw,u); }
  for(int i=0;i<NN;i++) C.wh[i]=mulm(C.wh[i],iw1);
  C.chi.assign(s,{});
  for(int c=0;c<s;c++) if(c!=cp){ C.xs.push_back(c); ll id=inv(md(a[cp]-a[c])); std::vector<ll> g(NN,0); for(int n=0;n<NN;n++) g[n]=((n==0)+mulm(id,u[n]))%P;
    std::vector<ll> h(NN,0); h[0]=1; for(int n=1;n<NN;n++){ ll sm=0; for(int k=1;k<=n;k++) sm=(sm+mulm(g[k],h[n-k]))%P; h[n]=md(-sm); } C.chi[c]=h; }
  return C; }
// admissible own values at depth l given psi[0..l-1]; returns list of (own representative o, pb) ; also bO,bX
static void admissible(int cp,const Col&C,const std::vector<ll>&psi,int l,ll O,const std::vector<ll>&X,std::vector<std::pair<ll,ll>>&adm){
  adm.clear(); ll thl=pw(th,l);
  ll so=0; for(int k=0;k<l;k++) so=(so+mulm(C.wh[l-k],psi[k]))%P; ll bO=md(O-mulm(thl,so));
  std::vector<ll> bX(s,0); for(int c:C.xs){ ll sx=0; for(int k=0;k<l;k++) sx=(sx+mulm(C.chi[c][l-k],psi[k]))%P; bX[c]=md(X[c]-mulm(mulm(md(kap[c][cp]),thl),sx)); }
  for(ll o=Wn[cp][cp].lo;o<=Wn[cp][cp].hi;o++){ ll pb=md(o-bO); bool ok=true; for(int c:C.xs){ ll v=(bX[c]+mulm(pb,md(kap[c][cp])))%P; if(!inI(v,Wn[c][cp])){ ok=false; break; } } if(ok) adm.push_back({o,pb}); } }
static bool better_cen(ll x,ll y,IW I,bool hi){ ll dx=llabs(2*x-(I.lo+I.hi)), dy=llabs(2*y-(I.lo+I.hi)); if(dx!=dy) return dx<dy; return hi? x>y : x<y; }
int main(int argc,char**argv){
  if(argc<5){ fprintf(stderr,"usage: steer_rule cfg N out_prefix mode\n"); return 1; }
  FILE*f=fopen(argv[1],"r"); N=atoi(argv[2]); std::string pre=argv[3]; std::string mode=argv[4];
  int bb; char md_[32], tag[64];
  if(fscanf(f," s %d p %lld theta %lld brick %d mode %31s",&s,&P,&th,&bb,md_)!=5) return 2;
  a.resize(s); lam.resize(s); if(fscanf(f," %63s",tag)!=1) return 3; for(int c=0;c<s;c++) if(fscanf(f,"%lld",&a[c])!=1) return 3;
  if(fscanf(f," %63s",tag)!=1) return 4; for(int c=0;c<s;c++) if(fscanf(f,"%lld",&lam[c])!=1) return 4;
  kap.assign(s,std::vector<ll>(s)); for(int c=0;c<s;c++){ if(fscanf(f," %63s",tag)!=1) return 5; for(int cp=0;cp<s;cp++) if(fscanf(f,"%lld",&kap[c][cp])!=1) return 5; }
  Wn.assign(s,std::vector<IW>(s)); for(int r=0;r<s;r++){ int cp; if(fscanf(f," %63s %d",tag,&cp)!=2) return 6; for(int c=0;c<s;c++) if(fscanf(f,"%lld %lld",&Wn[c][cp].lo,&Wn[c][cp].hi)!=2) return 6; }
  fclose(f);
  auto wp=[&](int c){ ll r=1; for(int e=0;e<s;e++) if(e!=c) r=mulm(r,md(a[c]-a[e])); return r; };
  for(int c=0;c<s;c++) for(int cp=0;cp<s;cp++) if(c!=cp){ ll k=mulm(mulm(md(th),md(lam[c])),inv(mulm(mulm(md(lam[cp]),wp(c)),md(a[cp]-a[c])))); if(k!=md(kap[c][cp])){ printf("kappa NOT realised by gauge\n"); return 7; } }
  for(int c=0;c<s;c++) for(int cp=0;cp<s;cp++) if(c!=cp && !inI(-kap[c][cp],Wn[c][cp])){ printf("forced cross outside window\n"); return 7; }
  NN=N+2; std::vector<Col> CC(s); for(int cp=0;cp<s;cp++) CC[cp]=prep(cp);
  // depth-1 forced choices (mode lb1)
  std::vector<ll> force(s,LLONG_MIN);
  if(mode.rfind("force:",0)==0){ std::stringstream ss(mode.substr(6)); std::string t; int c=0; while(std::getline(ss,t,',')&&c<s) force[c++]=atoll(t.c_str()); mode="cenhi"; }
  { printf("depth-1 admissible own values:"); for(int cp=0;cp<s;cp++){ std::vector<ll> psi(N+1,0); psi[0]=1; std::vector<ll> X(s,0); for(int c:CC[cp].xs) X[c]=md(-kap[c][cp]);
      std::vector<std::pair<ll,ll>> ad; admissible(cp,CC[cp],psi,1,0,X,ad); printf(" |"); for(auto&q:ad) printf(" %lld",q.first); } printf("\n"); }
  if(mode=="lb1"){
    std::vector<std::vector<std::pair<ll,ll>>> A1(s);
    for(int cp=0;cp<s;cp++){ std::vector<ll> psi(N+1,0); psi[0]=1; std::vector<ll> X(s,0); for(int c:CC[cp].xs) X[c]=md(-kap[c][cp]);
      admissible(cp,CC[cp],psi,1,0,X,A1[cp]);
      std::sort(A1[cp].begin(),A1[cp].end(),[&](auto&x,auto&y){ return better_cen(x.first,y.first,Wn[cp][cp],true); });
      if(A1[cp].empty()){ printf("STUCK at depth 1\n"); return 9; } }
    auto ST=steps_s(s); ll best=-1; std::vector<int> bi(s,0), idx(s,0);
    std::function<void(int)> rec=[&](int c){ if(c==s){ // D1[c][cp]: own = O^(1)_cp = own value o ; cross = -kappa
        ll mn=-1; for(auto&e:ST){ ll tot=0; for(int r=0;r<s;r++){ ll sg=0; for(int cp=0;cp<s;cp++) if(e[cp]){ ll v= (r==cp)? A1[cp][idx[cp]].first : -kap[r][cp]; sg+=e[cp]*v; } ll m=pf1(e[r],sg); tot+=m*m; } if(mn<0||tot<mn) mn=tot; }
        if(mn>best){ best=mn; bi=idx; } return; }
      for(size_t i=0;i<A1[c].size();i++){ idx[c]=(int)i; rec(c+1); } };
    rec(0); for(int cp=0;cp<s;cp++) force[cp]=A1[cp][bi[cp]].first;
    printf("lb1: depth-1 actual LB_1 = %.6f, combos =",sqrt((double)best)/P); for(int cp=0;cp<s;cp++) printf(" %zu",A1[cp].size()); printf("\n"); }
  FILE*out=fopen((pre+"_series.txt").c_str(),"w"); FILE*ps=fopen((pre+"_partial.txt").c_str(),"w");
  fprintf(out,"# s %d p %lld theta %lld N %d\nplaces",s,P,th,N); for(int c=0;c<s;c++) fprintf(out," %lld",md(a[c])); fprintf(out,"\nlambda"); for(int c=0;c<s;c++) fprintf(out," %lld",md(lam[c])); fprintf(out,"\n");
  fprintf(ps,"# column c' depth l: O^(l) then X_{c<-c'}^(l+1) for c != c' in increasing order (centred); depth 0: X^(1)\n");
  long viol=0; bool stuck=false; long admsum=0,nsteps=0; std::vector<ll> d1(s);
  for(int cp=0;cp<s;cp++){ const Col&C=CC[cp];
    std::vector<ll> psi(N+1,0); psi[0]=1; ll O=0; std::vector<ll> X(s,0); for(int c:C.xs) X[c]=md(-kap[c][cp]);
    fprintf(ps,"column %d depth 0:",cp); for(int c:C.xs) fprintf(ps," %lld",cen(X[c])); fprintf(ps,"\n");
    IW I=Wn[cp][cp]; std::vector<std::pair<ll,ll>> adm;
    for(int l=1;l<=N;l++){ ll thl=pw(th,l); admissible(cp,C,psi,l,O,X,adm); admsum+=adm.size(); nsteps++;
      if(adm.empty()){ stuck=true; printf("STUCK column %d depth %d\n",cp,l); break; }
      std::pair<ll,ll> pk=adm[0];
      if(l==1 && force[cp]!=LLONG_MIN){ for(auto&q:adm) if(q.first==force[cp]) pk=q; }
      else if(mode=="cenhi"||mode=="lb1"||mode=="cenlo"){ bool hi=(mode!="cenlo"); for(auto&q:adm) if(better_cen(q.first,pk.first,I,hi)) pk=q; }
      else if(mode=="near0"){ for(auto&q:adm) if(q.first>pk.first) pk=q; }
      else if(mode=="psimin"){ auto psiof=[&](ll pb){ return md(-mulm(pb,inv(thl))); }; for(auto&q:adm) if(psiof(q.second)<psiof(pk.second)) pk=q; }
      else if(mode=="own"){ ll oc=(I.lo+I.hi)/2; std::vector<ll> owl; for(ll o=I.lo;o<=I.hi;o++) owl.push_back(o); std::sort(owl.begin(),owl.end(),[&](ll x,ll y){ return llabs(x-oc)<llabs(y-oc); });
        bool done=false; for(ll o:owl){ for(auto&q:adm) if(q.first==o){ pk=q; done=true; break; } if(done) break; } }
      else { fprintf(stderr,"bad mode\n"); return 1; }
      if(l==1) d1[cp]=pk.first;
      ll pick=pk.second; psi[l]=md(-mulm(pick,inv(thl)));
      ll sO=0; for(int k=0;k<=l;k++) sO=(sO+mulm(C.wh[l-k],psi[k]))%P; O=md(O-mulm(thl,sO));
      for(int c:C.xs){ ll sx=0; for(int k=0;k<=l;k++) sx=(sx+mulm(C.chi[c][l-k],psi[k]))%P; X[c]=md(X[c]-mulm(mulm(md(kap[c][cp]),thl),sx)); }
      if(!inI(O,Wn[cp][cp])) viol++; for(int c:C.xs) if(!inI(X[c],Wn[c][cp])) viol++;
      if(repr(O,Wn[cp][cp])!=pk.first && inI(O,Wn[cp][cp])) viol++;
      fprintf(ps,"column %d depth %d: %lld",cp,l,cen(O)); for(int c:C.xs) fprintf(ps," %lld",cen(X[c])); fprintf(ps,"\n"); }
    fprintf(out,"psi %d",cp); for(int l=0;l<=N;l++) fprintf(out," %lld",psi[l]); fprintf(out,"\n"); }
  fclose(out); fclose(ps);
  { auto ST=steps_s(s); ll mn=-1; for(auto&e:ST){ ll tot=0; for(int r=0;r<s;r++){ ll sg=0; for(int cp=0;cp<s;cp++) if(e[cp]) sg+=e[cp]*((r==cp)? d1[cp] : -kap[r][cp]); ll m=pf1(e[r],sg); tot+=m*m; } if(mn<0||tot<mn) mn=tot; }
    printf("actual level-1 certificate LB_1(P_s) = %.6f\n",sqrt((double)mn)/P); }
  printf("mode %s: depth %d: %s, violations %ld, mean #adm %.2f, depth-1 own:",mode.c_str(),N,stuck?"STUCK":"never stuck",viol,(double)admsum/std::max(1L,nsteps)); for(int c=0;c<s;c++) printf(" %lld",d1[c]); printf("\n");
  return stuck?9:0; }
