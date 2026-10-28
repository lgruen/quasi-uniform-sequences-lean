// hv_dump.cpp -- copy of the research program hd_verify.cpp + a dump hook (bs_mind format).
// usage: hv_dump prefix s "K1,.." mmax Kc [dumprows dumpcols dumpfile]
// (original header:) hd_verify.cpp -- INDEPENDENT verification of a steered sequence, general s (port of the research program bs_verify.cpp).
// Does not use the law of prop:LI(c): from psi_c build the self-similar scramble in the Riordan form of prop:LI(a),
//   L_c[j][k] = lambda_c theta^j [u^{j-k}] h(u)^{-(j+1)} phi_c(w(u)),  phi_c = 1/psi_c,  h(u) = w(a_c+u)/u,
// generator matrices C'_c = L_c C_c with C_c[i][j] = binom(j,i) a_c^{j-i}; level-K law by Gaussian elimination over F_p
// (r_c B = C'_c[K, :sK], B = rows (c, i<K)), compared with every steered partial sum O^{(l)}, X^{(l)}, l <= K.
// Also: t = 0 by the composition rank check on the actual matrices (prefixes m <= mmax); exact certificate of the
// ACTUAL responses for K = 1..Kc (lem:cert j = 1, exact joint minimum over carry-length tuples).
// usage: hd_verify prefix s "K1,K2,..." mmax Kc
#include "../common/hd_common.h"
#include <sstream>
#include <chrono>
#include <functional>
static int S; static std::vector<std::vector<std::vector<ll>>> Cp; static std::vector<ll> a, lam; static ll th; static int Nser;
static std::vector<std::vector<ll>> psi;
static std::vector<ll> smul(const std::vector<ll>&x,const std::vector<ll>&y,int n){ std::vector<ll> z(n,0);
  for(int i=0;i<n&&i<(int)x.size();i++) if(x[i]) for(int j=0;i+j<n&&j<(int)y.size();j++) if(y[j]) z[i+j]=(z[i+j]+mulm(x[i],y[j]))%P; return z; }
static std::vector<ll> sinv(const std::vector<ll>&x,int n){ std::vector<ll> z(n,0); ll i0=inv(x[0]); z[0]=i0;
  for(int k=1;k<n;k++){ ll sm=0; for(int j=1;j<=k&&j<(int)x.size();j++) sm=(sm+mulm(x[j],z[k-j]))%P; z[k]=md(-mulm(sm,i0)); } return z; }
static void build(int nrows,int ncols){
  std::vector<std::vector<ll>> B(ncols+1,std::vector<ll>(ncols+1,0)); for(int j=0;j<=ncols;j++){ B[j][0]=1; for(int i=1;i<=j;i++) B[j][i]=(B[j-1][i-1]+(i<=j-1?B[j-1][i]:0))%P; }
  Cp.assign(S,{});
  for(int c=0;c<S;c++){ int n=nrows; ll A=md(a[c]);
    std::vector<ll> hu(1,1); for(int e=0;e<S;e++) if(e!=c){ ll de=md(A-a[e]); std::vector<ll> q(hu.size()+1,0); for(size_t i=0;i<hu.size();i++){ q[i]=(q[i]+mulm(hu[i],de))%P; q[i+1]=(q[i+1]+hu[i])%P; } hu=q; }
    std::vector<ll> wu(hu.size()+1,0); for(size_t i=0;i<hu.size();i++) wu[i+1]=hu[i];
    std::vector<ll> hinv=sinv(hu,n);
    std::vector<ll> ps(psi[c].begin(),psi[c].begin()+std::min((int)psi[c].size(),n)); ps.resize(n,0);
    std::vector<ll> phi=sinv(ps,n);
    std::vector<ll> phw(n,0); for(int k=n-1;k>=0;k--){ phw=smul(phw,wu,n); phw[0]=(phw[0]+phi[k])%P; }
    std::vector<std::vector<ll>> L(n,std::vector<ll>(n,0)); std::vector<ll> cur=hinv;
    for(int j=0;j<n;j++){ std::vector<ll> fz=smul(cur,phw,j+1); ll sc=mulm(md(lam[c]),pw(th,j)); for(int k=0;k<=j;k++) L[j][k]=mulm(sc,fz[j-k]); cur=smul(cur,hinv,n); }
    std::vector<ll> apw(ncols+1,1); for(int i=1;i<=ncols;i++) apw[i]=mulm(apw[i-1],A);
    Cp[c].assign(n,std::vector<ll>(ncols,0));
    for(int i=0;i<n;i++) for(int j=0;j<ncols;j++){ ll sm=0; for(int k=0;k<=i&&k<=j;k++) if(L[i][k]) sm=(sm+mulm(L[i][k],mulm(B[j][k],apw[j-k])))%P; Cp[c][i][j]=sm; } } }
static int rankp(std::vector<std::vector<ll>> M){ int r=0,R=M.size(),C=M[0].size();
  for(int c=0;c<C&&r<R;c++){ int pv=-1; for(int i=r;i<R;i++) if(M[i][c]){pv=i;break;} if(pv<0) continue; std::swap(M[r],M[pv]);
    ll iv=inv(M[r][c]); for(int j=c;j<C;j++) M[r][j]=mulm(M[r][j],iv);
    for(int i=r+1;i<R;i++) if(M[i][c]){ ll fct=M[i][c]; for(int j=c;j<C;j++) M[i][j]=md(M[i][j]-mulm(fct,M[r][j])); } r++; } return r; }
int main(int argc,char**argv){
  std::string pre=argv[1]; S=atoi(argv[2]); std::vector<int> Ks; { std::stringstream ss(argv[3]); std::string t; while(std::getline(ss,t,',')) Ks.push_back(atoi(t.c_str())); }
  int mmax=atoi(argv[4]); int Kc=argc>5? atoi(argv[5]) : 0;
  FILE*f=fopen((pre+"_series.txt").c_str(),"r"); char tag[64]; int s2;
  if(fscanf(f,"# s %d p %lld theta %lld N %d",&s2,&P,&th,&Nser)!=4||s2!=S) return 2;
  a.resize(S); lam.resize(S); if(fscanf(f," %63s",tag)!=1) return 3; for(int c=0;c<S;c++) if(fscanf(f,"%lld",&a[c])!=1) return 3;
  if(fscanf(f," %63s",tag)!=1) return 3; for(int c=0;c<S;c++) if(fscanf(f,"%lld",&lam[c])!=1) return 3;
  psi.assign(S,std::vector<ll>(Nser+1)); for(int c=0;c<S;c++){ int cc; if(fscanf(f," %63s %d",tag,&cc)!=2) return 4; for(int l=0;l<=Nser;l++) if(fscanf(f,"%lld",&psi[cc][l])!=1) return 4; }
  fclose(f);
  // steering partial sums D[cp][c][l] = response of column cp in coordinate c at carry length l (own: O^{(l)}, cross: X^{(l)})
  std::vector<std::vector<std::vector<ll>>> D(S,std::vector<std::vector<ll>>(S,std::vector<ll>(Nser+2,0)));
  f=fopen((pre+"_partial.txt").c_str(),"r"); char buf[1<<16]; if(!fgets(buf,sizeof buf,f)) return 5;
  while(fgets(buf,sizeof buf,f)){ int cp,l; int nread=0; if(sscanf(buf,"column %d depth %d:%n",&cp,&l,&nread)!=2) continue;
    std::stringstream ss(buf+nread); std::vector<ll> vals; ll x; while(ss>>x) vals.push_back(x);
    std::vector<int> xs; for(int c=0;c<S;c++) if(c!=cp) xs.push_back(c);
    if(l==0){ for(int q=0;q<S-1;q++) D[cp][xs[q]][1]=md(vals[q]); }
    else { D[cp][cp][l]=md(vals[0]); for(int q=0;q<S-1;q++) if(l+1<=Nser+1) D[cp][xs[q]][l+1]=md(vals[q+1]); } }
  fclose(f);
  int Kmax=*std::max_element(Ks.begin(),Ks.end()); int nrows=std::max(Kmax+1,mmax); int ncols=std::max(S*Kmax,mmax);
  auto t0=std::chrono::steady_clock::now(); auto el=[&](){ return std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count(); };
  int dr=0,dc=0; if(argc>8){ dr=atoi(argv[6]); dc=atoi(argv[7]); nrows=std::max(nrows,dr); ncols=std::max(ncols,dc); }
  build(nrows,ncols);
  if(argc>8){ FILE*g=fopen(argv[8],"w"); fprintf(g,"%lld %d %d\n",P,dr,dc); for(int c=0;c<S;c++) for(int i=0;i<dr;i++){ for(int j=0;j<dc;j++) fprintf(g,"%lld ",Cp[c][i][j]); fprintf(g,"\n"); } fclose(g); printf("dumped %d x %d of each C'_c to %s\n",dr,dc,argv[8]); } printf("built C'_c: %d rows x %d cols (%.1fs)\n",nrows,ncols,el());
  long totmis=0,totchk=0;
  for(int K:Ks){ if(K>Nser){ printf("K=%d > N skip\n",K); continue; } int m=S*K;
    std::vector<std::vector<ll>> M(m,std::vector<ll>(m+S,0));
    for(int c=0;c<S;c++) for(int i=0;i<K;i++) for(int j=0;j<m;j++) M[j][c*K+i]=Cp[c][i][j];
    for(int c=0;c<S;c++) for(int j=0;j<m;j++) M[j][m+c]=Cp[c][K][j];
    int r=0; for(int col=0;col<m;col++){ int pv=-1; for(int i=r;i<m;i++) if(M[i][col]){pv=i;break;} if(pv<0){ printf("K=%d singular B\n",K); return 7; }
      std::swap(M[r],M[pv]); ll iv=inv(M[r][col]); for(int j=col;j<m+S;j++) M[r][j]=mulm(M[r][j],iv);
      for(int i=0;i<m;i++) if(i!=r&&M[i][col]){ ll fct=M[i][col]; for(int j=col;j<m+S;j++) if(M[r][j]) M[i][j]=md(M[i][j]-mulm(fct,M[r][j])); } r++; }
    long mis=0,chk=0;
    for(int cp=0;cp<S;cp++) for(int l=1;l<=K;l++) for(int c=0;c<S;c++){ ll sm=0; for(int i=K-l;i<K;i++) sm+=M[cp*K+i][m+c]; sm=md(sm);
      chk++; if(sm!=D[cp][c][l]){ if(mis<5) printf("  mismatch K=%d col %d coord %d l=%d: LA %lld vs steer %lld\n",K,cp,c,l,cen(sm),cen(D[cp][c][l])); mis++; } }
    totmis+=mis; totchk+=chk; printf("K=%d: direct law vs steering: %ld/%ld agree (%.1fs)\n",K,chk-mis,chk,el()); fflush(stdout); }
  // t = 0
  int tbad=0; long ncomp=0; int mdone=0;
  for(int m=1;m<=mmax;m++){ std::vector<int> d(S,0);
    std::function<void(int,int)> rec=[&](int c,int left){ if(c==S-1){ d[c]=left; std::vector<std::vector<ll>> R; for(int q=0;q<S;q++) for(int i=0;i<d[q];i++) R.push_back(std::vector<ll>(Cp[q][i].begin(),Cp[q][i].begin()+m)); ncomp++; if(rankp(R)<m) tbad++; return; }
      for(int x=0;x<=left;x++){ d[c]=x; rec(c+1,left-x); } };
    rec(0,m); mdone=m; if(el()>40) break; }
  printf("t=0 check: prefixes m=1..%d, %ld compositions, rank-deficient: %d\n",mdone,ncomp,tbad);
  // exact certificate of the actual responses, K = 1..Kc (joint minimum over carry-length tuples l_c in [1,K])
  auto ST=steps_s(S);
  for(int K=1;K<=Kc && K<=Nser;K++){ ll best=-1; std::vector<int> bw;
    for(auto&e:ST){ std::vector<int> mv; for(int c=0;c<S;c++) if(e[c]) mv.push_back(c); std::vector<int> l(mv.size(),1);
      while(true){ ll tot=0; for(int c=0;c<S;c++){ ll sg=0; for(size_t q=0;q<mv.size();q++){ int cp=mv[q]; sg+= e[cp]*D[cp][c][l[q]]; } tot+= pf1(e[c],sg)*pf1(e[c],sg); }
        if(best<0||tot<best){ best=tot; bw=e; }
        size_t q=0; while(q<l.size()){ l[q]++; if(l[q]<=K) break; l[q]=1; q++; } if(q==l.size()) break; } }
    printf("actual-response certificate K=%d (P_{%d K}): LB_1 = %.6f (minS %lld)\n",K,S,sqrt((double)best)/P,best); }
  printf("SUMMARY: %ld/%ld law responses agree; t=0 rank-deficient compositions: %d\n",totchk-totmis,totchk,tbad);
}
