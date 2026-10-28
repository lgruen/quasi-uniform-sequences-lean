// bs_mind.cpp -- exact separation of the full level P_3 (K=1, N=p^3) of a digital (0,3)-sequence:
// points x_c = sum_{i<R} y_{c,i} p^{-i-1} with y_{c,i} = sum_j C'_c[i][j] n_j (n_j = base-p digits of the index, j<3),
// i.e. R geometric digits (R>3 includes the jitter of the deeper rows). Each cell (y_{0,0},y_{1,0},y_{2,0}) holds one point;
// any toroidal pair closer than 1 cell lies in adjacent cells, so sep = min(1, min over the 13 neighbour offsets).
// usage: bs_mind dumpfile   (format of bs_verify's dump: "p R C" then 3*R rows of C columns; uses columns 0..2)
#include "bs_common.h"
int main(int argc,char**argv){ FILE*f=fopen(argv[1],"r"); int R,C; if(fscanf(f,"%lld %d %d",&P,&R,&C)!=3) return 1;
  std::vector<std::vector<ll>> G[3]; for(int c=0;c<3;c++){ G[c].assign(R,std::vector<ll>(C)); for(int i=0;i<R;i++) for(int j=0;j<C;j++) if(fscanf(f,"%lld",&G[c][i][j])!=1) return 2; }
  fclose(f); ll N=P*P*P;
  for(int Rr: {3, R}){
    std::vector<double> X[3]; std::vector<int> cell(N,-1); for(int c=0;c<3;c++) X[c].assign(N,0);
    bool net=true;
    for(ll n=0;n<N;n++){ ll d[3]={n%P,(n/P)%P,n/(P*P)}; ll y0[3];
      for(int c=0;c<3;c++){ double x=0, sc=1; for(int i=0;i<Rr;i++){ ll y=(G[c][i][0]*d[0]+G[c][i][1]*d[1]+G[c][i][2]*d[2])%P; if(i==0) y0[c]=y; x+=y*sc; sc/=P; } X[c][n]=x; }
      ll id=(y0[0]*P+y0[1])*P+y0[2]; if(cell[id]>=0) net=false; cell[id]=(int)n; }
    double best=1e9; ll bi=-1,bj=-1;
    for(ll id=0;id<N;id++){ ll y0=id/(P*P), y1=(id/P)%P, y2=id%P; ll n=cell[id];
      for(int a=-1;a<=1;a++)for(int b=-1;b<=1;b++)for(int e=-1;e<=1;e++){ if(a<0||(a==0&&(b<0||(b==0&&e<=0)))) continue;
        ll jd=(md(y0+a)*P+md(y1+b))*P+md(y2+e); ll m=cell[jd]; double s=0;
        for(int c=0;c<3;c++){ double dd=fabs(X[c][n]-X[c][m]); dd=std::min(dd,(double)P-dd); s+=dd*dd; }
        if(s<best){ best=s; bi=n; bj=m; } } }
    printf("R=%d digits: net(one point per cell)=%s  sep(P_3) = %s%.6f  (closest pair indices %lld, %lld)\n",Rr,net?"yes":"NO",sqrt(best)>=1?">= 1 cap; nbr min ":"",sqrt(best),bi,bj); }
}
