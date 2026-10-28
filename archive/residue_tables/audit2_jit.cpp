// Second audit: exact lambda_jit^2 of Lambda_v, v = (x_1..x_{s-1}, -1) over F_p:
//   lambda_jit^2 = min_{0 != b in Lambda_v} sum_c (|b_c| - 1)_+^2.
// usage: jit eval p s x1 .. x_{s-1}        -> exact lambda^2
//        jit exh  p s                      -> max over all x in (F_p^*)^{s-1} of lambda^2 (exhaustive), one argmax
// Exactness: if the box [-B,B]^s (B < p/2) has min <= B^2, it is the global min (any vector leaving the box has >= B^2).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
using namespace std;
typedef long long ll;
static int p, s;
static inline ll cen(ll a){ a%=p; if(a<0) a+=p; if(2*a>p) a-=p; return a; }
static inline ll f1(ll b){ ll a = b<0? -b: b; return a>1? (a-1)*(a-1): 0; }
// min over box of nonzero lattice vectors with value; stop early if value <= stopv (returns that value)
static ll boxmin(const vector<ll>& x, int B, ll stopv){
  int d = s-1; vector<int> b(d, -B); ll best = (ll)1<<60;
  while(true){
    bool zero = true; ll lin = 0, val = 0;
    for(int i=0;i<d;i++){ if(b[i]) zero=false; lin += x[i]*b[i]; val += f1(b[i]); }
    if(!zero && val < best){
      ll last = cen(lin); // b_{s-1} = x . b'  (since sum v_c b_c = x.b' - b_{s-1} = 0)
      if((last<0?-last:last) <= B){ ll v = val + f1(last); if(v<best){ best=v; if(best<=stopv) return best; } }
    }
    int i=0; while(i<d && b[i]==B){ b[i]=-B; i++; } if(i==d) break; b[i]++;
  }
  return best;
}
static ll lam2(const vector<ll>& x, ll stopv){
  for(int B=1;;B++){
    if(2*B >= p){ fprintf(stderr,"B too large\n"); exit(1); }
    ll m = boxmin(x, B, stopv);
    if(m <= stopv) return m;          // early stop (caller only needs "<= stopv")
    if(m <= (ll)B*B) return m;        // exact
  }
}
int main(int argc, char** argv){
  if(argc<4) return 1;
  p = atoi(argv[2]); s = atoi(argv[3]);
  if(!strcmp(argv[1],"eval")){
    vector<ll> x(s-1); for(int i=0;i<s-1;i++) x[i]=atoll(argv[4+i]);
    printf("lambda^2=%lld\n", lam2(x, -1)); return 0;
  }
  vector<ll> x(s-1,1), arg; ll best = -1; long long cnt=0;
  while(true){
    ll v = lam2(x, best);             // returns exact value if > best, else some value <= best
    if(v > best){ best = v; arg = x; cnt = 1; } else if(v == best) cnt++;
    int i=0; while(i<s-1 && x[i]==p-1){ x[i]=1; i++; } if(i==s-1) break; x[i]++;
  }
  printf("max lambda^2=%lld argmax x=(", best); for(auto a: arg) printf("%lld,", a); printf("-1)\n");
  return 0;
}
