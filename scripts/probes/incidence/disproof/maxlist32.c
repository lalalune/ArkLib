// maxlist32.c — fast EXACT RS list counter + hill-climb for the proximity-floor disproof.
// Domain: mu_n (order-n mult subgroup) of F_q (q prime). codeword = deg<k poly on mu_n.
// list(w,a) = #{distinct deg<k polys agreeing with w on >= a points}.
// Counting: enumerate k-subsets, interpolate (precomputed Lagrange basis), dedup by full
// evaluation signature, count agreement>=a. Exact for a>=k. 64-bit modular arithmetic.
//
// Usage:
//   maxlist32 q n k a seed restarts hill_iters mode
//   mode: "search" -> random+monomial+cluster+hillclimb, prints best list and word.
//         "count W0 W1 ..." -> exact list(w,a) for given word (verification).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;
typedef __uint128_t u128;

static u64 Q;
static inline u64 mulm(u64 a, u64 b){ return (u64)(( (u128)a*b)%Q); }
static inline u64 addm(u64 a, u64 b){ u64 s=a+b; if(s>=Q)s-=Q; return s; }
static inline u64 subm(u64 a, u64 b){ return a>=b? a-b : a+Q-b; }
static u64 powm(u64 a,u64 e){ u64 r=1%Q; a%=Q; while(e){ if(e&1) r=mulm(r,a); a=mulm(a,a); e>>=1; } return r; }
static inline u64 invm(u64 a){ return powm(a, Q-2); }

static int N, K, A;
static u64 SUB[64];           // mu_n elements
// k-subsets and their Lagrange weight rows: for subset s, W[s][t][m] gives p(x_t)=sum_m W*ys[m]
// We store weights flattened. Number of subsets can be large (10.5M); store per-subset index list
// and compute weights on the fly is too slow. Instead we precompute, for each subset, the N*K
// weight matrix? That is 10.5M*32*8*8 bytes = huge. Instead compute weights per subset on the fly
// but cache denominators. We'll just compute Lagrange eval on the fly (fast enough in C).

// find generator of order exactly n
static void find_sub(u64 q,int n){
    for(u64 g=2; g<q; g++){
        if(powm(g,n)!=1) continue;
        int ok=1;
        for(int d=1; d<n; d++){ if(n%d==0 && d<n && powm(g,d)==1){ok=0;break;} }
        if(ok){ for(int j=0;j<n;j++) SUB[j]=powm(g,j); return; }
    }
    fprintf(stderr,"no order-%d element\n",n); exit(1);
}

// Evaluate the deg<K interpolant through points (SUB[idx[m]], ys[m]) at all N domain points,
// accumulate agreement with w; return agreement count and fill sig[] (eval at all points).
static inline int interp_eval(const int* idx, const u64* ys, const u64* w, u64* sig){
    // Lagrange: p(x_t) = sum_m ys[m] * prod_{j!=m} (x_t - x_{idx[j]})/(x_{idx[m]} - x_{idx[j]})
    u64 xs[16];
    for(int m=0;m<K;m++) xs[m]=SUB[idx[m]];
    u64 denomInv[16];
    for(int m=0;m<K;m++){
        u64 d=1;
        for(int j=0;j<K;j++) if(j!=m) d=mulm(d, subm(xs[m],xs[j]));
        denomInv[m]=invm(d);
    }
    int ag=0;
    for(int t=0;t<N;t++){
        u64 xt=SUB[t];
        u64 v=0;
        for(int m=0;m<K;m++){
            u64 num=1;
            for(int j=0;j<K;j++) if(j!=m) num=mulm(num, subm(xt,xs[j]));
            v=addm(v, mulm(mulm(num,denomInv[m]), ys[m]));
        }
        sig[t]=v;
        if(v==w[t]) ag++;
    }
    return ag;
}

// simple open-addressing hash set of signatures (hash of N u64 evals) to dedup codewords
typedef struct { u64* keys; int* used; size_t cap; size_t cnt; } HSet;
static u64 sighash(const u64* sig){
    u64 h=1469598103934665603ULL;
    for(int t=0;t<N;t++){ h^=sig[t]; h*=1099511628211ULL; }
    return h;
}
static void hs_init(HSet* s, size_t cap){ s->cap=cap; s->keys=calloc(cap,sizeof(u64)); s->used=calloc(cap,sizeof(int)); s->cnt=0; }
static void hs_clear(HSet* s){ memset(s->used,0,s->cap*sizeof(int)); s->cnt=0; }
static int hs_add(HSet* s, u64 h){ // returns 1 if newly added
    size_t i=h % s->cap;
    while(s->used[i]){ if(s->keys[i]==h) return 0; i++; if(i==s->cap)i=0; }
    s->used[i]=1; s->keys[i]=h; s->cnt++; return 1;
}

// enumerate all k-subsets and count distinct codewords with agreement>=A
static HSet GHS;
static long count_list(const u64* w){
    hs_clear(&GHS);
    long cnt=0;
    int idx[16]; u64 ys[16]; u64 sig[64];
    // iterative combinations
    for(int m=0;m<K;m++) idx[m]=m;
    while(1){
        for(int m=0;m<K;m++) ys[m]=w[idx[m]];
        int ag=interp_eval(idx,ys,w,sig);
        u64 h=sighash(sig);
        if(hs_add(&GHS,h)){
            if(ag>=A) cnt++;
        }
        // next combination
        int p=K-1;
        while(p>=0 && idx[p]==N-K+p) p--;
        if(p<0) break;
        idx[p]++;
        for(int m=p+1;m<K;m++) idx[m]=idx[m-1]+1;
    }
    return cnt;
}

static u64 rstate=88172645463325252ULL;
static inline u64 xrand(){ rstate^=rstate<<13; rstate^=rstate>>7; rstate^=rstate<<17; return rstate; }
static inline u64 randmod(){ return xrand()%Q; }

int main(int argc, char** argv){
    if(argc<5){ fprintf(stderr,"usage: q n k a [seed restarts hill mode...]\n"); return 1; }
    Q=strtoull(argv[1],0,10); N=atoi(argv[2]); K=atoi(argv[3]); A=atoi(argv[4]);
    u64 seed = argc>5? strtoull(argv[5],0,10):12345;
    int restarts = argc>6? atoi(argv[6]):200;
    int hill = argc>7? atoi(argv[7]):40;
    const char* mode = argc>8? argv[8]:"search";
    rstate = seed? seed : 1;
    find_sub(Q,N);
    // hash set sized ~ C(n,k)*1.3 but cap at something; use 2^24
    size_t cap = 1; while(cap < 4000000) cap<<=1; cap<<=1;
    hs_init(&GHS, cap);

    if(strcmp(mode,"count")==0){
        u64 w[64];
        for(int i=0;i<N;i++) w[i]=strtoull(argv[9+i],0,10)%Q;
        long c=count_list(w);
        printf("%ld\n", c);
        return 0;
    }

    // search: random + monomial + cluster + hillclimb
    u64 bestw[64]; long best=-1;
    u64 w[64];
    // monomials
    for(int e=K; e<=3*N; e++){
        for(int i=0;i<N;i++) w[i]=powm(SUB[i], e);
        long c=count_list(w);
        if(c>best){ best=c; memcpy(bestw,w,sizeof(u64)*N); }
        if(e>K+8 && e<2*N) e=2*N-1; // skip middle monomials
    }
    // random
    for(int r=0;r<restarts;r++){
        for(int i=0;i<N;i++) w[i]=randmod();
        long c=count_list(w);
        if(c>best){ best=c; memcpy(bestw,w,sizeof(u64)*N); }
    }
    // cluster: plurality of L random codewords (small L due to huge field rarely helps, but try)
    // build pool of candidate codeword value-vectors for hillclimb
    int POOL=96; u64 (*pool)[64]=malloc(sizeof(u64[64])*POOL);
    for(int p=0;p<POOL;p++){
        u64 coeff[16]; for(int j=0;j<K;j++) coeff[j]=randmod();
        for(int i=0;i<N;i++){ u64 v=0,xp=1; for(int j=0;j<K;j++){ v=addm(v,mulm(coeff[j],xp)); xp=mulm(xp,SUB[i]); } pool[p][i]=v; }
    }
    for(int Lc=0; Lc<8; Lc++){
        int L = (Lc<4)? (3+Lc) : (8<<(Lc-4)); if(L>4*N)L=4*N;
        for(int rep=0; rep<6; rep++){
            // plurality over L random codewords
            for(int i=0;i<N;i++){
                // gather L values, pick mode (small L: O(L^2))
                u64 vals[300];
                for(int l=0;l<L;l++){ vals[l]=pool[(xrand()% (u64)POOL)][i]; }
                u64 bestv=vals[0]; int bestc=0;
                for(int a=0;a<L;a++){ int c2=0; for(int b=0;b<L;b++) if(vals[b]==vals[a])c2++; if(c2>bestc){bestc=c2;bestv=vals[a];} }
                w[i]=bestv;
            }
            long c=count_list(w);
            if(c>best){ best=c; memcpy(bestw,w,sizeof(u64)*N); }
        }
    }
    // hillclimb from bestw
    memcpy(w,bestw,sizeof(u64)*N);
    long cur=count_list(w);
    for(int it=0; it<hill; it++){
        int improved=0;
        // random order
        int ord[64]; for(int i=0;i<N;i++)ord[i]=i;
        for(int i=N-1;i>0;i--){ int j=xrand()%(i+1); int tmp=ord[i];ord[i]=ord[j];ord[j]=tmp; }
        for(int oi=0; oi<N; oi++){
            int i=ord[oi];
            u64 oldv=w[i]; u64 bv=oldv; long bs=cur;
            for(int p=0;p<POOL;p++){
                u64 vv=pool[p][i]; if(vv==w[i])continue;
                w[i]=vv; long s=count_list(w);
                if(s>bs){ bs=s; bv=vv; }
            }
            w[i]=bv; if(bv!=oldv){ cur=bs; improved=1; }
        }
        if(cur>best){ best=cur; memcpy(bestw,w,sizeof(u64)*N); }
        if(!improved){ // kick
            for(int t=0;t<2;t++){ int j=xrand()%N; w[j]=randmod(); }
            cur=count_list(w);
        }
    }
    printf("BEST_LIST %ld\nWORD", best);
    for(int i=0;i<N;i++) printf(" %llu",(unsigned long long)bestw[i]);
    printf("\n");
    free(pool);
    return 0;
}
