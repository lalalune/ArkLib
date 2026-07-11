// maxlist32mp.c — OpenMP-parallel EXACT RS list counter, canonical-subset dedup (no hashset).
// list(w,a) = #{distinct deg<k polys agreeing with w on >= a points}.
// Count each codeword once via its LEX-MIN agreement k-subset: enumerate k-subsets idx; interpolate;
// compute full agreement set S; count iff idx equals the k smallest indices of S (and |S|>=a).
// Fully parallel over the first index. Validated against Python/maxlist32 (hashset version).
//
// Usage:
//   maxlist32mp q n k a count W0..W{n-1}     -> exact list(w,a)
//   maxlist32mp q n k a search seed restarts hill  -> search, prints BEST_LIST + WORD
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>

typedef uint64_t u64;
typedef __uint128_t u128;
static u64 Q;
static inline u64 mulm(u64 a,u64 b){ return (u64)(((u128)a*b)%Q); }
static inline u64 addm(u64 a,u64 b){ u64 s=a+b; return s>=Q? s-Q:s; }
static inline u64 subm(u64 a,u64 b){ return a>=b? a-b : a+Q-b; }
static u64 powm(u64 a,u64 e){ u64 r=1%Q; a%=Q; while(e){ if(e&1)r=mulm(r,a); a=mulm(a,a); e>>=1;} return r; }
static inline u64 invm(u64 a){ return powm(a,Q-2); }

static int N,K,A;
static u64 SUB[64];
static void find_sub(u64 q,int n){
    for(u64 g=2; g<q; g++){
        if(powm(g,n)!=1) continue; int ok=1;
        for(int d=1; d<n; d++){ if(n%d==0 && d<n && powm(g,d)==1){ok=0;break;} }
        if(ok){ for(int j=0;j<n;j++) SUB[j]=powm(g,j); return; }
    }
    fprintf(stderr,"no order-%d elt\n",n); exit(1);
}

// interpolate deg<K poly through (SUB[idx[m]], w[idx[m]]); return agreement count and fill agreement
// indices into S[] (sorted ascending since t loops ascending). nS = |S|.
static inline int interp_agree(const int* idx, const u64* w, int* S){
    u64 xs[16]; for(int m=0;m<K;m++) xs[m]=SUB[idx[m]];
    u64 dinv[16];
    for(int m=0;m<K;m++){ u64 d=1; for(int j=0;j<K;j++) if(j!=m) d=mulm(d,subm(xs[m],xs[j])); dinv[m]=invm(d); }
    u64 ys[16]; for(int m=0;m<K;m++) ys[m]=w[idx[m]];
    int nS=0;
    for(int t=0;t<N;t++){
        u64 xt=SUB[t], v=0;
        for(int m=0;m<K;m++){
            u64 num=1; for(int j=0;j<K;j++) if(j!=m) num=mulm(num,subm(xt,xs[j]));
            v=addm(v, mulm(mulm(num,dinv[m]),ys[m]));
        }
        if(v==w[t]) S[nS++]=t;
    }
    return nS;
}

// is idx the lex-min k-subset of agreement set S (i.e. the k smallest elements of S)?
static inline int is_canonical(const int* idx, const int* S, int nS){
    if(nS<K) return 0;
    for(int m=0;m<K;m++) if(idx[m]!=S[m]) return 0;
    return 1;
}

static long count_list(const u64* w){
    long total=0;
    #pragma omp parallel reduction(+:total)
    {
        int S[64];
        int idx[16];
        #pragma omp for schedule(dynamic,1)
        for(int first=0; first<=N-K; first++){
            // enumerate all k-subsets whose smallest element is 'first'
            idx[0]=first;
            // init remaining
            for(int m=1;m<K;m++) idx[m]=first+m;
            while(1){
                int nS=interp_agree(idx,w,S);
                if(nS>=A && is_canonical(idx,S,nS)) total++;
                // advance idx[1..K-1] keeping idx[0]=first
                int p=K-1;
                while(p>=1 && idx[p]==N-K+p) p--;
                if(p<1) break;
                idx[p]++;
                for(int m=p+1;m<K;m++) idx[m]=idx[m-1]+1;
            }
        }
    }
    return total;
}

static u64 rstate=88172645463325252ULL;
static inline u64 xrand(){ rstate^=rstate<<13; rstate^=rstate>>7; rstate^=rstate<<17; return rstate; }
static inline u64 randmod(){ return xrand()%Q; }

int main(int argc,char**argv){
    if(argc<6){ fprintf(stderr,"usage: q n k a mode ...\n"); return 1; }
    Q=strtoull(argv[1],0,10); N=atoi(argv[2]); K=atoi(argv[3]); A=atoi(argv[4]);
    const char* mode=argv[5];
    find_sub(Q,N);
    if(strcmp(mode,"count")==0){
        u64 w[64]; for(int i=0;i<N;i++) w[i]=strtoull(argv[6+i],0,10)%Q;
        printf("%ld\n", count_list(w)); return 0;
    }
    // search
    u64 seed=argc>6?strtoull(argv[6],0,10):12345;
    int restarts=argc>7?atoi(argv[7]):60;
    int hill=argc>8?atoi(argv[8]):20;
    rstate=seed?seed:1;
    u64 bestw[64]; long best=-1; u64 w[64];
    // monomials (key algebraic baselines incl. dilation-eigenvector far monomials)
    for(int e=K;e<=3*N;e++){
        for(int i=0;i<N;i++) w[i]=powm(SUB[i],e);
        long c=count_list(w);
        if(c>best){best=c;memcpy(bestw,w,sizeof(u64)*N);}
        fprintf(stderr,"mono^%d list=%ld\n",e,c);
        if(e>K+6 && e<2*N-1) e=2*N-2;
    }
    // candidate pool for clusters & hillclimb
    int POOL=64; static u64 pool[64][64];
    for(int p=0;p<POOL;p++){ u64 cf[16]; for(int j=0;j<K;j++) cf[j]=randmod();
        for(int i=0;i<N;i++){ u64 v=0,xp=1; for(int j=0;j<K;j++){v=addm(v,mulm(cf[j],xp));xp=mulm(xp,SUB[i]);} pool[p][i]=v; } }
    // random restarts
    for(int r=0;r<restarts;r++){ for(int i=0;i<N;i++) w[i]=randmod(); long c=count_list(w);
        if(c>best){best=c;memcpy(bestw,w,sizeof(u64)*N);} }
    // cluster plurality
    for(int Lc=0;Lc<7;Lc++){ int L=(Lc<4)?(3+Lc):(8<<(Lc-4)); if(L>4*N)L=4*N;
        for(int rep=0;rep<5;rep++){
            for(int i=0;i<N;i++){ u64 vals[300]; for(int l=0;l<L;l++) vals[l]=pool[xrand()%POOL][i];
                u64 bv=vals[0]; int bc=0; for(int a=0;a<L;a++){int c2=0;for(int b=0;b<L;b++)if(vals[b]==vals[a])c2++; if(c2>bc){bc=c2;bv=vals[a];}} w[i]=bv; }
            long c=count_list(w); if(c>best){best=c;memcpy(bestw,w,sizeof(u64)*N);} } }
    // hillclimb from bestw
    memcpy(w,bestw,sizeof(u64)*N); long cur=count_list(w);
    for(int it=0;it<hill;it++){ int improved=0;
        int ord[64]; for(int i=0;i<N;i++)ord[i]=i;
        for(int i=N-1;i>0;i--){int j=xrand()%(i+1);int t=ord[i];ord[i]=ord[j];ord[j]=t;}
        for(int oi=0;oi<N;oi++){ int i=ord[oi]; u64 oldv=w[i],bv=oldv; long bs=cur;
            for(int p=0;p<POOL;p++){ u64 vv=pool[p][i]; if(vv==w[i])continue; w[i]=vv; long s=count_list(w); if(s>bs){bs=s;bv=vv;} }
            w[i]=bv; if(bv!=oldv){cur=bs;improved=1;} }
        if(cur>best){best=cur;memcpy(bestw,w,sizeof(u64)*N);}
        fprintf(stderr,"hill it=%d cur=%ld best=%ld\n",it,cur,best);
        if(!improved){ for(int t=0;t<2;t++){int j=xrand()%N;w[j]=randmod();} cur=count_list(w); }
    }
    printf("BEST_LIST %ld\nWORD",best);
    for(int i=0;i<N;i++) printf(" %llu",(unsigned long long)bestw[i]);
    printf("\n");
    return 0;
}
