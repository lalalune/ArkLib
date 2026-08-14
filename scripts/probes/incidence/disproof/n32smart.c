// n32smart.c — integrated EXACT count + codeword-aware smart hill-climb for n=32.
// One enumeration of all C(n,k) canonical k-subsets yields, per word w:
//   (1) list(w,a) = # near-codewords with agreement >= a,
//   (2) for each coordinate i, a tally of values taken at i by codewords with agreement >= a-1
//       (the "almost-in-list" set), used to pick the best plurality move.
// Smart climb: from a seed word, repeatedly take the single-coordinate change to the most
// promising value (by re-scoring the few top candidates), keeping the move if list grows.
// Each accepted move costs O(1) full enumerations. OpenMP parallel. Exact (canonical dedup).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>

typedef uint64_t u64; typedef __uint128_t u128;
static u64 Q;
static inline u64 mulm(u64 a,u64 b){return (u64)(((u128)a*b)%Q);}
static inline u64 addm(u64 a,u64 b){u64 s=a+b;return s>=Q?s-Q:s;}
static inline u64 subm(u64 a,u64 b){return a>=b?a-b:a+Q-b;}
static u64 powm(u64 a,u64 e){u64 r=1%Q;a%=Q;while(e){if(e&1)r=mulm(r,a);a=mulm(a,a);e>>=1;}return r;}
static inline u64 invm(u64 a){return powm(a,Q-2);}
static int N,K,A;
static u64 SUB[64];
static void find_sub(u64 q,int n){
    for(u64 g=2;g<q;g++){ if(powm(g,n)!=1)continue; int ok=1;
        for(int d=1;d<n;d++){if(n%d==0&&d<n&&powm(g,d)==1){ok=0;break;}}
        if(ok){for(int j=0;j<n;j++)SUB[j]=powm(g,j);return;} }
    fprintf(stderr,"no order-%d\n",n);exit(1);
}
// returns nS (agreement count); fills S[] with agreement indices (ascending); also writes the
// full eval vector into ev[] for the caller (for plurality tallies).
static inline int interp_full(const int*idx,const u64*w,int*S,u64*ev){
    u64 xs[16]; for(int m=0;m<K;m++)xs[m]=SUB[idx[m]];
    u64 dinv[16]; for(int m=0;m<K;m++){u64 d=1;for(int j=0;j<K;j++)if(j!=m)d=mulm(d,subm(xs[m],xs[j]));dinv[m]=invm(d);}
    u64 ys[16]; for(int m=0;m<K;m++)ys[m]=w[idx[m]];
    int nS=0;
    for(int t=0;t<N;t++){ u64 xt=SUB[t],v=0;
        for(int m=0;m<K;m++){u64 num=1;for(int j=0;j<K;j++)if(j!=m)num=mulm(num,subm(xt,xs[j]));v=addm(v,mulm(mulm(num,dinv[m]),ys[m]));}
        ev[t]=v; if(v==w[t])S[nS++]=t; }
    return nS;
}
static inline int is_canon(const int*idx,const int*S,int nS){ if(nS<K)return 0; for(int m=0;m<K;m++)if(idx[m]!=S[m])return 0; return 1; }

// Exact list(w,A). (parallel)
static long count_list(const u64*w){
    long total=0;
    #pragma omp parallel reduction(+:total)
    { int S[64],idx[16]; u64 ev[64];
      #pragma omp for schedule(dynamic,1)
      for(int first=0;first<=N-K;first++){
        idx[0]=first; for(int m=1;m<K;m++)idx[m]=first+m;
        while(1){ int nS=interp_full(idx,w,S,ev);
            if(nS>=A&&is_canon(idx,S,nS))total++;
            int p=K-1; while(p>=1&&idx[p]==N-K+p)p--; if(p<1)break; idx[p]++; for(int m=p+1;m<K;m++)idx[m]=idx[m-1]+1; }
      } }
    return total;
}

static u64 rstate=88172645463325252ULL;
static inline u64 xr(){rstate^=rstate<<13;rstate^=rstate>>7;rstate^=rstate<<17;return rstate;}
static inline u64 rmod(){return xr()%Q;}

// gather candidate replacement values for each coordinate from near-codewords (agreement>=A-1):
// for each canonical near-codeword, for each coordinate where it DISAGREES with w, record its value.
// Setting w[i] to such a value can convert agreement A-1 -> A. We collect top candidates per coord.
#define MAXC 4096
typedef struct { u64 val[MAXC]; int cnt[MAXC]; int n; } Tally;
static void tally_add(Tally*T,u64 v){ for(int j=0;j<T->n;j++) if(T->val[j]==v){T->cnt[j]++;return;} if(T->n<MAXC){T->val[T->n]=v;T->cnt[T->n]=1;T->n++;} }

// one enumeration: count list AND build per-coordinate candidate tallies (serial; used between moves)
static long scan(const u64*w, Tally*tal){
    for(int i=0;i<N;i++) tal[i].n=0;
    long total=0; int S[64],idx[16]; u64 ev[64];
    for(int first=0;first<=N-K;first++){
        idx[0]=first; for(int m=1;m<K;m++)idx[m]=first+m;
        while(1){ int nS=interp_full(idx,w,S,ev);
            if(is_canon(idx,S,nS)){
                if(nS>=A) total++;
                else if(nS==A-1){
                    // this near-codeword could be promoted by changing ONE disagreeing coord to ev[t]
                    for(int t=0;t<N;t++) if(ev[t]!=w[t]) tally_add(&tal[t],ev[t]);
                }
            }
            int p=K-1; while(p>=1&&idx[p]==N-K+p)p--; if(p<1)break; idx[p]++; for(int m=p+1;m<K;m++)idx[m]=idx[m-1]+1; }
    }
    return total;
}

int main(int argc,char**argv){
    if(argc<7){fprintf(stderr,"usage: q n k a seed passes [maxcand]\n");return 1;}
    Q=strtoull(argv[1],0,10);N=atoi(argv[2]);K=atoi(argv[3]);A=atoi(argv[4]);
    u64 seed=strtoull(argv[5],0,10); int passes=atoi(argv[6]);
    int MAXCAND=argc>7?atoi(argv[7]):8; if(MAXCAND<1)MAXCAND=1; if(MAXCAND>8)MAXCAND=8;
    rstate=seed?seed:1; find_sub(Q,N);
    u64 w[64];
    // seed word: densest-cluster plurality of L random codewords (L=24)
    int L=24; static u64 cw[64][64];
    for(int l=0;l<L;l++){ u64 cf[16]; for(int j=0;j<K;j++)cf[j]=rmod();
        for(int i=0;i<N;i++){u64 v=0,xp=1;for(int j=0;j<K;j++){v=addm(v,mulm(cf[j],xp));xp=mulm(xp,SUB[i]);}cw[l][i]=v;} }
    for(int i=0;i<N;i++){ u64 vals[64]; for(int l=0;l<L;l++)vals[l]=cw[l][i];
        u64 bv=vals[0];int bc=0; for(int a=0;a<L;a++){int c=0;for(int b=0;b<L;b++)if(vals[b]==vals[a])c++;if(c>bc){bc=c;bv=vals[a];}} w[i]=bv; }
    Tally*tal=malloc(sizeof(Tally)*N);
    long cur=count_list(w);
    fprintf(stderr,"seed cluster list=%ld\n",cur);
    long best=cur; u64 bestw[64]; memcpy(bestw,w,sizeof(u64)*N);
    for(int pass=0; pass<passes; pass++){
        scan(w,tal);                 // build candidate tallies at current w
        int improved=0;
        // try coordinates in descending order of top-candidate count (most promising first)
        for(int i=0;i<N;i++){
            // pick the top few candidate values at coord i
            // simple: find the max-count candidate
            int order[8]; for(int z=0;z<8;z++)order[z]=-1;
            for(int z=0; z<MAXCAND; z++){
                int bidx=-1,bc=-1;
                for(int j=0;j<tal[i].n;j++){ int used=0; for(int y=0;y<z;y++) if(order[y]==j){used=1;break;}
                    if(!used && tal[i].cnt[j]>bc){bc=tal[i].cnt[j];bidx=j;} }
                order[z]=bidx; if(bidx<0)break;
            }
            u64 oldv=w[i]; long bs=cur; u64 bv=oldv;
            for(int z=0; z<MAXCAND && order[z]>=0; z++){
                u64 vv=tal[i].val[order[z]]; if(vv==w[i])continue;
                w[i]=vv; long s=count_list(w);
                if(s>bs){bs=s;bv=vv;}
                w[i]=oldv;
            }
            if(bv!=oldv){ w[i]=bv; cur=bs; improved=1;
                if(cur>best){best=cur;memcpy(bestw,w,sizeof(u64)*N);} }
        }
        fprintf(stderr,"pass %d list=%ld best=%ld\n",pass,cur,best);
        if(!improved){ // random kick
            for(int t=0;t<2;t++){int j=xr()%N;w[j]=rmod();} cur=count_list(w);
        }
    }
    printf("BEST_LIST %ld\nWORD",best);
    for(int i=0;i<N;i++)printf(" %llu",(unsigned long long)bestw[i]);
    printf("\n");
    free(tal);
    return 0;
}
