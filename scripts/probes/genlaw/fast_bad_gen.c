/* fast_bad_gen.c — generalize fast_bad.c (r=5) to ARBITRARY r.
 * Counts #distinct bad line-cut scalars gamma for the deep-band r-census on the subgroup mu_n
 * (n a 2-power), line (e,f), agreement a = r+1.
 *
 * Bad-scalar definition (identical to the proven r=5 kernel, just size-generalized):
 *   For each (r+1)-subset T of the n domain points, and each of the (r+1) "drops" of one point
 *   (leaving an r-point set t), let de = DD_t(x^e), df = DD_t(x^f) be order-(r-1) divided
 *   differences. The cut requires de + gamma*df = 0 for EVERY drop, single-valued; if so and
 *   nondegenerate, gamma is bad. Count distinct bad gamma over all (r+1)-subsets.
 *
 * Modes:
 *   line:  ./a.out n r e f        -> #bad_r on that one line
 *   sweep: ./a.out n r sweep       -> max_{(e,f)} #bad_r + argmax (feasible only small n)
 *
 * Prize budget for the deep-band census is K = 2^r * C(n/2, r) (confirmed against r=5 data).
 * This program reports #bad and lets the caller compare to K, K/2.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t u32; typedef uint64_t u64;
static const u64 P = 2013265921ULL;               /* BabyBear: 15*2^27+1, n | p-1 for n up to 2^27 */
static inline u32 mulm(u32 a, u32 b){ return (u32)((u64)a*b % P); }
static inline u32 addm(u32 a, u32 b){ u64 t=(u64)a+b; return t>=P?(u32)(t-P):(u32)t; }
static inline u32 subm(u32 a, u32 b){ return a>=b ? a-b : (u32)((u64)a+P-b); }
static u32 powm(u32 a, u64 e){ u64 r=1,b=a%P; while(e){ if(e&1)r=r*b%P; b=b*b%P; e>>=1; } return (u32)r; }
static inline u32 invm(u32 a){ return powm(a, P-2); }

static int N; static u32 dom[256], GEN, PE[256], PF[256]; static u32 DINV[256][256];
static void make_dom(int n){
  N=n; u64 e=(P-1)/n;
  for(u32 c=2;c<2000;c++){ u32 h=powm(c,e); if(powm(h,n)==1 && powm(h,n/2)!=1){
    GEN=h; u32 cur=1; for(int i=0;i<n;i++){ dom[i]=cur; cur=mulm(cur,h);} return; } }
  fprintf(stderr,"no generator\n"); exit(1);
}
/* order-(m-1) divided difference of pw over the m points ix[0..m-1] */
static inline u32 dd(const int*ix, int m, const u32*pw){
  u32 acc=0;
  for(int a=0;a<m;a++){ int i=ix[a]; u32 den=1;
    for(int b=0;b<m;b++) if(b!=a) den=mulm(den, DINV[i][ix[b]]);
    acc=addm(acc, mulm(pw[i], den)); }
  return acc;
}
#define HBITS 23                       /* 8M slots (32MB) >> any #bad (n=64,r=6 ~ 1e5); avoids 268MB OOM-segfault */
#define HSZ (1u<<HBITS)
static u32 *htab=NULL; static long NB;
static void hreset(){ if(!htab){ htab=malloc((size_t)HSZ*4); if(!htab){ fprintf(stderr,"malloc failed\n"); exit(2);} } memset(htab,0,(size_t)HSZ*4); NB=0; }
static inline u32 enc(u32 v){ return v+1; }
static int hadd(u32 v){ u32 e=enc(v); u32 h=(u32)(((u64)v*2654435761u)>>(32-HBITS))&(HSZ-1);
  while(htab[h]){ if((htab[h]&0x7fffffffu)==e) return 0; h=(h+1)&(HSZ-1);} htab[h]=e; NB++; return 1; }

/* count #bad gamma for one line (e,f) at offset r; a=r+1. returns NB; sets *has0. */
static long count_bad(int n, int r, int e, int f, int *has0){
  int A=r+1;
  for(int i=0;i<n;i++){ PE[i]=powm(dom[i], (u64)e); PF[i]=powm(dom[i], (u64)f); }
  hreset();
  int idx[16]; for(int i=0;i<A;i++) idx[i]=i;
  u32 de[16], df[16];
  while(1){
    int t[16];
    /* drop 0 and drop 1 first; early-reject the ~99.9% inconsistent subsets via cross-mult */
    { int p=0; for(int q=0;q<A;q++) if(q!=0) t[p++]=idx[q]; de[0]=dd(t,r,PE); df[0]=dd(t,r,PF); }
    { int p=0; for(int q=0;q<A;q++) if(q!=1) t[p++]=idx[q]; de[1]=dd(t,r,PE); df[1]=dd(t,r,PF); }
    int reject = (mulm(de[0],df[1]) != mulm(de[1],df[0]));   /* (de_i,df_i) not parallel */
    if(!reject){
      for(int drop=2; drop<A; drop++){ int p=0; for(int q=0;q<A;q++) if(q!=drop) t[p++]=idx[q];
        de[drop]=dd(t,r,PE); df[drop]=dd(t,r,PF); }
      int nondeg=0, anyf=0;
      for(int i=0;i<A;i++){ if(de[i]||df[i]) nondeg=1; if(df[i]) anyf=1; }
      int ok=1;
      for(int i=0;i<A && ok;i++) for(int j=i+1;j<A;j++)        /* all (de,df) mutually parallel */
        if(mulm(de[i],df[j]) != mulm(de[j],df[i])){ ok=0; break; }
      if(ok && nondeg && anyf){
        int k=0; while(df[k]==0) k++;                          /* a drop with df!=0 exists (anyf) */
        u32 gam=mulm(subm(0,de[k]), invm(df[k]));              /* ONE inverse per accepted subset */
        hadd(gam);
      }
    }
    int i=A-1; while(i>=0 && idx[i]==n-A+i) i--; if(i<0) break;
    idx[i]++; for(int j=i+1;j<A;j++) idx[j]=idx[j-1]+1;
  }
  /* gamma=0 present? */
  { u32 v=0,ec=enc(v); u32 h=(u32)(((u64)v*2654435761u)>>(32-HBITS))&(HSZ-1); int found=0;
    while(htab[h]){ if((htab[h]&0x7fffffffu)==ec){found=1;break;} h=(h+1)&(HSZ-1);} *has0=found; }
  return NB;
}

int main(int argc, char**argv){
  if(argc<4){ fprintf(stderr,"usage: %s n r (e f | sweep)\n", argv[0]); return 1; }
  int n=atoi(argv[1]), r=atoi(argv[2]);
  if(r<2||r>8){ fprintf(stderr,"r in [2,8]\n"); return 1; }
  make_dom(n);
  for(int i=0;i<n;i++) for(int j=0;j<n;j++) if(i!=j) DINV[i][j]=invm(subm(dom[i],dom[j]));
  if(strcmp(argv[3],"sweep")==0 || strcmp(argv[3],"dsweep")==0){
    int donly = (strcmp(argv[3],"dsweep")==0);  /* dsweep: restrict to d=n/2 (gcd(n,e-f)==2) resonance family */
    long best=-1; int be=0,bf=0,bh0=0;
    for(int e=1;e<n;e++) for(int f=1;f<n;f++){ if(e==f) continue;
      if(donly){ int df=((e-f)%n+n)%n; int gg=n,x=df; while(x){int t=gg%x;gg=x;x=t;} if(gg!=2) continue; }
      int h0; long nb=count_bad(n,r,e,f,&h0);
      if(nb>best){ best=nb; be=e; bf=f; bh0=h0; }
    }
    int dd0=( (be-bf)%n+n)%n; int gg=n,x=dd0; while(x){int t=gg%x;gg=x;x=t;} int d=n/gg;
    printf("SWEEP n=%d r=%d a=%d: MAX #bad=%ld at line (e=%d,f=%d) d=%d 0in=%d\n", n,r,r+1,best,be,bf,d,bh0);
  } else {
    int e=atoi(argv[3]), f=atoi(argv[4]); int h0; long nb=count_bad(n,r,e,f,&h0);
    int dd0=((e-f)%n+n)%n; int gg=n,x=dd0; while(x){int t=gg%x;gg=x;x=t;} int d=n/gg;
    printf("n=%d r=%d a=%d line(e=%d,f=%d) d=%d: #bad=%ld 0in=%d\n", n,r,r+1,e,f,d,nb,h0);
  }
  return 0;
}
