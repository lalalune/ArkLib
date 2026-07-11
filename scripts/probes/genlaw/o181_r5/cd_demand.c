/* cd_demand.c  — independent C recount of the CensusDomination DEMAND side
 * (#alignable a-sets and #bad scalars) at the exact pin k_c=(r-2)m+1, a0=rm+1,
 * m=1, n configurable. Faithful BabyBear prime p=2013265921 (p^2 >> C(n,a)).
 *
 * INDEPENDENT METHOD (deliberately different from the o165 Python, which uses
 * interpolation-coefficient Gaussian elimination):  here Aligned is tested via
 * the GROUND-TRUTH bordered-Vandermonde residual determinant (OwnershipBound.lean
 * L48 / UniversalAlignmentLaw.lean L178):
 *   residual(dom,k,t,y) = det of the (k+1)x(k+1) matrix whose row a is
 *      [ x_{t_a}^0, x_{t_a}^1, ..., x_{t_a}^{k-1}, y(x_{t_a}) ].
 *   A set S is Aligned with scalar gamma iff for EVERY (k+1)-subtuple t in S:
 *      residual(u0,t) + gamma*residual(u1,t) = 0.
 *   Non-degenerate: some t has NOT(residual u0 = 0 AND residual u1 = 0).
 *   gamma (the "bad scalar") = -residual(u0,t)/residual(u1,t) for any t with
 *   residual(u1,t)!=0; all such t must give the SAME gamma (else not aligned).
 *
 * #alignable = #{ a-subsets S : aligned & non-degenerate }.
 * #bad       = #{ distinct gamma pinned by some alignable non-degenerate S }.
 * Calibration: #alignable, #bad must be <= packing bound C(n,a)/(a+1).
 *
 * modes:
 *   kkh   n           full deep-band sweep r=2.. of the canonical KKH26 stack
 *                     (u0=x^{rm}, u1=x^{(r-1)m}) at deepest band a0=rm+1.
 *   ceil  n           same but at the CEILING band a=rm (validation regime).
 *   mono  n r         worst-case monomial-pair search at deep band a0=rm+1.
 *   one   n r e f a   single stack u0=x^e,u1=x^f, band a, print align+bad.
 * usage: cd_demand mode args...
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint32_t u32;
typedef uint64_t u64;

static const u64 P = 2013265921ULL; /* BabyBear, p-1 = 15*2^27 */

static inline u32 mulm(u32 a, u32 b){ return (u32)((u64)a*b % P); }
static inline u32 addm(u32 a, u32 b){ u64 t=(u64)a+b; return t>=P?(u32)(t-P):(u32)t; }
static inline u32 subm(u32 a, u32 b){ return a>=b? a-b : (u32)((u64)a+P-b); }
static u32 powm(u32 a, u64 e){ u64 r=1,b=a%P; while(e){ if(e&1) r=r*b%P; b=b*b%P; e>>=1; } return (u32)r; }
static inline u32 invm(u32 a){ return powm(a, P-2); }

static int N;            /* domain size */
static u32 dom[64];      /* mu_n */
static u32 U0[64], U1[64];

/* primitive n-th root of unity, dom[i] = g^i, g of exact order n */
static void make_dom(int n){
    N = n;
    u64 e = (P-1)/n;
    for(u32 c=2; c<300; c++){
        u32 h = powm(c, e);
        if(powm(h, n)==1 && powm(h, n/2)!=1){
            u32 cur=1;
            for(int i=0;i<n;i++){ dom[i]=cur; cur=mulm(cur,h); }
            return;
        }
    }
    fprintf(stderr,"no root of order %d\n", n); exit(1);
}

/* determinant mod P of an mxm matrix (row-major), destroys the buffer */
static u32 detm(u32 *M, int m){
    u32 det = 1;
    for(int col=0; col<m; col++){
        int piv=-1;
        for(int rr=col; rr<m; rr++) if(M[rr*m+col]!=0){ piv=rr; break; }
        if(piv<0) return 0;
        if(piv!=col){
            for(int c=0;c<m;c++){ u32 tmp=M[piv*m+c]; M[piv*m+c]=M[col*m+c]; M[col*m+c]=tmp; }
            det = (det==0)?0:subm(0,det);
        }
        det = mulm(det, M[col*m+col]);
        u32 inv = invm(M[col*m+col]);
        for(int rr=col+1; rr<m; rr++){
            if(M[rr*m+col]!=0){
                u32 f = mulm(M[rr*m+col], inv);
                for(int c=col;c<m;c++)
                    M[rr*m+c] = subm(M[rr*m+c], mulm(f, M[col*m+c]));
            }
        }
    }
    return det;
}

/* bordered-Vandermonde residual for a (k+1)-tuple t[0..k], witness y[] */
static u32 residual(int k, const int *t, const u32 *y){
    int m = k+1;
    u32 M[8*8];
    for(int a=0;a<m;a++){
        for(int b=0;b<k;b++) M[a*m+b] = powm(dom[t[a]], b);
        M[a*m+k] = y[t[a]];
    }
    return detm(M, m);
}

/* enumerate (k+1)-subsets of S (given as idx[0..a-1]) via combinations index */
/* We test Aligned: iterate all (k+1)-subsets of the a-set, derive gamma.
 * Returns 1 if aligned & nondeg, sets *gam to the bad scalar (valid iff some
 * residual(u1)!=0). If aligned but all residual(u1)==0 then it cannot pin a
 * unique gamma from u1; such sets are degenerate-for-bad-scalar (still counted
 * in alignable if nondeg via u0). */
static int aligned_set(int k, const int *Sidx, int a, u32 *gam_out, int *has_gam){
    int comb[8];
    for(int i=0;i<=k;i++) comb[i]=i;     /* indices into Sidx */
    int gam_set=0; u32 gam=0; int nondeg=0; int any_u1=0;
    while(1){
        int t[8];
        for(int i=0;i<=k;i++) t[i] = Sidx[comb[i]];
        u32 r0 = residual(k, t, U0);
        u32 r1 = residual(k, t, U1);
        if(r0 || r1) nondeg=1;
        if(r1==0){
            if(r0!=0) return 0;          /* 0 + gamma*0 = r0 != 0 impossible */
        } else {
            any_u1=1;
            u32 g = mulm(subm(0,r0), invm(r1));   /* gamma = -r0/r1 */
            if(!gam_set){ gam=g; gam_set=1; }
            else if(gam!=g) return 0;
        }
        /* next (k+1)-subset */
        int i=k;
        while(i>=0 && comb[i]==a-(k+1)+i) i--;
        if(i<0) break;
        comb[i]++;
        for(int j=i+1;j<=k;j++) comb[j]=comb[j-1]+1;
    }
    if(!nondeg) return 0;
    *has_gam = any_u1;
    if(any_u1) *gam_out = gam;
    return 1;
}

/* hashed set of distinct gamma (bad scalars). Open addressing, size 1<<20. */
#define HBITS 20
#define HSZ (1u<<HBITS)
static u32 *htab; static int hused;
static void hreset(){ if(!htab) htab=malloc(HSZ*sizeof(u32)); memset(htab,0xff,HSZ*sizeof(u32)); hused=0; }
static void hadd(u32 v){
    u32 key = v==0xffffffffu ? 0 : v;   /* avoid sentinel collision (gamma<P so fine) */
    u32 h = (u32)(((u64)key*2654435761u)>>(32-HBITS)) & (HSZ-1);
    while(htab[h]!=0xffffffffu){ if(htab[h]==key) return; h=(h+1)&(HSZ-1); }
    htab[h]=key; hused++;
}

/* count alignable + bad over all a-subsets of [N], for current U0,U1, pin (k,a) */
static void count_band(int k, int a, u64 *n_align, u64 *n_bad){
    hreset();
    u64 al=0;
    int idx[40];
    for(int i=0;i<a;i++) idx[i]=i;
    while(1){
        u32 gam; int hg;
        if(aligned_set(k, idx, a, &gam, &hg)){
            al++;
            if(hg) hadd(gam);
        }
        int i=a-1;
        while(i>=0 && idx[i]==N-a+i) i--;
        if(i<0) break;
        idx[i]++;
        for(int j=i+1;j<a;j++) idx[j]=idx[j-1]+1;
    }
    *n_align=al; *n_bad=(u64)hused;
}

static u64 binom(int n, int r){
    if(r<0||r>n) return 0;
    if(r>n-r) r=n-r;
    u64 v=1; for(int i=0;i<r;i++){ v=v*(n-i)/(i+1); } return v;
}

int main(int argc, char**argv){
    if(argc<3){ fprintf(stderr,"usage: %s mode n [args]\n",argv[0]); return 1; }
    const char*mode=argv[1];
    int n=atoi(argv[2]);
    make_dom(n);

    if(!strcmp(mode,"kkh") || !strcmp(mode,"ceil")){
        int ceil_band = !strcmp(mode,"ceil");
        printf("=== [COMPUTED] KKH26 canonical stack u0=x^{rm},u1=x^{(r-1)m}, n=%d, %s band, residual-det kernel ===\n",
               n, ceil_band?"CEILING a=rm":"DEEP a0=rm+1");
        printf("%3s %3s %4s %10s %11s %9s %9s %8s %s\n","r","kc","a","C(n,a)","#alignable","#badscal","K","pack","ok");
        for(int r=2; r<=n/2; r++){
            int kc=(r-2)+1;                 /* m=1 */
            int a = ceil_band ? r : r+1;
            for(int i=0;i<n;i++){ U0[i]=powm(dom[i], r); U1[i]=powm(dom[i], r-1); }
            u64 al,bad; count_band(kc, a, &al, &bad);
            u64 K=(1ULL<<r)*binom(n/2,r);
            u64 Cna=binom(n,a); u64 pack=Cna/(a+1);
            int ok = (al<=K) && (bad<=K) && (al<=Cna) && (bad<=pack || ceil_band);
            printf("%3d %3d %4d %10llu %11llu %9llu %9llu %8llu %s\n",
                   r,kc,a,(unsigned long long)Cna,(unsigned long long)al,
                   (unsigned long long)bad,(unsigned long long)K,(unsigned long long)pack,
                   ok?"OK":"!!");
            fflush(stdout);
        }
    } else if(!strcmp(mode,"mono")){
        int r=atoi(argv[3]);
        int kc=(r-2)+1, a0=r+1;
        u64 K=(1ULL<<r)*binom(n/2,r);
        u64 pack=binom(n,a0)/(a0+1);
        u64 best_al=0,best_bad=0; int be=0,bf=0, be2=0,bf2=0;
        printf("=== [MEASURED-FAITHFUL] worst-case MONOMIAL-PAIR search, n=%d r=%d deep band a0=%d, residual-det kernel ===\n",n,r,a0);
        for(int e=0;e<n;e++) for(int f=0;f<n;f++){
            if(e==f) continue;
            for(int i=0;i<n;i++){ U0[i]=powm(dom[i],e); U1[i]=powm(dom[i],f); }
            u64 al,bad; count_band(kc,a0,&al,&bad);
            if(bad>best_bad){ best_bad=bad; be=e; bf=f; }
            if(al>best_al){ best_al=al; be2=e; bf2=f; }
        }
        printf("WORST #bad-scalar = %llu (mono x^%d,x^%d)   K=%llu  pack=%llu  bad<=K? %s  bad<=pack? %s\n",
               (unsigned long long)best_bad,be,bf,(unsigned long long)K,(unsigned long long)pack,
               best_bad<=K?"YES":"NO", best_bad<=pack?"YES":"NO");
        printf("WORST #alignable  = %llu (mono x^%d,x^%d)   K=%llu  pack=%llu  align<=K? %s  align<=pack? %s\n",
               (unsigned long long)best_al,be2,bf2,(unsigned long long)K,(unsigned long long)pack,
               best_al<=K?"YES":"NO", best_al<=pack?"YES":"NO");
    } else if(!strcmp(mode,"wide")){
        /* worst-case over a BROAD stack family: all monomial pairs + random +
         * structured P(x^d) + random-deg<a0 codeword pairs. Deep band a0=rm+1. */
        int r=atoi(argv[3]);
        int ntrials = argc>4 ? atoi(argv[4]) : 200;
        unsigned seed = argc>5 ? (unsigned)atoi(argv[5]) : 1234567u;
        int kc=(r-2)+1, a0=r+1;
        u64 K=(1ULL<<r)*binom(n/2,r);
        u64 pack=binom(n,a0)/(a0+1);
        u64 best_bad=0; char bn[64]="";
        u64 best_al=0;  char an[64]="";
        /* monomial pairs */
        for(int e=0;e<n;e++) for(int f=0;f<n;f++){
            if(e==f) continue;
            for(int i=0;i<n;i++){ U0[i]=powm(dom[i],e); U1[i]=powm(dom[i],f); }
            u64 al,bad; count_band(kc,a0,&al,&bad);
            if(bad>best_bad){ best_bad=bad; snprintf(bn,64,"mono x^%d,x^%d",e,f); }
            if(al>best_al){ best_al=al; snprintf(an,64,"mono x^%d,x^%d",e,f); }
        }
        /* random + structured */
        u64 st=seed;
        u32 (*nextr)(u64*) ; (void)nextr;
        for(int tr=0; tr<ntrials; tr++){
            for(int i=0;i<n;i++){
                st = st*6364136223846793005ULL + 1442695040888963407ULL;
                U0[i]=(u32)((st>>17)%P);
                st = st*6364136223846793005ULL + 1442695040888963407ULL;
                U1[i]=(u32)((st>>17)%P);
            }
            u64 al,bad; count_band(kc,a0,&al,&bad);
            if(bad>best_bad){ best_bad=bad; snprintf(bn,64,"random#%d",tr); }
            if(al>best_al){ best_al=al; snprintf(an,64,"random#%d",tr); }
        }
        /* structured: u0 = low-degree poly in x^d, u1 = x^{r-1} */
        for(int d=2; d<=8; d*=2){
            for(int tr=0; tr<ntrials/2; tr++){
                int deg = 1 + (int)((st>>13)%(n/d));
                st = st*6364136223846793005ULL + 1442695040888963407ULL;
                u32 cf[64];
                for(int c=0;c<=deg;c++){ st = st*6364136223846793005ULL + 1442695040888963407ULL; cf[c]=(u32)((st>>17)%P); }
                for(int i=0;i<n;i++){
                    u32 xd=powm(dom[i],d), acc=0, xpow=1;
                    for(int c=0;c<=deg;c++){ acc=addm(acc, mulm(cf[c],xpow)); xpow=mulm(xpow,xd); }
                    U0[i]=acc; U1[i]=powm(dom[i],r-1);
                }
                u64 al,bad; count_band(kc,a0,&al,&bad);
                if(bad>best_bad){ best_bad=bad; snprintf(bn,64,"P(x^%d)#%d",d,tr); }
                if(al>best_al){ best_al=al; snprintf(an,64,"P(x^%d)#%d",d,tr); }
            }
        }
        printf("=== [MEASURED-FAITHFUL] WIDE worst-case search, n=%d r=%d deep a0=%d (mono+rand+struct, %d trials) ===\n",n,r,a0,ntrials);
        printf("WORST #bad-scalar = %llu (%s)   K=%llu  pack=%llu  bad<=K? %s  bad<=pack? %s\n",
               (unsigned long long)best_bad,bn,(unsigned long long)K,(unsigned long long)pack,
               best_bad<=K?"YES":"NO", best_bad<=pack?"YES":"NO");
        printf("WORST #alignable  = %llu (%s)   K=%llu  pack=%llu  align<=K? %s  align<=pack? %s\n",
               (unsigned long long)best_al,an,(unsigned long long)K,(unsigned long long)pack,
               best_al<=K?"YES":"NO", best_al<=pack?"YES":"NO");
    } else if(!strcmp(mode,"one")){
        int r=atoi(argv[3]), e=atoi(argv[4]), f=atoi(argv[5]), a=atoi(argv[6]);
        int kc=(r-2)+1;
        for(int i=0;i<n;i++){ U0[i]=powm(dom[i],e); U1[i]=powm(dom[i],f); }
        u64 al,bad; count_band(kc,a,&al,&bad);
        u64 K=(1ULL<<r)*binom(n/2,r);
        printf("n=%d r=%d kc=%d a=%d stack=(x^%d,x^%d): #align=%llu #bad=%llu K=%llu C(n,a)=%llu pack=%llu\n",
               n,r,kc,a,e,f,(unsigned long long)al,(unsigned long long)bad,(unsigned long long)K,
               (unsigned long long)binom(n,a),(unsigned long long)(binom(n,a)/(a+1)));
    } else { fprintf(stderr,"unknown mode %s\n",mode); return 1; }
    return 0;
}
