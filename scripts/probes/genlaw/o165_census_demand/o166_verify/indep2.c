/* indep.c - INDEPENDENT re-implementation of the CensusDomination demand side.
 * DELIBERATELY DIFFERENT method from cd_demand.c:
 *  - determinant via cofactor/Laplace expansion along the VALUE column
 *    (so residual = sum_a (-1)^(a+k) * y(x_{t_a}) * Vandermonde-minor),
 *    NOT Gaussian elimination.
 *  - Aligned consistency tested by CROSS-MULTIPLICATION r0_i * r1_j == r0_j * r1_i
 *    over all pairs of (k+1)-subtuples (no modular inverse in the test path);
 *    inverse used ONLY to materialize the distinct gamma for the hash.
 *  - independent root-of-unity search, independent combination enumeration.
 * Faithful BabyBear p = 2013265921. Pin k=(r-2)+1, a0=r+1 (m=1).
 *
 * modes:
 *   kkh  n        : KKH26 canonical u0=x^r u1=x^{r-1}, deep band a0=r+1, sweep r
 *   ceil n        : KKH26 canonical, CEILING band a=r, sweep r
 *   one  n r e f a : single monomial stack u0=x^e u1=x^f at band a
 *   mono n r      : worst-case monomial-pair search at deep band a0=r+1
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t u32; typedef uint64_t u64;
static u64 P=2013265921ULL;
static inline u32 mul(u32 a,u32 b){return (u32)((u64)a*b%P);}
static inline u32 add(u32 a,u32 b){u64 t=(u64)a+b;return t>=P?(u32)(t-P):(u32)t;}
static inline u32 sub(u32 a,u32 b){return a>=b?a-b:(u32)((u64)a+P-b);}
static u32 pw(u32 a,u64 e){u64 r=1,b=a%P;while(e){if(e&1)r=r*b%P;b=b*b%P;e>>=1;}return (u32)r;}
static inline u32 inv(u32 a){return pw(a,P-2);}
static int N; static u32 dom[64],U0[64],U1[64];

/* independent generator search: smallest c whose ((P-1)/n) power has order exactly n */
static void mkdom(int n){
    N=n; u64 e=(P-1)/n;
    for(u32 c=2;c<1000;c++){
        u32 h=pw(c,e);
        int ord_ok = (pw(h,n)==1);
        if(!ord_ok) continue;
        /* check order is EXACTLY n: h^(n/q)!=1 for prime q|n. n is power of 2 => q=2 */
        if(pw(h,n/2)==1) continue;
        u32 cur=1; for(int i=0;i<n;i++){dom[i]=cur;cur=mul(cur,h);} return;
    }
    fprintf(stderr,"no root order %d\n",n);exit(1);
}
/* Vandermonde determinant of the (k)x(k) matrix rows=subset of t (drop row d),
 * cols x^0..x^{k-1}. Closed form: product_{i<j}(x_j - x_i). */
static u32 vander(const u32 *xs,int k){
    u32 d=1;
    for(int i=0;i<k;i++) for(int j=i+1;j<k;j++) d=mul(d, sub(xs[j],xs[i]));
    return d;
}
/* residual via Laplace expansion along the VALUE column (last col, index k).
 * borderedMatrix row a: [x^0,...,x^{k-1}, y_a]; det = sum_a (-1)^(a+k) y_a * M_a,
 * where M_a = det of Vandermonde on rows != a, cols 0..k-1. */
static u32 residual(int k,const int *t,const u32 *y){
    int m=k+1; /* rows 0..k */
    u32 xfull[8]; for(int a=0;a<m;a++) xfull[a]=dom[t[a]];
    u32 acc=0;
    for(int a=0;a<m;a++){
        u32 minor_xs[8]; int c=0;
        for(int b=0;b<m;b++) if(b!=a) minor_xs[c++]=xfull[b];
        u32 minor=vander(minor_xs,k); /* (k)x(k) vandermonde */
        u32 term=mul(y[t[a]],minor);
        /* sign (-1)^(a + k): col index is k */
        if(((a+k)&1)) acc=sub(acc,term); else acc=add(acc,term);
    }
    return acc;
}
/* test Aligned over all (k+1)-subtuples of S(idx[0..a-1]); cross-mult consistency.
 * returns 1 if aligned+nondeg, *gam set & *hg=1 if some r1!=0. */
static int aligned_set(int k,const int *S,int a,u32 *gam,int *hg){
    int c[8]; for(int i=0;i<=k;i++) c[i]=i;
    /* collect residual pairs; require r0_i*r1_j==r0_j*r1_i for all i,j, and not both 0 */
    /* stream pairwise against a stored reference (first nondeg subtuple) */
    int have_ref=0; u32 ref0=0,ref1=0; int nondeg=0,any1=0;
    while(1){
        int t[8]; for(int i=0;i<=k;i++) t[i]=S[c[i]];
        u32 r0=residual(k,t,U0), r1=residual(k,t,U1);
        if(r0||r1) nondeg=1;
        if(r1) any1=1;
        if(have_ref){
            /* r0*ref1 must equal ref0*r1 (cross-mult of the two ratios) */
            if(mul(r0,ref1)!=mul(ref0,r1)) return 0;
        } else if(r0||r1){
            ref0=r0; ref1=r1; have_ref=1;
        }
        int i=k; while(i>=0 && c[i]==a-(k+1)+i) i--;
        if(i<0) break; c[i]++; for(int j=i+1;j<=k;j++) c[j]=c[j-1]+1;
    }
    if(!nondeg) return 0;
    *hg=any1;
    if(any1) *gam=mul(sub(0,ref0), inv(ref1)); /* but ref1 might be 0 if first ref had r1=0 */
    /* fix: if ref1==0 we must find a subtuple with r1!=0 to pin gamma. re-scan once. */
    if(any1 && ref1==0){
        for(int i=0;i<=k;i++) c[i]=i;
        while(1){
            int t[8]; for(int i=0;i<=k;i++) t[i]=S[c[i]];
            u32 r0=residual(k,t,U0), r1=residual(k,t,U1);
            if(r1){ *gam=mul(sub(0,r0),inv(r1)); break; }
            int i=k; while(i>=0 && c[i]==a-(k+1)+i) i--;
            if(i<0) break; c[i]++; for(int j=i+1;j<=k;j++) c[j]=c[j-1]+1;
        }
    }
    return 1;
}
/* distinct gamma hash */
#define HB 21
#define HS (1u<<HB)
static u32 *H; static u64 hu;
static void hr(){ if(!H)H=malloc(HS*4); memset(H,0xff,HS*4); hu=0; }
static void ha(u32 v){ u32 key=(v==0xffffffffu)?0:v; u32 h=(u32)(((u64)key*2654435761u)>>(32-HB))&(HS-1);
    while(H[h]!=0xffffffffu){ if(H[h]==key) return; h=(h+1)&(HS-1);} H[h]=key; hu++; }
static void count(int k,int a,u64*na,u64*nb){
    hr(); u64 al=0; int idx[40]; for(int i=0;i<a;i++) idx[i]=i;
    while(1){ u32 g;int hg; if(aligned_set(k,idx,a,&g,&hg)){ al++; if(hg) ha(g); }
        int i=a-1; while(i>=0&&idx[i]==N-a+i) i--; if(i<0) break; idx[i]++;
        for(int j=i+1;j<a;j++) idx[j]=idx[j-1]+1; }
    *na=al; *nb=hu;
}
static u64 binom(int n,int r){ if(r<0||r>n)return 0; if(r>n-r)r=n-r; u64 v=1; for(int i=0;i<r;i++) v=v*(n-i)/(i+1); return v; }
int main(int c,char**v){
    if(c<3){fprintf(stderr,"mode n ...\n");return 1;}
    char*m=v[1]; int n=atoi(v[2]);
    char*pe=getenv("PRIME"); if(pe) P=strtoull(pe,0,10);
    fprintf(stderr,"[prime=%llu]\n",(unsigned long long)P);
    mkdom(n);
    if(!strcmp(m,"kkh")||!strcmp(m,"ceil")){
        int cb=!strcmp(m,"ceil");
        printf("INDEP %s n=%d  %s band  (Laplace+crossmult kernel)\n",cb?"ceil":"kkh",n,cb?"CEIL a=r":"DEEP a0=r+1");
        printf("%3s %3s %4s %11s %9s %9s %8s\n","r","k","a","#align","#bad","K","pack");
        for(int r=2;r<=n/2;r++){ int k=r-1,a=cb?r:r+1;
            for(int i=0;i<n;i++){U0[i]=pw(dom[i],r);U1[i]=pw(dom[i],r-1);}
            u64 al,bad; count(k,a,&al,&bad);
            u64 K=(1ULL<<r)*binom(n/2,r), pk=binom(n,a)/(a+1);
            printf("%3d %3d %4d %11llu %9llu %9llu %8llu\n",r,k,a,(unsigned long long)al,(unsigned long long)bad,(unsigned long long)K,(unsigned long long)pk);
            fflush(stdout);
        }
    } else if(!strcmp(m,"one")){
        int r=atoi(v[3]),e=atoi(v[4]),f=atoi(v[5]),a=atoi(v[6]); int k=r-1;
        for(int i=0;i<n;i++){U0[i]=pw(dom[i],e);U1[i]=pw(dom[i],f);}
        u64 al,bad; count(k,a,&al,&bad);
        printf("INDEP n=%d r=%d k=%d a=%d (x^%d,x^%d): #align=%llu #bad=%llu K=%llu C=%llu pack=%llu\n",
            n,r,k,a,e,f,(unsigned long long)al,(unsigned long long)bad,(unsigned long long)((1ULL<<r)*binom(n/2,r)),
            (unsigned long long)binom(n,a),(unsigned long long)(binom(n,a)/(a+1)));
    } else if(!strcmp(m,"mono")){
        int r=atoi(v[3]); int k=r-1,a0=r+1;
        u64 bb=0; int be=0,bf=0; u64 ba=0; int ae=0,af=0;
        for(int e=0;e<n;e++)for(int f=0;f<n;f++){ if(e==f)continue;
            for(int i=0;i<n;i++){U0[i]=pw(dom[i],e);U1[i]=pw(dom[i],f);}
            u64 al,bad; count(k,a0,&al,&bad);
            if(bad>bb){bb=bad;be=e;bf=f;} if(al>ba){ba=al;ae=e;af=f;}
        }
        u64 K=(1ULL<<r)*binom(n/2,r), pk=binom(n,a0)/(a0+1);
        printf("INDEP mono n=%d r=%d a0=%d: WORST #bad=%llu (x^%d,x^%d) K=%llu pack=%llu | WORST #align=%llu (x^%d,x^%d)\n",
            n,r,a0,(unsigned long long)bb,be,bf,(unsigned long long)K,(unsigned long long)pk,(unsigned long long)ba,ae,af);
    } else { fprintf(stderr,"bad mode\n"); return 1; }
    return 0;
}
