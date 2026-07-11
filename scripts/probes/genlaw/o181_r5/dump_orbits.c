/* dump_orbits.c — dump the bad-scalar SET for a single (e,f) stack at the deep band,
 * then analyze the Z/n equivariance orbit structure:
 *   gamma -> g^{e-f} * gamma   (the B2 orbit action; period d = n/gcd(n,e-f))
 * Verify #bad = d*orbits + [0 in bad] and report the orbit-count census.
 * Built from cd_demand.c residual-det kernel (faithful BabyBear). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint32_t u32;
typedef uint64_t u64;
static const u64 P = 2013265921ULL;
static inline u32 mulm(u32 a, u32 b){ return (u32)((u64)a*b % P); }
static inline u32 subm(u32 a, u32 b){ return a>=b? a-b : (u32)((u64)a+P-b); }
static u32 powm(u32 a, u64 e){ u64 r=1,b=a%P; while(e){ if(e&1) r=r*b%P; b=b*b%P; e>>=1; } return (u32)r; }
static inline u32 invm(u32 a){ return powm(a, P-2); }

static int N;
static u32 dom[64], GEN;
static u32 U0[64], U1[64];

static void make_dom(int n){
    N=n; u64 e=(P-1)/n;
    for(u32 c=2;c<300;c++){ u32 h=powm(c,e);
        if(powm(h,n)==1 && powm(h,n/2)!=1){ GEN=h; u32 cur=1; for(int i=0;i<n;i++){dom[i]=cur;cur=mulm(cur,h);} return; } }
    fprintf(stderr,"no root order %d\n",n); exit(1);
}
static u32 detm(u32 *M,int m){ u32 det=1;
    for(int col=0;col<m;col++){ int piv=-1;
        for(int rr=col;rr<m;rr++) if(M[rr*m+col]){piv=rr;break;}
        if(piv<0) return 0;
        if(piv!=col){ for(int c=0;c<m;c++){u32 t=M[piv*m+c];M[piv*m+c]=M[col*m+c];M[col*m+c]=t;} det=subm(0,det); }
        det=mulm(det,M[col*m+col]); u32 inv=invm(M[col*m+col]);
        for(int rr=col+1;rr<m;rr++) if(M[rr*m+col]){ u32 fa=mulm(M[rr*m+col],inv);
            for(int c=col;c<m;c++) M[rr*m+c]=subm(M[rr*m+c],mulm(fa,M[col*m+c])); } }
    return det; }
static u32 residual(int k,const int*t,const u32*y){ int m=k+1; u32 M[8*8];
    for(int a=0;a<m;a++){ for(int b=0;b<k;b++) M[a*m+b]=powm(dom[t[a]],b); M[a*m+k]=y[t[a]]; }
    return detm(M,m); }
static int aligned_set(int k,const int*Sidx,int a,u32*gam_out,int*has_gam){
    int comb[8]; for(int i=0;i<=k;i++) comb[i]=i;
    int gam_set=0; u32 gam=0; int nondeg=0; int any_u1=0;
    while(1){ int t[8]; for(int i=0;i<=k;i++) t[i]=Sidx[comb[i]];
        u32 r0=residual(k,t,U0), r1=residual(k,t,U1);
        if(r0||r1) nondeg=1;
        if(r1==0){ if(r0) return 0; }
        else { any_u1=1; u32 g=mulm(subm(0,r0),invm(r1)); if(!gam_set){gam=g;gam_set=1;} else if(gam!=g) return 0; }
        int i=k; while(i>=0 && comb[i]==a-(k+1)+i) i--; if(i<0) break; comb[i]++; for(int j=i+1;j<=k;j++) comb[j]=comb[j-1]+1; }
    if(!nondeg) return 0; *has_gam=any_u1; if(any_u1)*gam_out=gam; return 1;
}
#define HBITS 21
#define HSZ (1u<<HBITS)
static u32 *htab; static int hused;
static void hreset(){ if(!htab) htab=malloc(HSZ*sizeof(u32)); memset(htab,0xff,HSZ*sizeof(u32)); hused=0; }
static int hadd(u32 v){ u32 key=v==0xffffffffu?0:v;
    u32 h=(u32)(((u64)key*2654435761u)>>(32-HBITS))&(HSZ-1);
    while(htab[h]!=0xffffffffu){ if(htab[h]==key) return 0; h=(h+1)&(HSZ-1); } htab[h]=key; hused++; return 1; }
static int hhas(u32 v){ u32 key=v==0xffffffffu?0:v;
    u32 h=(u32)(((u64)key*2654435761u)>>(32-HBITS))&(HSZ-1);
    while(htab[h]!=0xffffffffu){ if(htab[h]==key) return 1; h=(h+1)&(HSZ-1); } return 0; }

int main(int argc,char**argv){
    if(argc<6){ fprintf(stderr,"usage: %s n r e f\n",argv[0]); return 1; }
    int n=atoi(argv[1]), r=atoi(argv[2]), e=atoi(argv[3]), f=atoi(argv[4]);
    int a=atoi(argv[5]); int kc=(r-2)+1;
    make_dom(n);
    for(int i=0;i<n;i++){ U0[i]=powm(dom[i],e); U1[i]=powm(dom[i],f); }
    hreset();
    int idx[40]; for(int i=0;i<a;i++) idx[i]=i;
    /* collect all bad scalars */
    u32 *bads=malloc(sizeof(u32)*2000000); int nbad=0; int has0=0;
    while(1){ u32 gam; int hg;
        if(aligned_set(kc,idx,a,&gam,&hg)){ if(hg){ if(hadd(gam)){ bads[nbad++]=gam; if(gam==0) has0=1; } } }
        int i=a-1; while(i>=0 && idx[i]==n-a+i) i--; if(i<0) break; idx[i]++; for(int j=i+1;j<a;j++) idx[j]=idx[j-1]+1; }
    printf("n=%d r=%d (x^%d,x^%d) a=%d: #bad=%d  0 in bad? %d\n", n,r,e,f,a,nbad,has0);
    /* orbit action: gamma -> mult = g^{e-f} * gamma */
    long ediff = ((long)e-f) % n; if(ediff<0) ediff+=n;
    u32 mult = powm(GEN, (u64)ediff);   /* g^{e-f} */
    /* compute period d = n/gcd(n,e-f) and ord(mult) */
    int gg=n, x=(int)ediff; while(x){int t=gg%x; gg=x; x=t;} int d=n/gg;
    /* order of mult as a field element */
    u32 cur=mult; int ordmult=1; while(cur!=1){ cur=mulm(cur,mult); ordmult++; if(ordmult>100000) break; }
    printf("  e-f mod n=%ld, gcd(n,e-f)=%d, d=n/gcd=%d, ord(g^{e-f})=%d\n", ediff,gg,d,ordmult);
    /* verify bad set is closed under gamma->mult*gamma, and count orbits */
    int closed=1;
    for(int i=0;i<nbad;i++){ u32 img=mulm(bads[i],mult); if(!hhas(img)){ closed=0; } }
    printf("  bad set closed under gamma->g^{e-f}*gamma? %s\n", closed?"YES":"NO");
    /* count orbits: mark visited */
    char *vis=calloc(HSZ,1);
    int norb=0; int orbsizes[4096]; int norbsizes=0;
    /* need index lookup: rebuild via linear scan (nbad up to ~1.4k, fine) */
    char *used=calloc(nbad,1);
    for(int i=0;i<nbad;i++){
        if(used[i]) continue;
        u32 start=bads[i]; u32 c=start; int sz=0;
        do {
            /* find c in bads, mark used */
            for(int j=0;j<nbad;j++) if(!used[j] && bads[j]==c){ used[j]=1; break; }
            c=mulm(c,mult); sz++;
        } while(c!=start && sz< n+2);
        norb++; if(norbsizes<4096) orbsizes[norbsizes++]=sz;
    }
    /* orbit size histogram */
    int hist[64]={0};
    for(int i=0;i<norbsizes;i++){ int s=orbsizes[i]; if(s<64) hist[s]++; }
    printf("  #orbits=%d   #bad = sum of orbit sizes\n", norb);
    printf("  orbit-size histogram: ");
    for(int s=1;s<64;s++) if(hist[s]) printf("[size %d]x%d ", s, hist[s]);
    printf("\n");
    /* predicted: #bad = d*(full orbits) + (fixed points). gamma=0 is fixed. */
    printf("  CHECK: d*floor + fixed.  #bad=%d, d=%d, (#bad - [0])/d = %.4f\n",
           nbad, d, (double)(nbad - has0)/d);
    free(vis); free(used); free(bads);
    return 0;
}
