/* fast_orbits.c — optimized deep-band bad-gamma orbit counter via divided differences.
 * gamma(5-tuple t) = -DD_e(t)/DD_f(t), DD_e = 4th divided difference of x^e on t.
 * DD_e(t) = sum_{i in t} (x_i^e) / prod_{j in t, j!=i} (x_i - x_j).
 * Precompute: pe[i]=x_i^e, pf[i]=x_i^f, dinv[i][j]=1/(x_i-x_j).
 * A 6-subset is aligned iff all 6 of its 5-subtuples share one gamma. Collect distinct
 * aligned gammas; report #bad, gamma=0 flag, and orbit count under gamma->g^{e-f}*gamma. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t u32; typedef uint64_t u64;
static const u64 P=2013265921ULL;
static inline u32 mulm(u32 a,u32 b){return (u32)((u64)a*b%P);}
static inline u32 addm(u32 a,u32 b){u64 t=(u64)a+b;return t>=P?(u32)(t-P):(u32)t;}
static inline u32 subm(u32 a,u32 b){return a>=b?a-b:(u32)((u64)a+P-b);}
static u32 powm(u32 a,u64 e){u64 r=1,b=a%P;while(e){if(e&1)r=r*b%P;b=b*b%P;e>>=1;}return(u32)r;}
static inline u32 invm(u32 a){return powm(a,P-2);}
static int N;static u32 dom[128],GEN,PE[128],PF[128];
static u32 DINV[128][128]; /* 1/(x_i - x_j) */
static void make_dom(int n){N=n;u64 e=(P-1)/n;
  for(u32 c=2;c<300;c++){u32 h=powm(c,e);if(powm(h,n)==1&&powm(h,n/2)!=1){GEN=h;u32 cur=1;for(int i=0;i<n;i++){dom[i]=cur;cur=mulm(cur,h);}return;}}exit(1);}
/* divided difference of x^e (via table P*) on 5 indices in arr; returns DD. */
static inline u32 dd5(const int*ix,const u32*pw){
  u32 acc=0;
  for(int a=0;a<5;a++){int i=ix[a];u32 den=1;
    for(int b=0;b<5;b++)if(b!=a)den=mulm(den,DINV[i][ix[b]]);
    acc=addm(acc,mulm(pw[i],den));}
  return acc;}
/* gamma for a 5-tuple = -DD_e/DD_f (DD_f must be nonzero; if both zero -> degenerate-skip;
 * if DD_f==0 && DD_e!=0 -> no finite gamma (forces u1 alignment impossible) -> set tag. */
#define HBITS 24
#define HSZ (1u<<HBITS)
static u32 *htab;static int hused;static u32 *BADS;static int NB;
static void hreset(){if(!htab)htab=malloc((size_t)HSZ*4);memset(htab,0xff,(size_t)HSZ*4);hused=0;NB=0;}
static void hadd(u32 v){u32 key=v==0xffffffffu?0:v;u32 h=(u32)(((u64)key*2654435761u)>>(32-HBITS))&(HSZ-1);
  while(htab[h]!=0xffffffffu){if(htab[h]==key)return;h=(h+1)&(HSZ-1);}htab[h]=key;BADS[NB++]=v;hused++;}
static int hhas(u32 v){u32 key=v==0xffffffffu?0:v;u32 h=(u32)(((u64)key*2654435761u)>>(32-HBITS))&(HSZ-1);
  while(htab[h]!=0xffffffffu){if(htab[h]==key)return 1;h=(h+1)&(HSZ-1);}return 0;}
int main(int argc,char**argv){
  int n=atoi(argv[1]),r=atoi(argv[2]),e=atoi(argv[3]),f=atoi(argv[4]),a=atoi(argv[5]);
  if(r!=5||a!=6){fprintf(stderr,"this fast path is hardcoded r=5,a=6 (k=4)\n");return 1;}
  make_dom(n);
  for(int i=0;i<n;i++){PE[i]=powm(dom[i],e);PF[i]=powm(dom[i],f);}
  for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(i!=j)DINV[i][j]=invm(subm(dom[i],dom[j]));
  BADS=malloc((size_t)40000000*4);
  hreset();
  int idx[6];for(int i=0;i<6;i++)idx[i]=i;
  u64 cnt=0;
  while(1){
    /* 6 subtuples: drop each position. compute gamma for each, require all equal (and nondegenerate). */
    u32 gam=0;int gset=0;int ok=1;int nondeg=0;int anyfinite=0;
    for(int drop=0;drop<6 && ok;drop++){
      int t[5];int p=0;for(int q=0;q<6;q++)if(q!=drop)t[p++]=idx[q];
      u32 de=dd5(t,PE),df=dd5(t,PF);
      if(de||df)nondeg=1;
      if(df==0){ if(de){ ok=0; } /* DD_f=0,DD_e!=0 -> cannot align -> not bad via this; whole set fails */ }
      else { anyfinite=1; u32 g=mulm(subm(0,de),invm(df)); if(!gset){gam=g;gset=1;} else if(gam!=g){ok=0;} }
    }
    if(ok && nondeg && anyfinite){ if(!hhas(gam)) hadd(gam); }
    cnt++;
    /* next 6-combination */
    int i=5;while(i>=0&&idx[i]==n-6+i)i--;if(i<0)break;idx[i]++;for(int j=i+1;j<6;j++)idx[j]=idx[j-1]+1;
  }
  int has0=hhas(0)?1:0;
  /* orbit count under mult=g^{e-f} */
  long ediff=((long)e-f)%n;if(ediff<0)ediff+=n;u32 mult=powm(GEN,(u64)ediff);
  int gg=n,x=(int)ediff;while(x){int tt=gg%x;gg=x;x=tt;}int d=n/gg;
  /* closed check + orbit count */
  int closed=1;for(int i=0;i<NB;i++){if(!hhas(mulm(BADS[i],mult)))closed=0;}
  char*used=calloc(NB,1);int norb=0;long sz_d=0,sz_other=0;
  for(int i=0;i<NB;i++){if(used[i])continue;u32 start=BADS[i],c=start;int sz=0;
    do{ for(int j=0;j<NB;j++)if(!used[j]&&BADS[j]==c){used[j]=1;break;} c=mulm(c,mult);sz++; }while(c!=start&&sz<n+2);
    norb++; if(sz==d)sz_d++; else sz_other++; }
  printf("n=%d r=%d (e=%d,f=%d) a=%d: #bad=%d  0in=%d  d=%d  orbits=%d (size-d:%ld other:%ld)  closed=%d  check 1+d*(orbits-other?)\n",
    n,r,e,f,a,NB,has0,d,norb,sz_d,sz_other,closed);
  printf("  full_orb(size-d)=%ld  1+d*full_orb=%ld\n",sz_d,1+(long)d*sz_d);
  return 0;}
