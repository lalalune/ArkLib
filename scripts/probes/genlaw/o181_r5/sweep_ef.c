/* sweep_ef.c — for fixed n,r, sweep all monomial (e,f) pairs at deep band a0=r+1,
 * report #bad and the orbit period d, find the maximizer. Reuses residual-det kernel. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t u32; typedef uint64_t u64;
static const u64 P = 2013265921ULL;
static inline u32 mulm(u32 a,u32 b){return (u32)((u64)a*b%P);}
static inline u32 subm(u32 a,u32 b){return a>=b?a-b:(u32)((u64)a+P-b);}
static u32 powm(u32 a,u64 e){u64 r=1,b=a%P;while(e){if(e&1)r=r*b%P;b=b*b%P;e>>=1;}return(u32)r;}
static inline u32 invm(u32 a){return powm(a,P-2);}
static int N; static u32 dom[64],GEN,U0[64],U1[64];
static void make_dom(int n){N=n;u64 e=(P-1)/n;
  for(u32 c=2;c<300;c++){u32 h=powm(c,e);
    if(powm(h,n)==1&&powm(h,n/2)!=1){GEN=h;u32 cur=1;for(int i=0;i<n;i++){dom[i]=cur;cur=mulm(cur,h);}return;}}
  exit(1);}
static u32 detm(u32*M,int m){u32 det=1;
  for(int col=0;col<m;col++){int piv=-1;
    for(int rr=col;rr<m;rr++)if(M[rr*m+col]){piv=rr;break;}
    if(piv<0)return 0;
    if(piv!=col){for(int c=0;c<m;c++){u32 t=M[piv*m+c];M[piv*m+c]=M[col*m+c];M[col*m+c]=t;}det=subm(0,det);}
    det=mulm(det,M[col*m+col]);u32 inv=invm(M[col*m+col]);
    for(int rr=col+1;rr<m;rr++)if(M[rr*m+col]){u32 fa=mulm(M[rr*m+col],inv);
      for(int c=col;c<m;c++)M[rr*m+c]=subm(M[rr*m+c],mulm(fa,M[col*m+c]));}}
  return det;}
static u32 residual(int k,const int*t,const u32*y){int m=k+1;u32 M[8*8];
  for(int a=0;a<m;a++){for(int b=0;b<k;b++)M[a*m+b]=powm(dom[t[a]],b);M[a*m+k]=y[t[a]];}
  return detm(M,m);}
static int aligned_set(int k,const int*Sidx,int a,u32*gam_out,int*has_gam){
  int comb[8];for(int i=0;i<=k;i++)comb[i]=i;
  int gam_set=0;u32 gam=0;int nondeg=0;int any_u1=0;
  while(1){int t[8];for(int i=0;i<=k;i++)t[i]=Sidx[comb[i]];
    u32 r0=residual(k,t,U0),r1=residual(k,t,U1);
    if(r0||r1)nondeg=1;
    if(r1==0){if(r0)return 0;}
    else{any_u1=1;u32 g=mulm(subm(0,r0),invm(r1));if(!gam_set){gam=g;gam_set=1;}else if(gam!=g)return 0;}
    int i=k;while(i>=0&&comb[i]==a-(k+1)+i)i--;if(i<0)break;comb[i]++;for(int j=i+1;j<=k;j++)comb[j]=comb[j-1]+1;}
  if(!nondeg)return 0;*has_gam=any_u1;if(any_u1)*gam_out=gam;return 1;}
#define HBITS 22
#define HSZ (1u<<HBITS)
static u32*htab;static int hused;
static void hreset(){if(!htab)htab=malloc(HSZ*sizeof(u32));memset(htab,0xff,HSZ*sizeof(u32));hused=0;}
static void hadd(u32 v){u32 key=v==0xffffffffu?0:v;
  u32 h=(u32)(((u64)key*2654435761u)>>(32-HBITS))&(HSZ-1);
  while(htab[h]!=0xffffffffu){if(htab[h]==key)return;h=(h+1)&(HSZ-1);}htab[h]=key;hused++;}
static u64 count_bad(int k,int a){hreset();int idx[40];for(int i=0;i<a;i++)idx[i]=i;
  while(1){u32 gam;int hg;if(aligned_set(k,idx,a,&gam,&hg)){if(hg)hadd(gam);}
    int i=a-1;while(i>=0&&idx[i]==N-a+i)i--;if(i<0)break;idx[i]++;for(int j=i+1;j<a;j++)idx[j]=idx[j-1]+1;}
  return(u64)hused;}
int main(int argc,char**argv){
  int n=atoi(argv[1]),r=atoi(argv[2]);
  int kc=(r-2)+1,a0=r+1; make_dom(n);
  u64 best=0;int be=0,bf=0;
  /* only need e>f WLOG? gamma <-> 1/gamma symmetry swaps e,f. sweep all to be safe but skip half */
  for(int e=0;e<n;e++){for(int f=0;f<n;f++){
    if(e==f)continue;
    for(int i=0;i<n;i++){U0[i]=powm(dom[i],e);U1[i]=powm(dom[i],f);}
    u64 bad=count_bad(kc,a0);
    if(bad>best){best=bad;be=e;bf=f;
      long ediff=((long)e-f)%n;if(ediff<0)ediff+=n;
      int gg=n,x=(int)ediff;while(x){int t=gg%x;gg=x;x=t;}int d=n/gg;
      printf("  new best #bad=%llu at (e=%d,f=%d) e-f=%ld gcd=%d d=%d\n",(unsigned long long)best,e,f,ediff,gg,d);fflush(stdout);}
  }}
  long ediff=((long)be-bf)%n;if(ediff<0)ediff+=n;int gg=n,x=(int)ediff;while(x){int t=gg%x;gg=x;x=t;}int d=n/gg;
  printf("WORST n=%d r=%d: #bad=%llu at (%d,%d) d=%d\n",n,r,(unsigned long long)best,be,bf,d);
  return 0;}
