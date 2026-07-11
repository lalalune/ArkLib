/* generalized fast orbit counter for any r (deg k=r-2, band a=r+1). divided differences. */
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
static int N,KK,AA;static u32 dom[128],GEN,PE[128],PF[128];static u32 DINV[128][128];
static void make_dom(int n){N=n;u64 e=(P-1)/n;
  for(u32 c=2;c<300;c++){u32 h=powm(c,e);if(powm(h,n)==1&&powm(h,n/2)!=1){GEN=h;u32 cur=1;for(int i=0;i<n;i++){dom[i]=cur;cur=mulm(cur,h);}return;}}exit(1);}
/* (m-1)th divided diff of monomial table pw on m indices */
static inline u32 ddm(const int*ix,int m,const u32*pw){
  u32 acc=0;
  for(int a=0;a<m;a++){int i=ix[a];u32 den=1;
    for(int b=0;b<m;b++)if(b!=a)den=mulm(den,DINV[i][ix[b]]);
    acc=addm(acc,mulm(pw[i],den));}
  return acc;}
#define HBITS 24
#define HSZ (1u<<HBITS)
static u32 *htab;static u32 *BADS;static int NB;
static void hreset(){if(!htab)htab=malloc((size_t)HSZ*4);memset(htab,0xff,(size_t)HSZ*4);NB=0;}
static int hadd(u32 v){u32 key=v==0xffffffffu?0:v;u32 h=(u32)(((u64)key*2654435761u)>>(32-HBITS))&(HSZ-1);
  while(htab[h]!=0xffffffffu){if(htab[h]==key)return 0;h=(h+1)&(HSZ-1);}htab[h]=key;BADS[NB++]=v;return 1;}
static int hhas(u32 v){u32 key=v==0xffffffffu?0:v;u32 h=(u32)(((u64)key*2654435761u)>>(32-HBITS))&(HSZ-1);
  while(htab[h]!=0xffffffffu){if(htab[h]==key)return 1;h=(h+1)&(HSZ-1);}return 0;}
int main(int argc,char**argv){
  int n=atoi(argv[1]),r=atoi(argv[2]),e=atoi(argv[3]),f=atoi(argv[4]),a=atoi(argv[5]);
  int kc=(r-2)+1; /* matrix size; subtuple size = kc+1 = r-1 */
  int m=kc+1; /* divided-diff order m points */
  KK=kc;AA=a;N=n;make_dom(n);
  for(int i=0;i<n;i++){PE[i]=powm(dom[i],e);PF[i]=powm(dom[i],f);}
  for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(i!=j)DINV[i][j]=invm(subm(dom[i],dom[j]));
  BADS=malloc((size_t)40000000*4);hreset();
  int idx[16];for(int i=0;i<a;i++)idx[i]=i;
  while(1){
    u32 gam=0;int gset=0,ok=1,nondeg=0,anyfin=0;
    /* iterate all m-subtuples of the a-set */
    int comb[16];for(int i=0;i<m;i++)comb[i]=i;
    while(ok){
      int t[16];for(int i=0;i<m;i++)t[i]=idx[comb[i]];
      u32 de=ddm(t,m,PE),df=ddm(t,m,PF);
      if(de||df)nondeg=1;
      if(df==0){if(de)ok=0;}
      else{anyfin=1;u32 g=mulm(subm(0,de),invm(df));if(!gset){gam=g;gset=1;}else if(gam!=g)ok=0;}
      int i=m-1;while(i>=0&&comb[i]==a-m+i)i--;if(i<0)break;comb[i]++;for(int j=i+1;j<m;j++)comb[j]=comb[j-1]+1;
    }
    if(ok&&nondeg&&anyfin){if(!hhas(gam))hadd(gam);}
    int i=a-1;while(i>=0&&idx[i]==n-a+i)i--;if(i<0)break;idx[i]++;for(int j=i+1;j<a;j++)idx[j]=idx[j-1]+1;
  }
  int has0=hhas(0)?1:0;
  long ediff=((long)e-f)%n;if(ediff<0)ediff+=n;u32 mult=powm(GEN,(u64)ediff);
  int gg=n,x=(int)ediff;while(x){int tt=gg%x;gg=x;x=tt;}int d=n/gg;
  char*used=calloc(NB,1);int norb=0;long szd=0,szo=0;
  for(int i=0;i<NB;i++){if(used[i])continue;u32 start=BADS[i],c=start;int sz=0;
    do{for(int j=0;j<NB;j++)if(!used[j]&&BADS[j]==c){used[j]=1;break;}c=mulm(c,mult);sz++;}while(c!=start&&sz<n+2);
    norb++;if(sz==d)szd++;else szo++;}
  printf("n=%d r=%d (e=%d,f=%d) a=%d: #bad=%d 0in=%d d=%d orbits=%d (size-d:%ld other:%ld) full_orb=%ld\n",
    n,r,e,f,a,NB,has0,d,norb,szd,szo,szd);
  return 0;}
