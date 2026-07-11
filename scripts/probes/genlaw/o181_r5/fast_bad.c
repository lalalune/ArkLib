/* fast_bad.c — count #bad gammas + gamma=0 flag for r=5 deep band, plus efficient orbit count
 * via hash-table-marked orbit walk (O(NB * d), not O(NB^2)). Divided-difference kernel. */
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
static int N;static u32 dom[128],GEN,PE[128],PF[128];static u32 DINV[128][128];
static void make_dom(int n){N=n;u64 e=(P-1)/n;
  for(u32 c=2;c<300;c++){u32 h=powm(c,e);if(powm(h,n)==1&&powm(h,n/2)!=1){GEN=h;u32 cur=1;for(int i=0;i<n;i++){dom[i]=cur;cur=mulm(cur,h);}return;}}exit(1);}
static inline u32 dd5(const int*ix,const u32*pw){
  u32 acc=0;
  for(int a=0;a<5;a++){int i=ix[a];u32 den=1;
    for(int b=0;b<5;b++)if(b!=a)den=mulm(den,DINV[i][ix[b]]);
    acc=addm(acc,mulm(pw[i],den));}
  return acc;}
/* hash with a 'visited' bit packed in high bit of stored key; we store key in low 31 bits.
 * but keys can use full 31 bits (residues < 2^31). P<2^31 so residues fit in 31 bits. use bit31 as visited. */
#define HBITS 25
#define HSZ (1u<<HBITS)
static u32 *htab; static int NB;
static void hreset(){if(!htab)htab=malloc((size_t)HSZ*4);memset(htab,0,(size_t)HSZ*4);NB=0;} /* 0 = empty (we never store 0 as residue except gamma=0 -> store sentinel) */
/* store value+1 so 0 means empty; values are residues < P < 2^31, +1 fits in 31 bits; bit31=visited */
static inline u32 enc(u32 v){return v+1;}
static int hadd(u32 v){u32 e=enc(v);u32 h=(u32)(((u64)v*2654435761u)>>(32-HBITS))&(HSZ-1);
  while(htab[h]){ if((htab[h]&0x7fffffffu)==e) return 0; h=(h+1)&(HSZ-1);} htab[h]=e; NB++; return 1;}
static u32* hslot(u32 v){u32 e=enc(v);u32 h=(u32)(((u64)v*2654435761u)>>(32-HBITS))&(HSZ-1);
  while(htab[h]){ if((htab[h]&0x7fffffffu)==e) return &htab[h]; h=(h+1)&(HSZ-1);} return NULL;}
int main(int argc,char**argv){
  int n=atoi(argv[1]),r=atoi(argv[2]),e=atoi(argv[3]),f=atoi(argv[4]),a=atoi(argv[5]);
  if(r!=5||a!=6){fprintf(stderr,"hardcoded r=5,a=6\n");return 1;}
  make_dom(n);
  for(int i=0;i<n;i++){PE[i]=powm(dom[i],e);PF[i]=powm(dom[i],f);}
  for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(i!=j)DINV[i][j]=invm(subm(dom[i],dom[j]));
  hreset();
  int idx[6];for(int i=0;i<6;i++)idx[i]=i;
  while(1){
    u32 gam=0;int gset=0,ok=1,nondeg=0,anyf=0;
    for(int drop=0;drop<6 && ok;drop++){
      int t[5];int p=0;for(int q=0;q<6;q++)if(q!=drop)t[p++]=idx[q];
      u32 de=dd5(t,PE),df=dd5(t,PF);
      if(de||df)nondeg=1;
      if(df==0){if(de)ok=0;}else{anyf=1;u32 g=mulm(subm(0,de),invm(df));if(!gset){gam=g;gset=1;}else if(gam!=g)ok=0;}
    }
    if(ok&&nondeg&&anyf)hadd(gam);
    int i=5;while(i>=0&&idx[i]==n-6+i)i--;if(i<0)break;idx[i]++;for(int j=i+1;j<6;j++)idx[j]=idx[j-1]+1;
  }
  u32*s0=hslot(0);int has0=s0?1:0;
  long ediff=((long)e-f)%n;if(ediff<0)ediff+=n;u32 mult=powm(GEN,(u64)ediff);
  int gg=n,x=(int)ediff;while(x){int tt=gg%x;gg=x;x=tt;}int d=n/gg;
  /* efficient orbit count: walk hash table, for each unvisited slot, traverse its orbit via *mult marking visited */
  long norb=0,szd=0,szo=0;
  for(u32 h=0;h<HSZ;h++){
    if(!htab[h])continue; if(htab[h]&0x80000000u)continue; /* visited */
    u32 start=(htab[h]&0x7fffffffu)-1; u32 c=start;int sz=0;
    do{ u32*sl=hslot(c); if(sl){ *sl|=0x80000000u; } c=mulm(c,mult); sz++; }while(c!=start && sz<n+2);
    norb++; if(sz==d)szd++; else szo++;
  }
  printf("n=%d r=%d (e=%d,f=%d) a=%d: #bad=%d 0in=%d d=%d orbits=%ld (size-d:%ld other:%ld) full_orb=%ld 1+d*full_orb=%ld\n",
    n,r,e,f,a,NB,has0,d,norb,szd,szo,szd,1+(long)d*szd);
  return 0;}
