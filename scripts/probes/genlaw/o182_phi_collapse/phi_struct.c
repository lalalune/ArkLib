/* phi_struct.c — characterize Phi(c1,c2) = -res0/res1 on line-forced (r+1)-subsets.
 *
 * For the deep-band line (e,f), pin k_c=r-1, a0=r+1. For each line-forced
 * non-degenerate (r+1)-subset S with a bad scalar gamma:
 *   record (c1=e1(S), c2=e2(S)-as-power-sum-p2, gamma).
 * TESTS:
 *  T1  gamma == -c1 ?  (the Vieta/e1 claim).  [task says FALSE on maximizer]
 *  T2  is gamma in mu_n? (gamma^n==1)
 *  T3  ANTIPODAL: S* = {-x : x in S} = {x*zeta : zeta=g^{n/2}}. Is S* line-forced?
 *      what is gamma(S*) vs gamma(S)?  (does antipode negate / fix gamma?)
 *  T4  FROBENIUS: S^2 = {x^2 : x in S}. line-forced? gamma(S^2) vs gamma(S)^2 ?
 *  T5  the c1-COLLAPSE: how many distinct c1 map to each gamma (fiber over image),
 *      and how many distinct gamma per c1 (Phi single-valued per c1-fiber?).
 *  T6  ROTATION: S' = g*S (multiply all by g). gamma(g*S) = ? * gamma(S)?
 *
 * Output is machine-parseable lines for downstream python orbit analysis.
 */
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
static int N;static u32 dom[64],GEN,U0[64],U1[64];
static int HALF; /* index shift for antipode: dom[i]*dom[HALF] = -dom[i] (dom[HALF]=g^{n/2}=-1) */
static void make_dom(int n){N=n;u64 e=(P-1)/n;
  for(u32 c=2;c<300;c++){u32 h=powm(c,e);if(powm(h,n)==1&&powm(h,n/2)!=1){GEN=h;u32 cur=1;for(int i=0;i<n;i++){dom[i]=cur;cur=mulm(cur,h);}HALF=n/2;return;}}exit(1);}
static u32 detm(u32*M,int m){u32 det=1;
  for(int col=0;col<m;col++){int piv=-1;for(int rr=col;rr<m;rr++)if(M[rr*m+col]){piv=rr;break;}
    if(piv<0)return 0;if(piv!=col){for(int c=0;c<m;c++){u32 t=M[piv*m+c];M[piv*m+c]=M[col*m+c];M[col*m+c]=t;}det=subm(0,det);}
    det=mulm(det,M[col*m+col]);u32 inv=invm(M[col*m+col]);
    for(int rr=col+1;rr<m;rr++)if(M[rr*m+col]){u32 fa=mulm(M[rr*m+col],inv);for(int c=col;c<m;c++)M[rr*m+c]=subm(M[rr*m+c],mulm(fa,M[col*m+c]));}}return det;}
/* residual using EXPLICIT field values x[] (not dom indices) so we can map subsets */
static u32 residual_x(int k,const u32*xv,const u32*yv){int m=k+1;u32 M[8*8];
  for(int a=0;a<m;a++){for(int b=0;b<k;b++)M[a*m+b]=powm(xv[a],b);M[a*m+k]=yv[a];}return detm(M,m);}
/* given a multiset of x-values for S and matched (u0,u1) values, derive gamma; return 1 if line-forced+nondeg+has_gamma */
static int gamma_of_xset(int k,int a,const u32*xv,const u32*u0v,const u32*u1v,u32*gam_out){
  int comb[8];for(int i=0;i<=k;i++)comb[i]=i;int gam_set=0;u32 gam=0;int nondeg=0;int any_u1=0;
  while(1){u32 xx[8],y0[8],y1[8];for(int i=0;i<=k;i++){xx[i]=xv[comb[i]];y0[i]=u0v[comb[i]];y1[i]=u1v[comb[i]];}
    u32 r0=residual_x(k,xx,y0),r1=residual_x(k,xx,y1);if(r0||r1)nondeg=1;
    if(r1==0){if(r0)return 0;}else{any_u1=1;u32 g=mulm(subm(0,r0),invm(r1));if(!gam_set){gam=g;gam_set=1;}else if(gam!=g)return 0;}
    int i=k;while(i>=0&&comb[i]==a-(k+1)+i)i--;if(i<0)break;comb[i]++;for(int j=i+1;j<=k;j++)comb[j]=comb[j-1]+1;}
  if(!nondeg)return 0;if(!any_u1)return 0;*gam_out=gam;return 1;}

/* find which index in [0,N) has dom value v; -1 if none */
static int idx_of(u32 v){for(int i=0;i<N;i++)if(dom[i]==v)return i;return -1;}

int main(int argc,char**argv){
  int n=atoi(argv[1]),r=atoi(argv[2]),e=atoi(argv[3]),f=atoi(argv[4]);
  int a=argc>5?atoi(argv[5]):r+1;
  int kc=(r-2)+1;make_dom(n);
  for(int i=0;i<n;i++){U0[i]=powm(dom[i],e);U1[i]=powm(dom[i],f);}
  int idx[40];for(int i=0;i<a;i++)idx[i]=i;
  /* T1/T2 emit: c1 c2 gamma gam_eq_negc1 gamma_in_mu  for every line-forced S */
  while(1){
    /* build x-values of S */
    u32 xv[40],u0v[40],u1v[40];u32 c1=0,c2=0;
    for(int i=0;i<a;i++){xv[i]=dom[idx[i]];u0v[i]=U0[idx[i]];u1v[i]=U1[idx[i]];c1=addm(c1,xv[i]);c2=addm(c2,mulm(xv[i],xv[i]));}
    u32 gam;
    if(gamma_of_xset(kc,a,xv,u0v,u1v,&gam)){
      int eqnegc1 = (gam==subm(0,c1));
      int inmu = (gam!=0 && powm(gam,n)==1);
      /* ANTIPODE: S* = {-x}. its e,f images: u0(-x)=(-x)^e = (-1)^e x^e, u1 similarly */
      u32 axv[40],au0[40],au1[40];u32 ac1=0,ac2=0;
      for(int i=0;i<a;i++){u32 nx=subm(0,xv[i]);axv[i]=nx;au0[i]=powm(nx,e);au1[i]=powm(nx,f);ac1=addm(ac1,nx);ac2=addm(ac2,mulm(nx,nx));}
      u32 agam;int aok=gamma_of_xset(kc,a,axv,au0,au1,&agam);
      /* FROBENIUS: S^2={x^2}. u0(x^2)=x^{2e}, u1=x^{2f} */
      u32 fxv[40],fu0[40],fu1[40];u32 fc1=0;int fdistinct=1;
      for(int i=0;i<a;i++){u32 x2=mulm(xv[i],xv[i]);fxv[i]=x2;fu0[i]=powm(x2,e);fu1[i]=powm(x2,f);fc1=addm(fc1,x2);}
      /* check x^2 distinct (collapses if x and -x both in S) */
      for(int i=0;i<a&&fdistinct;i++)for(int j=i+1;j<a;j++)if(fxv[i]==fxv[j]){fdistinct=0;break;}
      u32 fgam=0;int fok=0;
      if(fdistinct) fok=gamma_of_xset(kc,a,fxv,fu0,fu1,&fgam);
      printf("S c1=%u c2=%u gam=%u eqnegc1=%d inmu=%d | antip ac1=%u agam=%u aok=%d agam_eq_gam=%d agam_eq_neggam=%d | frob fok=%d fdist=%d fgam=%u fgam_eq_gam2=%d\n",
        c1,c2,gam,eqnegc1,inmu, ac1,agam,aok,(aok&&agam==gam),(aok&&agam==subm(0,gam)),
        fok,fdistinct,fgam,(fok&&fgam==mulm(gam,gam)));
    }
    int i=a-1;while(i>=0&&idx[i]==N-a+i)i--;if(i<0)break;idx[i]++;for(int j=i+1;j<a;j++)idx[j]=idx[j-1]+1;
  }
  return 0;
}
