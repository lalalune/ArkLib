/* verify: residual det of x^e on a (k+1)=5 subtuple t equals
 *  +/- Vandermonde(t) * h_{e-k}(t)   where h_m = complete homogeneous symmetric of degree m,
 *  k=4 here. So gamma = -h_{e-4}(t)/h_{f-4}(t). Test on random tuples. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint32_t u32; typedef uint64_t u64;
static const u64 P=2013265921ULL;
static inline u32 mulm(u32 a,u32 b){return (u32)((u64)a*b%P);}
static inline u32 addm(u32 a,u32 b){u64 t=(u64)a+b;return t>=P?(u32)(t-P):(u32)t;}
static inline u32 subm(u32 a,u32 b){return a>=b?a-b:(u32)((u64)a+P-b);}
static u32 powm(u32 a,u64 e){u64 r=1,b=a%P;while(e){if(e&1)r=r*b%P;b=b*b%P;e>>=1;}return(u32)r;}
static inline u32 invm(u32 a){return powm(a,P-2);}
static u32 detm(u32*M,int m){u32 det=1;
  for(int col=0;col<m;col++){int piv=-1;for(int rr=col;rr<m;rr++)if(M[rr*m+col]){piv=rr;break;}
    if(piv<0)return 0;if(piv!=col){for(int c=0;c<m;c++){u32 t=M[piv*m+c];M[piv*m+c]=M[col*m+c];M[col*m+c]=t;}det=subm(0,det);}
    det=mulm(det,M[col*m+col]);u32 inv=invm(M[col*m+col]);
    for(int rr=col+1;rr<m;rr++)if(M[rr*m+col]){u32 fa=mulm(M[rr*m+col],inv);for(int c=col;c<m;c++)M[rr*m+c]=subm(M[rr*m+c],mulm(fa,M[col*m+c]));}}return det;}
/* residual: 5x5, rows: [1,x,x^2,x^3, x^e] for the 5 points */
static u32 residual_e(u32*pts,int k,u32 e){int m=k+1;u32 M[64];
  for(int a=0;a<m;a++){for(int b=0;b<k;b++)M[a*m+b]=powm(pts[a],b);M[a*m+k]=powm(pts[a],e);}return detm(M,m);}
static u32 vdm(u32*pts,int m){u32 v=1;for(int i=0;i<m;i++)for(int j=i+1;j<m;j++)v=mulm(v,subm(pts[j],pts[i]));return v;}
/* complete homogeneous h_d on m points via recurrence: h_d = sum over monomials.
 * use: h_d(x_1..x_m) = sum_{i} x_i^{d+m-1} / prod_{j!=i}(x_i-x_j)  (this is the divided difference of x^{d+m-1}? )
 * Actually 4th divided diff of x^e on 5 points = h_{e-4}(points). Divided diff formula:
 * f[x0..x4] = sum_i f(x_i)/prod_{j!=i}(x_i-x_j). */
static u32 divdiff(u32*pts,int m,u32 e){ /* m points, (m-1)th divided difference of x^e */
  u32 acc=0;
  for(int i=0;i<m;i++){u32 num=powm(pts[i],e);u32 den=1;
    for(int j=0;j<m;j++)if(j!=i)den=mulm(den,subm(pts[i],pts[j]));
    acc=addm(acc,mulm(num,invm(den)));}
  return acc;}
int main(){
  int n=32;u64 ee=(P-1)/n;u32 GEN=0;
  for(u32 c=2;c<300;c++){u32 h=powm(c,ee);if(powm(h,n)==1&&powm(h,n/2)!=1){GEN=h;break;}}
  u32 dom[32];u32 cur=1;for(int i=0;i<n;i++){dom[i]=cur;cur=mulm(cur,GEN);}
  /* pick a 5-subtuple, e=17,f=31, k=4 */
  int e=17,f=31,k=4;
  int tuples[][5]={{0,1,2,3,4},{0,2,5,9,13},{1,4,7,11,30}};
  for(int tt=0;tt<3;tt++){
    u32 pts[5];for(int i=0;i<5;i++)pts[i]=dom[tuples[tt][i]];
    u32 r0=residual_e(pts,k,e),r1=residual_e(pts,k,f);
    u32 gam_det = r1? mulm(subm(0,r0),invm(r1)) : 0xffffffff;
    /* divided diff: (m-1)=4 th divided diff of x^e = divdiff(pts,5,e) = h_{e-4} */
    u32 dd_e=divdiff(pts,5,e),dd_f=divdiff(pts,5,f);
    u32 gam_dd = dd_f? mulm(subm(0,dd_e),invm(dd_f)) : 0xffffffff;
    printf("tuple %d: gamma_det=%u  gamma_divdiff=%u  match=%d\n",tt,gam_det,gam_dd,gam_det==gam_dd);
  }
  return 0;}
