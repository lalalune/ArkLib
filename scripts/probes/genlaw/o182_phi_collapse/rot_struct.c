/* rot_struct.c — test the ROTATION (cyclic g-shift) and DILATION action on gamma.
 * S' = g^j * S (multiply every element by g^j). Record gamma(S') vs gamma(S).
 * Also test the full group action: does the image of Phi decompose into orbits
 * under x -> g*x (rotation by primitive root), and is gamma(g*S) = g^? * gamma(S)?
 *
 * The hope (brief): distinct gamma <-> r-subsets of n/2 AXES x signs.  An "axis"
 * is an antipodal pair {x,-x} = {g^i, g^{i+n/2}}.  There are n/2 axes.  Rotation
 * by g permutes axes cyclically (period n/2 on axes).  If gamma transforms by a
 * fixed scalar per g-shift, the rotation orbits of gammas reveal the axis content.
 *
 * Output per line-forced S: gamma, gamma(g*S), ratio gamma(gS)/gamma(S) if both nz.
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
static void make_dom(int n){N=n;u64 e=(P-1)/n;
  for(u32 c=2;c<300;c++){u32 h=powm(c,e);if(powm(h,n)==1&&powm(h,n/2)!=1){GEN=h;u32 cur=1;for(int i=0;i<n;i++){dom[i]=cur;cur=mulm(cur,h);}return;}}exit(1);}
static u32 detm(u32*M,int m){u32 det=1;
  for(int col=0;col<m;col++){int piv=-1;for(int rr=col;rr<m;rr++)if(M[rr*m+col]){piv=rr;break;}
    if(piv<0)return 0;if(piv!=col){for(int c=0;c<m;c++){u32 t=M[piv*m+c];M[piv*m+c]=M[col*m+c];M[col*m+c]=t;}det=subm(0,det);}
    det=mulm(det,M[col*m+col]);u32 inv=invm(M[col*m+col]);
    for(int rr=col+1;rr<m;rr++)if(M[rr*m+col]){u32 fa=mulm(M[rr*m+col],inv);for(int c=col;c<m;c++)M[rr*m+c]=subm(M[rr*m+c],mulm(fa,M[col*m+c]));}}return det;}
static u32 residual_x(int k,const u32*xv,const u32*yv){int m=k+1;u32 M[8*8];
  for(int a=0;a<m;a++){for(int b=0;b<k;b++)M[a*m+b]=powm(xv[a],b);M[a*m+k]=yv[a];}return detm(M,m);}
static int gamma_of_xset(int k,int a,const u32*xv,int e,int f,u32*gam_out){
  int comb[8];for(int i=0;i<=k;i++)comb[i]=i;int gam_set=0;u32 gam=0;int nondeg=0;int any_u1=0;
  while(1){u32 xx[8],y0[8],y1[8];for(int i=0;i<=k;i++){xx[i]=xv[comb[i]];y0[i]=powm(xx[i],e);y1[i]=powm(xx[i],f);}
    u32 r0=residual_x(k,xx,y0),r1=residual_x(k,xx,y1);if(r0||r1)nondeg=1;
    if(r1==0){if(r0)return 0;}else{any_u1=1;u32 g=mulm(subm(0,r0),invm(r1));if(!gam_set){gam=g;gam_set=1;}else if(gam!=g)return 0;}
    int i=k;while(i>=0&&comb[i]==a-(k+1)+i)i--;if(i<0)break;comb[i]++;for(int j=i+1;j<=k;j++)comb[j]=comb[j-1]+1;}
  if(!nondeg)return 0;if(!any_u1)return 0;*gam_out=gam;return 1;}

int main(int argc,char**argv){
  int n=atoi(argv[1]),r=atoi(argv[2]),e=atoi(argv[3]),f=atoi(argv[4]);
  int a=argc>5?atoi(argv[5]):r+1;
  int kc=(r-2)+1;make_dom(n);
  int idx[40];for(int i=0;i<a;i++)idx[i]=i;
  while(1){
    u32 xv[40];for(int i=0;i<a;i++)xv[i]=dom[idx[i]];
    u32 gam;
    if(gamma_of_xset(kc,a,xv,e,f,&gam)){
      /* rotate S by g: multiply each x by GEN */
      u32 gxv[40];for(int i=0;i<a;i++)gxv[i]=mulm(xv[i],GEN);
      u32 ggam;int gok=gamma_of_xset(kc,a,gxv,e,f,&ggam);
      /* ratio ggam/gam */
      u32 ratio=0;int hasr=0;
      if(gok&&gam!=0&&ggam!=0){ratio=mulm(ggam,invm(gam));hasr=1;}
      /* dilation by GEN^2 (square of rotation): */
      u32 g2xv[40];for(int i=0;i<a;i++)g2xv[i]=mulm(xv[i],mulm(GEN,GEN));
      u32 g2gam;int g2ok=gamma_of_xset(kc,a,g2xv,e,f,&g2gam);
      printf("gam=%u ggam=%u gok=%d ratio=%u hasr=%d g2gam=%u g2ok=%d\n",gam,ggam,gok,ratio,hasr,g2gam,g2ok);
    }
    int i=a-1;while(i>=0&&idx[i]==N-a+i)i--;if(i<0)break;idx[i]++;for(int j=i+1;j<a;j++)idx[j]=idx[j-1]+1;
  }
  return 0;
}
