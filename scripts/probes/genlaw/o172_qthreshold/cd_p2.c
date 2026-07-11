/* second-prime q-independence check: deep band #bad for high-freq monomial, prime configurable */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t u32; typedef uint64_t u64;
static u64 P;
static u32 mulm(u32 a,u32 b){return (u32)((u64)a*b%P);}
static u32 subm(u32 a,u32 b){return a>=b?a-b:(u32)((u64)a+P-b);}
static u32 powm(u32 a,u64 e){u64 r=1,b=a%P;while(e){if(e&1)r=r*b%P;b=b*b%P;e>>=1;}return(u32)r;}
static u32 invm(u32 a){return powm(a,P-2);}
static int N; static u32 dom[64],U0[64],U1[64];
static void make_dom(int n){N=n;u64 e=(P-1)/n;for(u32 c=2;c<2000;c++){u32 h=powm(c,e);if(powm(h,n)==1&&powm(h,n/2)!=1){u32 cur=1;for(int i=0;i<n;i++){dom[i]=cur;cur=mulm(cur,h);}return;}}fprintf(stderr,"no root\n");exit(1);}
static u32 detm(u32*M,int m){u32 d=1;for(int col=0;col<m;col++){int piv=-1;for(int rr=col;rr<m;rr++)if(M[rr*m+col]){piv=rr;break;}if(piv<0)return 0;if(piv!=col){for(int c=0;c<m;c++){u32 t=M[piv*m+c];M[piv*m+c]=M[col*m+c];M[col*m+c]=t;}d=subm(0,d);}d=mulm(d,M[col*m+col]);u32 inv=invm(M[col*m+col]);for(int rr=col+1;rr<m;rr++)if(M[rr*m+col]){u32 f=mulm(M[rr*m+col],inv);for(int c=col;c<m;c++)M[rr*m+c]=subm(M[rr*m+c],mulm(f,M[col*m+c]));}}return d;}
static u32 residual(int k,const int*t,const u32*y){int m=k+1;u32 M[64];for(int a=0;a<m;a++){for(int b=0;b<k;b++)M[a*m+b]=powm(dom[t[a]],b);M[a*m+k]=y[t[a]];}return detm(M,m);}
static int aligned_set(int k,const int*Sidx,int a,u32*go,int*hg){int comb[8];for(int i=0;i<=k;i++)comb[i]=i;int gs=0;u32 g=0;int nd=0,au=0;while(1){int t[8];for(int i=0;i<=k;i++)t[i]=Sidx[comb[i]];u32 r0=residual(k,t,U0),r1=residual(k,t,U1);if(r0||r1)nd=1;if(r1==0){if(r0)return 0;}else{au=1;u32 gg=mulm(subm(0,r0),invm(r1));if(!gs){g=gg;gs=1;}else if(g!=gg)return 0;}int i=k;while(i>=0&&comb[i]==a-(k+1)+i)i--;if(i<0)break;comb[i]++;for(int j=i+1;j<=k;j++)comb[j]=comb[j-1]+1;}if(!nd)return 0;*hg=au;if(au)*go=g;return 1;}
#define HB 21
#define HS (1u<<HB)
static u32*ht;static int hu;
static void hr(){if(!ht)ht=malloc(HS*4);memset(ht,0xff,HS*4);hu=0;}
static void ha(u32 v){u32 k=v==0xffffffffu?0:v;u32 h=(u32)(((u64)k*2654435761u)>>(32-HB))&(HS-1);while(ht[h]!=0xffffffffu){if(ht[h]==k)return;h=(h+1)&(HS-1);}ht[h]=k;hu++;}
static u64 cb(int k,int a){hr();u64 al=0;int idx[40];for(int i=0;i<a;i++)idx[i]=i;while(1){u32 g;int hg;if(aligned_set(k,idx,a,&g,&hg)){al++;if(hg)ha(g);}int i=a-1;while(i>=0&&idx[i]==N-a+i)i--;if(i<0)break;idx[i]++;for(int j=i+1;j<a;j++)idx[j]=idx[j-1]+1;}(void)al;return(u64)hu;}
int main(int c,char**v){P=strtoull(v[1],0,10);int n=atoi(v[2]),r=atoi(v[3]),e=atoi(v[4]),f=atoi(v[5]),a=atoi(v[6]);make_dom(n);int kc=(r-2)+1;for(int i=0;i<n;i++){U0[i]=powm(dom[i],e);U1[i]=powm(dom[i],f);}u64 bad=cb(kc,a);printf("p=%llu n=%d r=%d (x^%d,x^%d) a=%d: #bad=%llu\n",(unsigned long long)P,n,r,e,f,a,(unsigned long long)bad);return 0;}
