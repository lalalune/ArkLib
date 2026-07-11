/* Parallel-split pattern sweep at s=32: like sweep32.c but only processes
   subsets whose FIRST element f satisfies f % NW == WID (args: r NW WID). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define S 32
#define N 64
#define A 16
static int R, B, NW, WID;
static long long total = 0;
static long long binom[40][40];
static void initbinom(void){for(int i=0;i<40;i++){binom[i][0]=1;for(int j=1;j<=i;j++)binom[i][j]=binom[i-1][j-1]+(j<=i-1?binom[i-1][j]:0);}}
static void process(const int *O){
    unsigned Omask=0; for(int i=0;i<R;i++) Omask|=1u<<O[i];
    for(long m=0;m<(1L<<(R-1));m++){
        int a[16]; a[0]=O[0];
        for(int i=1;i<R;i++) a[i]=O[i]+S*((m>>(i-1))&1);
        signed char cnt[N]; memset(cnt,0,N);
        for(int i=0;i<R;i++) for(int j=i+1;j<R;j++) cnt[(a[i]+a[j])%N]++;
        for(int i=0;i<R;i++) cnt[(2*O[i])%N]++;
        cnt[48]++;
        int ok=1;
        for(int mm=1;mm<S&&ok;mm+=2) if(cnt[mm]!=cnt[mm+S]) ok=0;
        if(!ok) continue;
        int h=0,v=0;
        for(int c=0;c<A&&ok;c++){
            int d=cnt[2*c]-cnt[(2*c+S)%N];
            if(d<-1||d>1){ok=0;break;}
            if(d==-1){ if(Omask&(1u<<c)){ok=0;break;} h++; }
            else if(d==1){ if(Omask&(1u<<(c+A))){ok=0;break;} h++; }
            else { if(!(Omask&(1u<<c))&&!(Omask&(1u<<(c+A)))) v++; }
        }
        if(!ok) continue;
        if(h<=B&&(B-h)%2==0&&(B-h)/2<=v) total+=binom[v][(B-h)/2];
    }
}
static void rec(int *O,int depth,int start){
    if(depth==3 && ((O[0]*1024+O[1]*32+O[2])%NW)!=WID) return;
    if(depth==R){process(O);return;}
    for(int x=start;x<S;x++){O[depth]=x;rec(O,depth+1,x+1);}
}
int main(int argc,char**argv){
    R=atoi(argv[1]); NW=atoi(argv[2]); WID=atoi(argv[3]);
    B=(S+1-R)/2; initbinom();
    int O[16];
    rec(O,0,0);
    printf("r=%d worker %d/%d: partial = %lld\n",R,WID,NW,total);
    return 0;
}
