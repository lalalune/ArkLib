// Exact floor-bad scanner for the off-BGK δ* floor (KB bad-prime-localization §1).
// p in B(n) iff some adjacent 7th-type pattern A is realizable over F_p:
//   rank[M_A] == rank[M_A | b_A], M_A=[x^0..x^{n/2-1} | -x^{n/2}]_{x in A}, b_A=x^{3n/4}.
// Validated against n=16 ground truth (17->160/2304, others 0).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef long long ll;
static ll P;

static ll pw(ll a, ll e){ a%=P; if(a<0)a+=P; ll r=1; while(e){ if(e&1) r=r*a%P; a=a*a%P; e>>=1;} return r; }
static ll inv(ll a){ return pw(a,P-2); }

// rank of (nr x nc) matrix mod P (destroys M)
static int rankmod(ll *M, int nr, int nc){
    int rank=0;
    for(int col=0; col<nc && rank<nr; col++){
        int piv=-1;
        for(int r=rank;r<nr;r++){ if(M[r*nc+col]%P!=0){piv=r;break;} }
        if(piv<0) continue;
        for(int c=0;c<nc;c++){ ll t=M[rank*nc+c]; M[rank*nc+c]=M[piv*nc+c]; M[piv*nc+c]=t; }
        ll iv=inv(M[rank*nc+col]);
        for(int c=0;c<nc;c++) M[rank*nc+c]=M[rank*nc+c]*iv%P;
        for(int r=0;r<nr;r++){
            if(r!=rank){ ll f=M[r*nc+col]%P; if(f){ for(int c=0;c<nc;c++){ ll v=M[r*nc+c]-f*M[rank*nc+c]%P; v%=P; if(v<0)v+=P; M[r*nc+c]=v; } } }
        }
        rank++;
    }
    return rank;
}

static int isprime(ll n){ if(n<2)return 0; for(ll d=2;d*d<=n;d++) if(n%d==0) return 0; return 1; }
static ll generator(ll p){
    // factor p-1
    ll m=p-1; ll fac[64]; int nf=0; ll mm=m;
    for(ll d=2; d*d<=mm; d++){ if(mm%d==0){ fac[nf++]=d; while(mm%d==0)mm/=d; } }
    if(mm>1) fac[nf++]=mm;
    for(ll h=2; h<p; h++){ int ok=1; for(int i=0;i<nf;i++){ if(pw(h,(p-1)/fac[i])==1){ok=0;break;} } if(ok) return h; }
    return -1;
}

// choose: fill combos[][k] with all C(setsize,k) subsets of {0..setsize-1}; returns count
static int build_combos(int setsize, int k, int combos[][8]){
    int idx[8]; for(int i=0;i<k;i++) idx[i]=i; int cnt=0;
    while(1){
        for(int i=0;i<k;i++) combos[cnt][i]=idx[i];
        cnt++;
        int i=k-1; while(i>=0 && idx[i]==setsize-k+i) i--;
        if(i<0) break;
        idx[i]++; for(int j=i+1;j<k;j++) idx[j]=idx[j-1]+1;
    }
    return cnt;
}

// scan prime p at subgroup order n. shortcircuit: stop at first realizable.
// returns realizable count (or -1 if shortcircuit hit, with *hit set). prints progress.
static ll scan(ll p, int n, int shortcircuit){
    P=p;
    int m=n/4, half=n/2, deg34=3*n/4;
    int agr_min=m-m/4, agr_maj=m-m/2; // n=32: 6,4 ; n=16: 3,2
    ll g0=pw(generator(p),(p-1)/n);
    // domain + precomputed rows
    int N=n;
    ll *Xrow=malloc(sizeof(ll)*N*(half+2)); // row(j): half+1 cols of M, plus b at index half+1
    for(int j=0;j<N;j++){
        ll x=pw(g0,j);
        for(int k=0;k<half;k++) Xrow[j*(half+2)+k]=pw(x,k);
        Xrow[j*(half+2)+half]=(P-pw(x,half))%P;     // -x^{half}
        Xrow[j*(half+2)+half+1]=pw(x,deg34);        // b = x^{3n/4}
    }
    // classes
    int cls[4][8]; for(int c=0;c<4;c++){ int t=0; for(int j=0;j<N;j++) if(j%4==c) cls[c][t++]=j; }
    // combos within a class of size m=n/4
    static int cmin[256][8], cmaj[256][8];
    int nmin=build_combos(m, agr_min, cmin);
    int nmaj=build_combos(m, agr_maj, cmaj);
    int Asz=2*agr_min+2*agr_maj; // |A|
    int nc=half+2;               // augmented columns (half+1 of M + 1 for b)
    ll *Mat=malloc(sizeof(ll)*Asz*nc);
    ll count=0, total=0;
    for(int c0=0;c0<4;c0++){
        int mn0=c0, mn1=(c0+1)%4, mj0=(c0+2)%4, mj1=(c0+3)%4;
        for(int a=0;a<nmin;a++) for(int b=0;b<nmin;b++) for(int d=0;d<nmaj;d++) for(int e=0;e<nmaj;e++){
            // build A
            int A[40]; int t=0;
            for(int i=0;i<agr_min;i++) A[t++]=cls[mn0][cmin[a][i]];
            for(int i=0;i<agr_min;i++) A[t++]=cls[mn1][cmin[b][i]];
            for(int i=0;i<agr_maj;i++) A[t++]=cls[mj0][cmaj[d][i]];
            for(int i=0;i<agr_maj;i++) A[t++]=cls[mj1][cmaj[e][i]];
            // M_A (cols 0..half) rank, then augmented rank
            for(int r=0;r<Asz;r++){ int jj=A[r]; for(int c=0;c<half+1;c++) Mat[r*nc+c]=Xrow[jj*(half+2)+c]; }
            int rM=rankmod(Mat, Asz, half+1); // only first half+1 cols
            for(int r=0;r<Asz;r++){ int jj=A[r]; for(int c=0;c<nc;c++) Mat[r*nc+c]=Xrow[jj*(half+2)+c]; }
            int rA=rankmod(Mat, Asz, nc);
            total++;
            if(rA==rM){ count++; if(shortcircuit){ free(Xrow);free(Mat); return count; } }
        }
    }
    free(Xrow); free(Mat);
    return count;
}

int main(int argc, char**argv){
    // n=16 self-validation
    fprintf(stderr,"[validate n=16] expect 17->160, others 0\n");
    int v16[]={17,97,113,193,241,257,0};
    for(int i=0;v16[i];i++){ ll c=scan(v16[i],16,0); printf("n=16 p=%d realizable=%lld -> %s\n",v16[i],c,c>0?"BAD":"good"); fflush(stdout);}
    // n=32 candidate primes (smallest few primes ≡1 mod 32 and the disputed ones)
    printf("--- n=32 scan ---\n"); fflush(stdout);
    int cand[]={97,193,257,353,449,577,673,929,1153,1217,1249,0};
    for(int i=0;cand[i];i++){ int p=cand[i]; if((p-1)%32||!isprime(p)) continue;
        // single short-circuit scan: returns 1 quickly if BAD, else fully scans 15.4M and returns 0 (good)
        ll sc=scan(p,32,1);
        printf("n=32 p=%d -> %s%s\n", p, sc>0?"BAD":"good", sc>0?" (>=1 adjacent pattern realizable)":" (0 of 15366400 realizable, fully scanned)"); fflush(stdout);
    }
    return 0;
}
