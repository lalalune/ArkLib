/* PER-PRIME FALSIFIER for the O130 marginal-layer counts (issue #232 lane).
 *
 * Pattern (b,r) at scale s (n = 2s): class = (O, m) = r odd-rooted fibers
 * O = {o_1<...<o_r} (subset of Z_s) + sign mask m in [0, 2^{r-1})
 * (d_1 = 0, d_i = (m>>(i-1))&1; global negation quotiented).  B = b-subset of
 * Z_s \ O,  b = (s+1-r)/2.   Marginal-layer membership of (B,O,m) mod p is
 * EXACTLY ONE linear equation (verified against raw polynomial arithmetic in
 * verify_reduction.py — coeff(X^s) of e equals LAM - alpha identically):
 *     Sum_{c in B} G[c]  ==  target(O,m) := ZS - (e2(x) + e1(O_z))   (mod p)
 * with G[c] = H[2c], x_i = H[o_i + s d_i], ZS = H[s/2], LAM = p - ZS.
 *
 * char-0 truth per class: the DERIVED-672 placement rule  C(v, (b-h)/2)
 * (re-implemented here independently; cross-checked vs audit_sweep64 rec).
 * spurious(p, class) = modp_count - char0_count  (>= 0 always, since the
 * ring hom Z[zeta_n] -> F_p, zeta -> H[1], preserves char-0 solutions).
 *
 * modes:
 *   scan  [nw wid] [rec] [mitm|brute|both]   exhaustive over all (O,m)
 *   class o1,o2,...,or m                     full brute of ONE class; dumps
 *                                            every spurious B explicitly
 * usage: falsify s r p g0 mode ...
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint32_t u32;
typedef uint64_t u64;

static u64 P;
static int Sc, N, A, R, Bsz, M, ML, MR;
static u32 Hh[64], Gz[32], ZS, LAM;
static u64 C[70][70];
static int NW = 1, WID = 0, PRINTREC = 0;
static int DO_MITM = 1, DO_BRUTE = 0;

static inline u32 addm(u32 a, u32 b){ u64 t=(u64)a+b; return t>=P?(u32)(t-P):(u32)t; }
static inline u32 subm(u32 a, u32 b){ return a>=b? a-b : (u32)((u64)a+P-b); }
static inline u32 mulm(u32 a, u32 b){ return (u32)((u64)a*b%P); }
static u32 powm(u32 a, u64 e){ u64 r=1,b=a%P; while(e){ if(e&1) r=r*b%P; b=b*b%P; e>>=1; } return (u32)r; }

/* ---- per-O state ---- */
static int O[8], cand[32];
static u32 wl[16], wr[16];
static u32 lsum[1u<<15], rsum[1u<<15], lv[1u<<15];
static u64 ka[1u<<15], kb[1u<<15];
static long loff[20];                     /* static popcount offsets in lv */

/* ---- totals ---- */
static u64 t_classes=0, t_feas=0, t_char0=0, t_modp=0;
static u64 t_spur_classes=0, t_spur_excess=0, t_xih=0, t_xih_feas=0, t_mm=0;
static u64 ocount=0;

static u64 placement(long m, int *hout, int *vout, int *forced, int *freeax){
    int a[8], cnt[64];
    memset(cnt, 0, sizeof(int)*N);
    a[0]=O[0];
    for(int i=1;i<R;i++) a[i]=O[i]+Sc*((m>>(i-1))&1);
    for(int i=0;i<R;i++) for(int j=i+1;j<R;j++) cnt[(a[i]+a[j])%N]++;
    for(int i=0;i<R;i++) cnt[(2*O[i])%N]++;
    cnt[(3*Sc/2)%N]++;
    for(int t=1;t<Sc;t+=2) if(cnt[t]!=cnt[t+Sc]) return 0;
    u64 om=0; for(int i=0;i<R;i++) om |= 1ull<<O[i];
    int h=0, v=0;
    for(int c=0;c<A;c++){
        int dd = cnt[2*c]-cnt[2*c+Sc];
        if(dd>1 || dd<-1) return 0;
        if(dd==-1){ if(om&(1ull<<c)) return 0; if(forced) forced[h]=c; h++; }
        else if(dd==1){ if(om&(1ull<<(c+A))) return 0; if(forced) forced[h]=c+A; h++; }
        else if(!(om&(1ull<<c)) && !(om&(1ull<<(c+A)))){ if(freeax) freeax[v]=c; v++; }
    }
    *hout=h; *vout=v;
    int rem=Bsz-h;
    if(rem<0 || (rem&1)) return 0;
    int k=rem/2;
    if(k>v) return 0;
    return C[v][k];
}

static void class_data(long m, u32 *target, int *xih){
    int a[8]; u32 x[8];
    a[0]=O[0];
    for(int i=1;i<R;i++) a[i]=O[i]+Sc*((m>>(i-1))&1);
    for(int i=0;i<R;i++) x[i]=Hh[a[i]];
    u32 e2=0, sx=0;
    for(int i=0;i<R;i++){
        for(int j=i+1;j<R;j++) e2=addm(e2, mulm(x[i],x[j]));
        sx=addm(sx, x[i]);
    }
    u32 fix=e2;
    for(int i=0;i<R;i++) fix=addm(fix, Gz[O[i]]);
    *target = subm(ZS, fix);
    u32 xi = sx? (u32)(P-sx) : 0;          /* xi = -(sum x_i) */
    *xih = (xi==0);
    for(int i=0;i<N && !*xih;i++) if(Hh[i]==xi) *xih=1;
}

static void radix_sort_left(void){
    long n = 1l<<ML;
    for(long msk=1; msk<n; msk++)
        lsum[msk] = addm(lsum[msk & (msk-1)], wl[__builtin_ctzl(msk)]);
    for(long msk=0; msk<n; msk++)
        ka[msk] = ((u64)__builtin_popcountl(msk)<<32) | lsum[msk];
    for(int pass=0; pass<5; pass++){
        long cnt[256]; memset(cnt,0,sizeof cnt);
        int sh = pass*8;
        for(long i=0;i<n;i++) cnt[(ka[i]>>sh)&255]++;
        long acc=0;
        for(int b=0;b<256;b++){ long c=cnt[b]; cnt[b]=acc; acc+=c; }
        for(long i=0;i<n;i++) kb[cnt[(ka[i]>>sh)&255]++] = ka[i];
        memcpy(ka, kb, sizeof(u64)*n);
    }
    for(long i=0;i<n;i++) lv[i]=(u32)ka[i];
    loff[0]=0;
    for(int k=0;k<=ML;k++) loff[k+1]=loff[k]+(long)C[ML][k];
}

static inline long rng_count(const u32 *a, long n, u32 v){
    long lo=0, hi=n;
    while(lo<hi){ long md=(lo+hi)>>1; if(a[md]<v) lo=md+1; else hi=md; }
    long lb=lo; hi=n;
    while(lo<hi){ long md=(lo+hi)>>1; if(a[md]<=v) lo=md+1; else hi=md; }
    return lo-lb;
}

static void build_tables(void){
    int ci=0;
    u64 om=0; for(int i=0;i<R;i++) om |= 1ull<<O[i];
    for(int c=0;c<Sc;c++) if(!(om&(1ull<<c))) cand[ci++]=c;
    for(int i=0;i<ML;i++) wl[i]=Gz[cand[i]];
    for(int i=0;i<MR;i++) wr[i]=Gz[cand[ML+i]];
    radix_sort_left();
    long n=1l<<MR;
    for(long msk=1; msk<n; msk++)
        rsum[msk] = addm(rsum[msk & (msk-1)], wr[__builtin_ctzl(msk)]);
    rsum[0]=0; lsum[0]=0;
}

static u64 mitm_count(u32 target){
    u64 cnt=0;
    long n=1l<<MR;
    for(long msk=0; msk<n; msk++){
        int t=__builtin_popcountl(msk);
        int k2=Bsz-t;
        if(k2<0 || k2>ML) continue;
        cnt += rng_count(lv+loff[k2], (long)C[ML][k2], subm(target, rsum[msk]));
    }
    return cnt;
}

static u64 brute_count(u32 target){
    /* Gosper over C(M,Bsz) masks; sum via the two half tables */
    u64 cnt=0;
    long lim=1l<<M, lomask=(1l<<ML)-1;
    long msk=(1l<<Bsz)-1;
    while(msk<lim){
        if(addm(lsum[msk&lomask], rsum[msk>>ML])==target) cnt++;
        long c=msk&-msk, r2=msk+c;
        msk = r2 | (((msk^r2)>>2)/c);
        if(Bsz==0) break;
    }
    return cnt;
}

static void process_O(void){
    build_tables();
    int forced[32], freeax[32], h=0, v=0;
    for(long m=0; m<(1l<<(R-1)); m++){
        u32 target; int xih;
        class_data(m, &target, &xih);
        u64 c0 = placement(m, &h, &v, forced, freeax);
        u64 mp=0, bp=0;
        if(DO_MITM) mp = mitm_count(target);
        if(DO_BRUTE) bp = brute_count(target);
        if(DO_MITM && DO_BRUTE && mp!=bp){
            t_mm++;
            printf("MM O=");
            for(int i=0;i<R;i++) printf("%s%d", i?",":"", O[i]);
            printf(" m=%ld mitm=%llu brute=%llu\n",
                   m,(unsigned long long)mp,(unsigned long long)bp);
        }
        if(!DO_MITM) mp=bp;
        t_classes++; t_char0+=c0; t_modp+=mp;
        if(c0) t_feas++;
        if(xih){ t_xih++; if(c0) t_xih_feas++;
            printf("XI O=");
            for(int i=0;i<R;i++) printf("%s%d", i?",":"", O[i]);
            printf(" m=%ld char0=%llu (xi in mu_n or 0 mod p)\n",
                   m,(unsigned long long)c0);
        }
        if(mp!=c0){
            t_spur_classes++; t_spur_excess += mp-c0;
            printf("SPUR O=");
            for(int i=0;i<R;i++) printf("%s%d", i?",":"", O[i]);
            printf(" m=%ld char0=%llu modp=%llu\n",
                   m,(unsigned long long)c0,(unsigned long long)mp);
        }
        if(PRINTREC && c0){
            printf("C0REC");
            for(int i=0;i<R;i++) printf(" %d", O[i]);
            printf(" | %ld | h %d :", m, h);
            for(int i=0;i<h;i++) printf(" %d", forced[i]);
            printf(" | v %d :", v);
            for(int i=0;i<v;i++) printf(" %d", freeax[i]);
            printf(" | w %llu\n", (unsigned long long)c0);
        }
    }
}

static void rec_O(int depth, int start){
    if(depth==R){ if((ocount++ % NW)==(u64)WID) process_O(); return; }
    for(int x=start; x<Sc; x++){ O[depth]=x; rec_O(depth+1, x+1); }
}

static void class_mode(const char *ospec, long m){
    char buf[128]; strncpy(buf, ospec, 127); buf[127]=0;
    int i=0;
    for(char *t=strtok(buf,","); t; t=strtok(NULL,","), i++) O[i]=atoi(t);
    if(i!=R){ fprintf(stderr,"need %d O entries\n",R); exit(2); }
    build_tables();
    u32 target; int xih, h, v, forced[32], freeax[32];
    class_data(m, &target, &xih);
    u64 c0 = placement(m, &h, &v, forced, freeax);
    u64 mp = mitm_count(target);
    /* full brute with explicit spurious dump + independent balance check */
    int basecnt[64]; memset(basecnt,0,sizeof(int)*N);
    int a[8]; a[0]=O[0];
    for(int j=1;j<R;j++) a[j]=O[j]+Sc*((m>>(j-1))&1);
    for(int j=0;j<R;j++) for(int k=j+1;k<R;k++) basecnt[(a[j]+a[k])%N]++;
    for(int j=0;j<R;j++) basecnt[(2*O[j])%N]++;
    basecnt[(3*Sc/2)%N]++;
    u64 bcnt=0, genuine=0, spur=0;
    long lim=1l<<M, lomask=(1l<<ML)-1, msk=(1l<<Bsz)-1;
    while(msk<lim){
        if(addm(lsum[msk&lomask], rsum[msk>>ML])==target){
            bcnt++;
            int cnt[64]; memcpy(cnt, basecnt, sizeof(int)*N);
            for(int j=0;j<M;j++) if(msk&(1l<<j)) cnt[(2*cand[j])%N]++;
            int bal=1;
            for(int t=0;t<Sc;t++) if(cnt[t]!=cnt[t+Sc]) { bal=0; break; }
            if(bal) genuine++;
            else{
                spur++;
                if(spur<=1000){
                    printf("SPUR_B O=");
                    for(int j=0;j<R;j++) printf("%s%d", j?",":"", O[j]);
                    printf(" m=%ld B=", m);
                    int first=1;
                    for(int j=0;j<M;j++) if(msk&(1l<<j)){
                        printf("%s%d", first?"":",", cand[j]); first=0; }
                    printf("\n");
                }
            }
        }
        long c=msk&-msk, r2=msk+c;
        msk = r2 | (((msk^r2)>>2)/c);
    }
    printf("CLASS s=%d r=%d p=%llu O=%s m=%ld char0=%llu mitm=%llu "
           "brute=%llu genuine_bal=%llu spurious=%llu xiH=%d\n",
           Sc, R, (unsigned long long)P, ospec, m,
           (unsigned long long)c0,(unsigned long long)mp,
           (unsigned long long)bcnt,(unsigned long long)genuine,
           (unsigned long long)spur, xih);
}

int main(int argc, char **argv){
    if(argc<6){ fprintf(stderr,"usage: %s s r p g0 mode ...\n",argv[0]); return 2; }
    Sc=atoi(argv[1]); R=atoi(argv[2]);
    P=strtoull(argv[3],NULL,10);
    u32 g0=(u32)strtoull(argv[4],NULL,10);
    N=2*Sc; A=Sc/2; Bsz=(Sc+1-R)/2; M=Sc-R; ML=M/2; MR=M-ML;
    if((P-1)%(u64)N){ fprintf(stderr,"p != 1 mod n\n"); return 2; }
    for(int i=0;i<70;i++){ C[i][0]=1; for(int j=1;j<=i;j++) C[i][j]=C[i-1][j-1]+C[i-1][j]; }
    u32 h = powm(g0,(P-1)/(u64)N);
    Hh[0]=1;
    for(int i=1;i<N;i++) Hh[i]=mulm(Hh[i-1],h);
    if(Hh[Sc]!=P-1 || mulm(Hh[N-1],h)!=1){ fprintf(stderr,"bad root order\n"); return 2; }
    for(int c=0;c<Sc;c++) Gz[c]=Hh[(2*c)%N];
    ZS=Hh[Sc/2]; LAM=(u32)(P-ZS);
    const char *mode=argv[5];
    if(!strcmp(mode,"class")){
        if(argc<8){ fprintf(stderr,"class needs O m\n"); return 2; }
        class_mode(argv[6], atol(argv[7]));
        return 0;
    }
    int ai=6;
    if(argc>ai+1 && argv[ai][0]>='0' && argv[ai][0]<='9'){
        NW=atoi(argv[ai]); WID=atoi(argv[ai+1]); ai+=2; }
    for(; ai<argc; ai++){
        if(!strcmp(argv[ai],"rec")) PRINTREC=1;
        else if(!strcmp(argv[ai],"brute")){ DO_BRUTE=1; DO_MITM=0; }
        else if(!strcmp(argv[ai],"both")){ DO_BRUTE=1; DO_MITM=1; }
    }
    rec_O(0,0);
    printf("SUMMARY s=%d r=%d p=%llu w=%d/%d mode=%s%s classes=%llu feas=%llu "
           "char0_sum=%llu modp_sum=%llu spur_classes=%llu spur_excess=%llu "
           "xiH=%llu xiH_feas=%llu mitm_brute_mismatch=%llu\n",
           Sc,R,(unsigned long long)P,WID,NW,
           DO_MITM?(DO_BRUTE?"both":"mitm"):"brute", PRINTREC?"+rec":"",
           (unsigned long long)t_classes,(unsigned long long)t_feas,
           (unsigned long long)t_char0,(unsigned long long)t_modp,
           (unsigned long long)t_spur_classes,(unsigned long long)t_spur_excess,
           (unsigned long long)t_xih,(unsigned long long)t_xih_feas,
           (unsigned long long)t_mm);
    fprintf(stderr,"done s=%d r=%d p=%llu w=%d/%d\n",Sc,R,
            (unsigned long long)P,WID,NW);
    return t_mm?3:0;
}
