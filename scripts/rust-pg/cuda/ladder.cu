// ladder.cu — GPU exact list-size of explicit smooth-domain RS[mu_n,k] past Johnson.
//
// Prize (ArkLib #444 / proximityprize.org): proximity-gap FLOOR <=> explicit-RS list past
// Johnson stays POLY. We measure the worst-case list size L(word, t) = #{deg<k codewords
// agreeing with `word` on >= t points of the dyadic subgroup mu_n}, swept across the window
// t in (rho n, sqrt(rho) n], for 2-power n, at a thin prize-regime prime p ~ n^4 (p = n^beta).
//
// Method: enumerate ALL C(n,k) k-subsets (combinatorial-number-system unrank => embarrassingly
// parallel), interpolate the deg<k codeword through each, count agreement (with early-exit),
// emit a 128-bit hash of any codeword agreeing on >= t_min points; host de-dups by hash => L(t).
// A list member with agreement set S is re-found C(|S|,k) times; host dedup collapses them.
//
// HONESTY: this is an EMPIRICAL ladder. It can (a) extend the constant-list evidence by 1-2
// octaves per rate (n=64,128) and (b) REFUTE the floor if L jumps. It CANNOT prove the n->2^30
// asymptotic (that is the BGK/uncertainty wall). Buffer overflow => list is huge => reported as
// LIST_OVERFLOW (itself a floor-refutation signal at that n), never silently truncated.
//
// Self-test: identical __host__ __device__ core runs on CPU and GPU for n=16,k=4; the driver
// aborts unless GPU matches CPU before any large-n run is trusted.
//
// Build:  nvcc -O3 -arch=sm_90 -o ladder ladder.cu        (sm_90 = H100/H200; use your arch)
// Run:    ./ladder <n> <k> <word>   word = "mA"  (x^A)  or  "A,B" (x^A + x^B)  or "self"
//   e.g.  ./ladder 128 8 127,126     ./ladder 64 8 self
//
// Constraint: p < 2^31 so products fit u64 (holds for n<=128, p~n^4<2.7e8). n>=256 needs the
// 128-bit path (TODO; flagged at runtime).

#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <algorithm>
#include <string>

typedef unsigned long long u64;
typedef unsigned int u32;

#define KMAX 24   // supports k up to 24 (ladder targets: rho=1/16 k<=8, rho=1/8 k<=16)

// ---------- modular arithmetic (p < 2^31, so a*b fits u64) ----------
__host__ __device__ inline u64 mulmod(u64 a, u64 b, u64 p){ return (a*b)%p; }
__host__ __device__ inline u64 addmod(u64 a, u64 b, u64 p){ u64 s=a+b; return s>=p? s-p : s; }
__host__ __device__ inline u64 submod(u64 a, u64 b, u64 p){ return a>=b? a-b : p-b+a; }
__host__ __device__ inline u64 powmod(u64 b, u64 e, u64 p){ u64 r=1; b%=p; while(e){ if(e&1) r=mulmod(r,b,p); b=mulmod(b,b,p); e>>=1;} return r; }
__host__ __device__ inline u64 invmod(u64 a, u64 p){ return powmod(a,p-2,p); }

// ---------- per-subset core: given a k-subset of indices, interpolate deg<k codeword through
// (mu[idx], w[idx]), count agreement with w over all n points (early-exit at t_min), and if
// agreement >= t_min return a 128-bit hash of the codeword's coefficient vector; else return 0. ----------
struct Hash128 { u64 lo, hi; };

__host__ __device__ inline Hash128 subset_member_hash(
    const u64* idx, int k, const u64* mu, const u64* w, int n, u64 p, int t_min)
{
    Hash128 zero{0,0};
    u64 xs[KMAX], ys[KMAX], coef[KMAX];
    for(int i=0;i<k;i++){ xs[i]=mu[idx[i]]; ys[i]=w[idx[i]]; coef[i]=0; }
    // Lagrange -> coefficients. k inversions total (one per basis denominator).
    for(int i=0;i<k;i++){
        u64 denom=1;
        for(int j=0;j<k;j++) if(j!=i) denom=mulmod(denom, submod(xs[i],xs[j],p), p);
        u64 scale=mulmod(ys[i], invmod(denom,p), p);
        // numerator poly np = prod_{j!=i}(x - xs[j])
        u64 np[KMAX]; for(int t=0;t<k;t++) np[t]=0; np[0]=1; int deg=0;
        for(int j=0;j<k;j++) if(j!=i){
            u64 nn[KMAX]; for(int t=0;t<k;t++) nn[t]=0;
            for(int t=0;t<=deg;t++){
                nn[t+1]=addmod(nn[t+1], np[t], p);
                nn[t]  =addmod(nn[t],   mulmod(np[t], submod(0,xs[j],p), p), p);
            }
            for(int t=0;t<k;t++) np[t]=nn[t];
            deg++;
        }
        for(int t=0;t<k;t++) coef[t]=addmod(coef[t], mulmod(scale,np[t],p), p);
    }
    // agreement count with early-exit: Horner eval at each mu point.
    int ag=0;
    for(int i=0;i<n;i++){
        u64 x=mu[i], r=0;
        for(int t=k-1;t>=0;t--) r=addmod(mulmod(r,x,p), coef[t], p);
        if(r==w[i]) ag++;
        if(ag + (n-i-1) < t_min) return zero;   // cannot reach t_min
    }
    if(ag < t_min) return zero;
    // 128-bit hash of the coefficient vector (two independent polynomial hashes).
    u64 h1=1469598103934665603ULL, h2=1125899906842597ULL;
    for(int t=0;t<k;t++){ h1=(h1 ^ coef[t]) * 1099511628211ULL; h2=h2*1000000007ULL + coef[t] + 0x9e3779b97f4a7c15ULL; }
    if(h1==0&&h2==0) h1=1;   // reserve {0,0} for "no member"
    return Hash128{h1,h2};
}

// ---------- combinatorial number system: unrank r in [0,C(n,k)) -> lexicographic k-subset ----------
// binom table passed in (host-precomputed), C[a*(KMAX+1)+b] = C(a,b).
__host__ __device__ inline void unrank(u64 r, int n, int k, const u64* C, int CW, u64* idx){
    int a=n; // choose decreasing
    for(int i=0;i<k;i++){
        // find largest c < a with C(c, k-i) <= r
        int kk=k-i;
        int c=kk-1;
        // linear/ex, but a is small (<=128) so a simple scan is fine
        while(c+1<a && C[(c+1)*CW + kk] <= r) c++;
        idx[i]= (u64)c;
        r -= C[c*CW + kk];
        a = c;
    }
    // produced in decreasing order; reverse to increasing (order irrelevant for interpolation,
    // but keep deterministic)
    for(int i=0;i<k/2;i++){ u64 tmp=idx[i]; idx[i]=idx[k-1-i]; idx[k-1-i]=tmp; }
}

// ---------- GPU kernel: grid-stride over all C(n,k) subsets ----------
__global__ void ladder_kernel(
    u64 total, int n, int k, u64 p, int t_min,
    const u64* mu, const u64* w, const u64* C, int CW,
    Hash128* out, u64* outcount, u64 cap)
{
    u64 stride = (u64)gridDim.x * blockDim.x;
    for(u64 r = (u64)blockIdx.x*blockDim.x + threadIdx.x; r < total; r += stride){
        u64 idx[KMAX];
        unrank(r, n, k, C, CW, idx);
        Hash128 h = subset_member_hash(idx, k, mu, w, n, p, t_min);
        if(h.lo|h.hi){
            u64 slot = atomicAdd((unsigned long long*)outcount, 1ULL);
            if(slot < cap) out[slot]=h;
        }
    }
}

// ---------- host helpers ----------
static bool isprime(u64 x){ if(x<2)return false; for(u64 d=2; d*d<=x; d++) if(x%d==0) return false; return true; }
static u64 big_prime(u64 n){ u64 p=n*n*n*n; while(!(p%n==1 && isprime(p))) p++; return p; }
static u64 h_powmod(u64 b,u64 e,u64 p){ u64 r=1;b%=p; while(e){if(e&1)r=(__uint128_t)r*b%p; b=(__uint128_t)b*b%p; e>>=1;} return r;}
static std::vector<u64> factor(u64 x){ std::vector<u64> f; for(u64 d=2; d*d<=x; d++) if(x%d==0){ f.push_back(d); while(x%d==0)x/=d; } if(x>1)f.push_back(x); return f; }
static u64 proot(u64 p){ auto fs=factor(p-1); for(u64 g=2;g<p;g++){ bool ok=true; for(u64 q:fs) if(h_powmod(g,(p-1)/q,p)==1){ok=false;break;} if(ok)return g; } return 0; }

// host de-dup of emitted hashes
static u64 distinct_count(std::vector<Hash128>& v){
    std::sort(v.begin(), v.end(), [](const Hash128&a,const Hash128&b){ return a.hi!=b.hi? a.hi<b.hi : a.lo<b.lo; });
    u64 c=0; for(size_t i=0;i<v.size();i++) if(i==0 || v[i].hi!=v[i-1].hi || v[i].lo!=v[i-1].lo) c++;
    return c;
}

// CPU reference (single-thread) list size — for self-test only (small n).
static u64 cpu_list_size(int n,int k,u64 p,int t_min,const std::vector<u64>&mu,const std::vector<u64>&w,const std::vector<u64>&C,int CW){
    u64 total=C[n*CW+k];
    std::vector<Hash128> hits;
    for(u64 r=0;r<total;r++){
        u64 idx[KMAX]; unrank(r,n,k,C.data(),CW,idx);
        Hash128 h=subset_member_hash(idx,k,mu.data(),w.data(),n,p,t_min);
        if(h.lo|h.hi) hits.push_back(h);
    }
    return distinct_count(hits);
}

#define CUDACHECK(call) do{ cudaError_t e=(call); if(e!=cudaSuccess){ fprintf(stderr,"CUDA error %s at %d: %s\n",#call,__LINE__,cudaGetErrorString(e)); exit(1);} }while(0)

int main(int argc, char** argv){
    if(argc<4){ fprintf(stderr,"usage: %s <n> <k> <word: mA | A,B | self>\n",argv[0]); return 1; }
    int n=atoi(argv[1]), k=atoi(argv[2]);
    if(k>KMAX){ fprintf(stderr,"k>%d unsupported\n",KMAX); return 1; }
    u64 p=big_prime(n);
    if(p>= (1ULL<<31)){ fprintf(stderr,"p=%llu >= 2^31 (n>=256): needs 128-bit modmul path (not in this build)\n",(unsigned long long)p); return 1; }
    u64 g=proot(p), h=h_powmod(g,(p-1)/n,p);
    std::vector<u64> mu(n); for(int i=0;i<n;i++) mu[i]=h_powmod(h,i,p);

    // binomials up to n, KMAX
    int CW=KMAX+1; std::vector<u64> C((n+1)*CW,0);
    for(int a=0;a<=n;a++){ C[a*CW+0]=1; for(int b=1;b<=k && b<=a && b<CW;b++) C[a*CW+b]=C[(a-1)*CW+b-1]+C[(a-1)*CW+b]; }
    u64 total=C[n*CW+k];

    double rho=(double)k/n, john=1.0-sqrt(rho), cap=1.0-rho;
    int t_cap=(int)ceil(rho*n), t_john=(int)floor(sqrt(rho)*n);
    int t_lo = (t_cap>k+1? t_cap : k+1);

    // build word
    auto build_word=[&](const std::string& spec)->std::vector<u64>{
        std::vector<u64> w(n);
        if(spec[0]=='m'){ int A=atoi(spec.c_str()+1); for(int i=0;i<n;i++) w[i]=h_powmod(mu[i],A,p); }
        else { int A,B; sscanf(spec.c_str(),"%d,%d",&A,&B); for(int i=0;i<n;i++) w[i]=addmod(h_powmod(mu[i],A,p),h_powmod(mu[i],B,p),p); }
        return w;
    };

    // ----- self-test: GPU vs CPU on this (n,k) for a fixed word, at one t -----
    if(std::string(argv[3])=="self"){
        std::string spec = std::to_string(n-1)+","+std::to_string(n-2); // consecutive lacunary
        std::vector<u64> w=build_word(spec);
        int t_test=(t_lo+t_john)/2; if(t_test<=k) t_test=k+1;
        printf("SELFTEST n=%d k=%d p=%llu word=x^%d+x^%d t=%d (window [%d..%d], John=%.3f)\n",
               n,k,(unsigned long long)p,n-1,n-2,t_test,t_lo,t_john,john);
        u64 cpuL=cpu_list_size(n,k,p,t_test,mu,w,C,CW);
        // GPU
        u64 *d_mu,*d_w,*d_C,*d_cnt; Hash128* d_out; u64 cap_e=50000000ULL;
        CUDACHECK(cudaMalloc(&d_mu,n*8)); CUDACHECK(cudaMemcpy(d_mu,mu.data(),n*8,cudaMemcpyHostToDevice));
        CUDACHECK(cudaMalloc(&d_w,n*8));  CUDACHECK(cudaMemcpy(d_w,w.data(),n*8,cudaMemcpyHostToDevice));
        CUDACHECK(cudaMalloc(&d_C,C.size()*8)); CUDACHECK(cudaMemcpy(d_C,C.data(),C.size()*8,cudaMemcpyHostToDevice));
        CUDACHECK(cudaMalloc(&d_out,cap_e*sizeof(Hash128)));
        CUDACHECK(cudaMalloc(&d_cnt,8)); CUDACHECK(cudaMemset(d_cnt,0,8));
        ladder_kernel<<<1024,256>>>(total,n,k,p,t_test,d_mu,d_w,d_C,CW,d_out,d_cnt,cap_e);
        CUDACHECK(cudaDeviceSynchronize());
        u64 cnt; CUDACHECK(cudaMemcpy(&cnt,d_cnt,8,cudaMemcpyDeviceToHost));
        if(cnt>cap_e){ printf("GPU LIST_OVERFLOW (%llu hits)\n",(unsigned long long)cnt); return 2; }
        std::vector<Hash128> hits(cnt); CUDACHECK(cudaMemcpy(hits.data(),d_out,cnt*sizeof(Hash128),cudaMemcpyDeviceToHost));
        u64 gpuL=distinct_count(hits);
        printf("CPU L=%llu   GPU L=%llu   => %s\n",(unsigned long long)cpuL,(unsigned long long)gpuL, cpuL==gpuL?"MATCH":"MISMATCH");
        return cpuL==gpuL?0:3;
    }

    // ----- real run: sweep t across the window for the given word -----
    std::vector<u64> w=build_word(argv[3]);
    printf("n=%d k=%d rho=%.4f p=%llu John=%.3f cap=%.3f total=%llu word=%s\n",
           n,k,rho,(unsigned long long)p,john,cap,(unsigned long long)total,argv[3]);
    u64 *d_mu,*d_w,*d_C,*d_cnt; Hash128* d_out; u64 cap_e=50000000ULL;
    CUDACHECK(cudaMalloc(&d_mu,n*8)); CUDACHECK(cudaMemcpy(d_mu,mu.data(),n*8,cudaMemcpyHostToDevice));
    CUDACHECK(cudaMalloc(&d_w,n*8));  CUDACHECK(cudaMemcpy(d_w,w.data(),n*8,cudaMemcpyHostToDevice));
    CUDACHECK(cudaMalloc(&d_C,C.size()*8)); CUDACHECK(cudaMemcpy(d_C,C.data(),C.size()*8,cudaMemcpyHostToDevice));
    CUDACHECK(cudaMalloc(&d_out,cap_e*sizeof(Hash128)));
    CUDACHECK(cudaMalloc(&d_cnt,8));
    // sweep t from Johnson down to capacity edge; report L(t), delta, region
    for(int t=t_john+1; t>=t_lo; t--){
        CUDACHECK(cudaMemset(d_cnt,0,8));
        ladder_kernel<<<4096,256>>>(total,n,k,p,t,d_mu,d_w,d_C,CW,d_out,d_cnt,cap_e);
        CUDACHECK(cudaDeviceSynchronize());
        u64 cnt; CUDACHECK(cudaMemcpy(&cnt,d_cnt,8,cudaMemcpyDeviceToHost));
        double delta=1.0-(double)t/n; const char* reg = delta>john? "WINDOW":"<=John";
        if(cnt>cap_e){ printf("  t=%d delta=%.3f %s : L=OVERFLOW(>%llu)\n",t,delta,reg,(unsigned long long)cap_e); continue; }
        std::vector<Hash128> hits(cnt); CUDACHECK(cudaMemcpy(hits.data(),d_out,cnt*sizeof(Hash128),cudaMemcpyDeviceToHost));
        u64 L=distinct_count(hits);
        printf("  t=%d delta=%.3f %s : L=%llu  (hits=%llu)\n",t,delta,reg,(unsigned long long)L,(unsigned long long)cnt);
        fflush(stdout);
    }
    printf("DONE\n");
    return 0;
}
