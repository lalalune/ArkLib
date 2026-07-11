// ladder_cpu.cpp — CPU twin of ladder.cu. Same shared core (ladder_core.h); OpenMP-parallel over
// subsets. Compilable on any host (clang++/g++) for validation + for n<=64 production runs.
// Build:  clang++ -O3 -fopenmp -o ladder_cpu ladder_cpu.cpp   (or g++)
//         (macOS: clang++ -O3 -Xpreprocessor -fopenmp -lomp ... ; or drop -fopenmp for serial)
// Run:    ./ladder_cpu <n> <k> <word>   word = mA | A,B | self
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <vector>
#include <string>
#include <algorithm>
#include "ladder_core.h"
#ifdef _OPENMP
#include <omp.h>
#endif

static bool isprime(u64 x){ if(x<2)return false; for(u64 d=2;d*d<=x;d++) if(x%d==0)return false; return true; }
static u64 big_prime(u64 n){ u64 p=n*n*n*n; while(!(p%n==1&&isprime(p)))p++; return p; }
static u64 hpow(u64 b,u64 e,u64 p){ u64 r=1;b%=p; while(e){ if(e&1)r=(__uint128_t)r*b%p; b=(__uint128_t)b*b%p; e>>=1;} return r; }
static std::vector<u64> factor(u64 x){ std::vector<u64> f; for(u64 d=2;d*d<=x;d++) if(x%d==0){ f.push_back(d); while(x%d==0)x/=d; } if(x>1)f.push_back(x); return f; }
static u64 proot(u64 p){ auto fs=factor(p-1); for(u64 g=2;g<p;g++){ bool ok=true; for(u64 q:fs) if(hpow(g,(p-1)/q,p)==1){ok=false;break;} if(ok)return g; } return 0; }
static u64 distinct(std::vector<Hash128>& v){
    std::sort(v.begin(),v.end(),[](const Hash128&a,const Hash128&b){ return a.hi!=b.hi?a.hi<b.hi:a.lo<b.lo; });
    u64 c=0; for(size_t i=0;i<v.size();i++) if(i==0||v[i].hi!=v[i-1].hi||v[i].lo!=v[i-1].lo) c++; return c;
}

static u64 list_size(int n,int k,u64 p,int t,const std::vector<u64>&mu,const std::vector<u64>&w,
                     const std::vector<u64>&C,int CW){
    u64 total=C[n*CW+k];
    std::vector<Hash128> hits;
    #ifdef _OPENMP
    int T=omp_get_max_threads(); std::vector<std::vector<Hash128>> loc(T);
    #pragma omp parallel
    { int tid=omp_get_thread_num(); auto& h=loc[tid];
      #pragma omp for schedule(dynamic,4096)
      for(long long r=0;r<(long long)total;r++){ u64 idx[KMAX]; unrank((u64)r,n,k,C.data(),CW,idx);
          Hash128 z=subset_member_hash(idx,k,mu.data(),w.data(),n,p,t); if(z.lo|z.hi) h.push_back(z); } }
    for(auto& h:loc) hits.insert(hits.end(),h.begin(),h.end());
    #else
    for(u64 r=0;r<total;r++){ u64 idx[KMAX]; unrank(r,n,k,C.data(),CW,idx);
        Hash128 z=subset_member_hash(idx,k,mu.data(),w.data(),n,p,t); if(z.lo|z.hi) hits.push_back(z); }
    #endif
    return distinct(hits);
}

int main(int argc,char**argv){
    if(argc<4){ fprintf(stderr,"usage: %s <n> <k> <word: mA|A,B|self>\n",argv[0]); return 1; }
    int n=atoi(argv[1]), k=atoi(argv[2]);
    u64 p=big_prime(n);
    u64 g=proot(p), h=hpow(g,(p-1)/n,p);
    std::vector<u64> mu(n); for(int i=0;i<n;i++) mu[i]=hpow(h,i,p);
    int CW=KMAX+1; std::vector<u64> C((n+1)*CW,0);
    for(int a=0;a<=n;a++){ C[a*CW+0]=1; for(int b=1;b<=k&&b<=a&&b<CW;b++) C[a*CW+b]=C[(a-1)*CW+b-1]+C[(a-1)*CW+b]; }
    double rho=(double)k/n, john=1.0-sqrt(rho), cap=1.0-rho;
    int t_cap=(int)ceil(rho*n), t_john=(int)floor(sqrt(rho)*n), t_lo=(t_cap>k+1?t_cap:k+1);
    auto build=[&](const std::string&s){ std::vector<u64> w(n);
        if(s[0]=='m'){ int A=atoi(s.c_str()+1); for(int i=0;i<n;i++) w[i]=hpow(mu[i],A,p); }
        else { int A,B; sscanf(s.c_str(),"%d,%d",&A,&B); for(int i=0;i<n;i++) w[i]=addmod(hpow(mu[i],A,p),hpow(mu[i],B,p),p);} return w; };
    if(std::string(argv[3])=="self"){
        // sweep a few fixed words at all window t and print — to diff against the Rust engine.
        const char* specs[]={ "m4", (std::string(std::to_string(n-1)).c_str()) }; (void)specs;
        std::vector<std::string> S={ std::to_string(n-1)+","+std::to_string(n-2), "m"+std::to_string(n/2), std::to_string(n-1)+","+std::to_string(n-3) };
        printf("SELF n=%d k=%d p=%llu rho=%.3f John=%.3f window t=[%d..%d]\n",n,k,(unsigned long long)p,rho,john,t_lo,t_john);
        for(auto&s:S){ auto w=build(s); printf("  word=%s:",s.c_str());
            for(int t=t_john+1;t>=t_lo;t--){ u64 L=list_size(n,k,p,t,mu,w,C,CW); printf(" t=%d:L=%llu",t,(unsigned long long)L);} printf("\n"); }
        return 0;
    }
    auto w=build(argv[3]);
    printf("n=%d k=%d rho=%.4f p=%llu John=%.3f cap=%.3f total=%llu word=%s\n",n,k,rho,(unsigned long long)p,john,cap,(unsigned long long)C[n*CW+k],argv[3]);
    // optional 4th arg = single t to evaluate (avoids the full window sweep for heavy n);
    // optional 5th arg present => only print that one t.
    if(argc>=5){ int t=atoi(argv[4]); u64 L=list_size(n,k,p,t,mu,w,C,CW);
        double delta=1.0-(double)t/n; printf("  t=%d delta=%.3f %s : L=%llu\n",t,delta,delta>john?"WINDOW":"<=John",(unsigned long long)L); fflush(stdout);
        printf("DONE\n"); return 0; }
    for(int t=t_john+1;t>=t_lo;t--){ u64 L=list_size(n,k,p,t,mu,w,C,CW);
        double delta=1.0-(double)t/n; printf("  t=%d delta=%.3f %s : L=%llu\n",t,delta,1.0-(double)t/n>john?"WINDOW":"<=John",(unsigned long long)L); fflush(stdout); }
    printf("DONE\n"); return 0;
}
