// ladder_core.h — modular arithmetic + per-subset interpolation core, SHARED verbatim by the
// CUDA build (ladder.cu) and the CPU twin (ladder_cpu.cpp). The CPU twin is compilable on any
// host and cross-checked against the Rust engine, so this exact code is validated before the GPU
// (whose only extra surface is memcpy/kernel-launch boilerplate) is trusted at large n.
#pragma once
#include <cstdint>
typedef unsigned long long u64;

#ifndef __CUDACC__
  #define __host__
  #define __device__
#endif

#define KMAX 24

// modular arithmetic, valid for p < 2^31 (products a*b < 2^62 fit u64). n<=128 => p~n^4 < 2.7e8.
__host__ __device__ inline u64 mulmod(u64 a,u64 b,u64 p){ return (a*b)%p; }
__host__ __device__ inline u64 addmod(u64 a,u64 b,u64 p){ u64 s=a+b; return s>=p?s-p:s; }
__host__ __device__ inline u64 submod(u64 a,u64 b,u64 p){ return a>=b?a-b:p-b+a; }
__host__ __device__ inline u64 powmod(u64 b,u64 e,u64 p){ u64 r=1;b%=p; while(e){ if(e&1)r=mulmod(r,b,p); b=mulmod(b,b,p); e>>=1;} return r; }
__host__ __device__ inline u64 invmod(u64 a,u64 p){ return powmod(a,p-2,p); }

struct Hash128 { u64 lo, hi; };

// Interpolate deg<k codeword through (mu[idx], w[idx]); count agreement with w over all n points
// (early-exit at t_min); if agreement >= t_min return a 128-bit hash of the coefficient vector,
// else {0,0}. Identical on CPU and GPU.
__host__ __device__ inline Hash128 subset_member_hash(
    const u64* idx,int k,const u64* mu,const u64* w,int n,u64 p,int t_min)
{
    Hash128 zero{0,0};
    u64 xs[KMAX], ys[KMAX], coef[KMAX];
    for(int i=0;i<k;i++){ xs[i]=mu[idx[i]]; ys[i]=w[idx[i]]; coef[i]=0; }
    for(int i=0;i<k;i++){
        u64 denom=1;
        for(int j=0;j<k;j++) if(j!=i) denom=mulmod(denom, submod(xs[i],xs[j],p), p);
        u64 scale=mulmod(ys[i], invmod(denom,p), p);
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
    int ag=0;
    for(int i=0;i<n;i++){
        u64 x=mu[i], r=0;
        for(int t=k-1;t>=0;t--) r=addmod(mulmod(r,x,p), coef[t], p);
        if(r==w[i]) ag++;
        if(ag + (n-i-1) < t_min) return zero;
    }
    if(ag < t_min) return zero;
    u64 h1=1469598103934665603ULL, h2=1125899906842597ULL;
    for(int t=0;t<k;t++){ h1=(h1 ^ coef[t]) * 1099511628211ULL; h2=h2*1000000007ULL + coef[t] + 0x9e3779b97f4a7c15ULL; }
    if(h1==0&&h2==0) h1=1;
    return Hash128{h1,h2};
}

// combinatorial number system: unrank r in [0,C(n,k)) -> lexicographic k-subset (increasing).
__host__ __device__ inline void unrank(u64 r,int n,int k,const u64* C,int CW,u64* idx){
    int a=n;
    for(int i=0;i<k;i++){
        int kk=k-i, c=kk-1;
        while(c+1<a && C[(c+1)*CW + kk] <= r) c++;
        idx[i]=(u64)c; r -= C[c*CW + kk]; a=c;
    }
    for(int i=0;i<k/2;i++){ u64 t=idx[i]; idx[i]=idx[k-1-i]; idx[k-1-i]=t; }
}
