// CUDA over-determined far-line incidence engine for #407 (GPU port of scripts/rust-pg).
//
// Computes delta* = (n - s*)/n where s* = min s with
//   max over far dirs (a,b), k<=b<s, k<=a<n, a!=b, of incidence(a,b;s) <= budget = n.
// incidence(a,b;s) = # distinct gamma in F_p s.t. x^a + gamma x^b agrees with a
//   deg<k poly on >= s points of mu_n.  Exact, via the divided-difference / over-
//   determined witness condition.  One CUDA thread per size-s subset of mu_n.
//
// Mirrors scripts/rust-pg/src/main.rs semantics EXACTLY (same mu, invd, divided
// differences, heavy/saturation rule = u64::MAX -> 0 in the max, distinct-gamma
// count) so results are bit-for-bit comparable.  Validate with ./validate.sh.
//
// Arithmetic: p = big_prime(n) ~ n^4 < 2^32 for all n <= 256, so operands are 32-bit
// and products fit in 64 bits.  Reduction is Barrett with the fixed prime
// (bmu = floor(2^64 / p)).
//
// Build:  nvcc -O3 -arch=native -o pg pg.cu      (RTX 5080: -arch=sm_120 ; H200: -arch=sm_90a)
// Run:    ./pg <n> <k> [cap]
//
// Copyright (c) 2026 ArkLib Contributors. Apache-2.0.

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cmath>
#include <vector>
#include <cuda_runtime.h>

#define MAXN 48                 // compile-time cap on n (subset/value scratch size)
#define SENTINEL 0xFFFFFFFFu    // never a valid gamma (gamma <= p-1 <= 2^32-2)

#define CUDA_OK(call) do { cudaError_t e_ = (call); if (e_ != cudaSuccess) { \
  fprintf(stderr, "CUDA error %s at %s:%d\n", cudaGetErrorString(e_), __FILE__, __LINE__); \
  exit(1); } } while (0)

// ---------------------------------------------------------------------------
// Host modular helpers (setup: mu, invd, per-direction mua/mub) — mirror Rust.
// ---------------------------------------------------------------------------
static inline uint32_t h_mulmod(uint32_t a, uint32_t b, uint32_t p) { return (uint32_t)(((uint64_t)a*b)%p); }
static inline uint32_t h_submod(uint32_t a, uint32_t b, uint32_t p) { return a>=b ? a-b : p-b+a; }
static uint32_t h_powmod(uint32_t b, uint64_t e, uint32_t p) {
  uint32_t r = 1; b %= p;
  while (e) { if (e & 1) r = h_mulmod(r, b, p); b = h_mulmod(b, b, p); e >>= 1; } return r;
}
static uint32_t h_invmod(uint32_t a, uint32_t p) { return h_powmod(a, p - 2, p); }
static bool h_is_prime(uint64_t x) {
  if (x < 2) return false;
  for (uint64_t q : {2ull,3ull,5ull,7ull,11ull,13ull,17ull,19ull,23ull,29ull,31ull,37ull})
    if (x % q == 0) return x == q;
  uint64_t d = x - 1; int s = 0; while ((d & 1) == 0) { d >>= 1; s++; }
  for (uint64_t a : {2ull,3ull,5ull,7ull,11ull,13ull,17ull,19ull,23ull,29ull,31ull,37ull}) {
    __uint128_t y = 1, base = a % x, e = d;
    while (e) { if (e & 1) y = (y*base)%x; base = (base*base)%x; e >>= 1; }
    if (y == 1 || y == x - 1) continue;
    bool ok = false;
    for (int i = 0; i < s - 1; i++) { y = (y*y)%x; if (y == x - 1) { ok = true; break; } }
    if (!ok) return false;
  }
  return true;
}
static std::vector<uint64_t> h_factor(uint64_t x) {
  std::vector<uint64_t> f; for (uint64_t d = 2; d*d <= x; d++)
    if (x % d == 0) { f.push_back(d); while (x % d == 0) x /= d; }
  if (x > 1) f.push_back(x); return f;
}
static uint32_t h_proot(uint32_t p) {
  auto fs = h_factor(p - 1);
  for (uint32_t g = 2; g < p; g++) {
    bool ok = true; for (uint64_t q : fs) if (h_powmod(g, (p-1)/q, p) == 1) { ok = false; break; }
    if (ok) return g;
  } return 0;
}
static uint32_t h_big_prime(uint64_t n) {           // smallest p>=n^4, p%n==1, prime (mirrors Rust)
  uint64_t p = n*n*n*n; for (;;) { if (p % n == 1 && h_is_prime(p)) return (uint32_t)p; p++; }
}
static uint64_t h_nck(uint64_t n, uint64_t k) {
  if (k > n) return 0; k = k < n - k ? k : n - k;
  __uint128_t r = 1; for (uint64_t i = 0; i < k; i++) r = r*(n-i)/(i+1); return (uint64_t)r;
}
static uint32_t npow2(uint32_t x) { uint32_t r = 1; while (r < x) r <<= 1; return r; }

// ---------------------------------------------------------------------------
// Device: Barrett 32-bit modular arithmetic (fixed prime p, bmu = floor(2^64/p)).
// ---------------------------------------------------------------------------
__device__ __forceinline__ uint32_t d_mulmod(uint32_t a, uint32_t b, uint32_t p, uint64_t bmu) {
  uint64_t x = (uint64_t)a * b;            // < p^2 < 2^64
  uint64_t q = __umul64hi(x, bmu);         // ~ floor(x/p), undershoots by <= ~2
  uint32_t r = (uint32_t)(x - q * (uint64_t)p);
  if (r >= p) r -= p; if (r >= p) r -= p; if (r >= p) r -= p;   // <= ~2 corrections + safety
  return r;
}
__device__ __forceinline__ uint32_t d_addmod(uint32_t a, uint32_t b, uint32_t p) {
  uint32_t s = a + b; return s >= p ? s - p : s;
}
__device__ __forceinline__ uint32_t d_submod(uint32_t a, uint32_t b, uint32_t p) {
  return a >= b ? a - b : p - b + a;
}
__device__ uint32_t d_powmod(uint32_t b, uint32_t e, uint32_t p, uint64_t bmu) {
  uint32_t r = 1; while (e) { if (e & 1) r = d_mulmod(r, b, p, bmu); b = d_mulmod(b, b, p, bmu); e >>= 1; }
  return r;
}
__device__ __forceinline__ uint32_t d_invmod(uint32_t a, uint32_t p, uint64_t bmu) {
  return d_powmod(a, p - 2, p, bmu);
}

// combinatorial number system unrank (mirrors Rust `unrank`): r-th s-combination of
// [0,n) in lexicographic order -> comb[0..s) ascending.  nckt[a*(MAXN+1)+b] = C(a,b).
__device__ void d_unrank(uint64_t r, int n, int s, int* comb, const uint64_t* nckt) {
  int x = 0, remaining = s, idx = 0;
  while (remaining > 0) {
    for (;;) {
      uint64_t c = nckt[(uint64_t)(n - 1 - x) * (MAXN + 1) + (remaining - 1)];
      if (r < c) { comb[idx++] = x; x++; remaining--; break; } else { r -= c; x++; }
    }
  }
}
// order-k divided difference of vals[0..k] on node-indices idx[0..k] (mirrors ddk_idx).
__device__ uint32_t d_ddk(const uint32_t* vals, const int* idx, int k, uint32_t p,
                          uint64_t bmu, const uint32_t* invd, int n) {
  uint32_t vs[MAXN];
  for (int t = 0; t <= k; t++) vs[t] = vals[t];
  for (int j = 1; j <= k; j++)
    for (int i = k; i >= j; i--) {
      uint32_t inv = invd[(uint64_t)idx[i] * n + idx[i - j]];
      vs[i] = d_mulmod(d_submod(vs[i], vs[i - 1], p), inv, p, bmu);
    }
  return vs[k];
}
// does vals (node-indices idx, length s) lie on a deg<k poly? (mirrors in_rs_idx)
__device__ bool d_in_rs(const uint32_t* vals, const int* idx, int k, uint32_t p,
                        uint64_t bmu, const uint32_t* invd, int n, int s) {
  if (s <= k) return true;
  for (int st = 0; st < s - k; st++)
    if (d_ddk(vals + st, idx + st, k, p, bmu, invd, n) != 0) return false;
  return true;
}
// open-addressing insert of a distinct gamma; exact count (table sized >= 4*n*n so it
// never fills) — matches Rust `local.insert(gm); local.len()`.
__device__ __forceinline__ void d_hash_insert(uint32_t g, uint32_t* htab, uint32_t hmask, uint32_t* dcount) {
  uint32_t slot = (g * 2654435761u) & hmask;
  for (uint32_t probe = 0; probe <= hmask; probe++) {
    uint32_t cur = atomicCAS(&htab[slot], SENTINEL, g);
    if (cur == SENTINEL) { atomicAdd(dcount, 1u); return; }   // newly distinct
    if (cur == g) return;                                     // already counted
    slot = (slot + 1) & hmask;
  }
}

// Kernel: one thread per size-s subset of mu_n, fixed direction (a,b).
__global__ void incidence_kernel(
    uint64_t total, int n, int k, int s, uint32_t p, uint64_t bmu,
    const uint32_t* __restrict__ mua, const uint32_t* __restrict__ mub,
    const uint32_t* __restrict__ invd, const uint64_t* __restrict__ nckt,
    uint32_t* htab, uint32_t hmask, uint32_t* dcount, int* heavy) {
  uint64_t stride = (uint64_t)gridDim.x * blockDim.x;
  for (uint64_t r = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x; r < total; r += stride) {
    if (*heavy) return;                              // a heavy witness already saturated this direction
    int comb[MAXN];
    d_unrank(r, n, s, comb, nckt);
    uint32_t u0[MAXN], u1[MAXN];
    for (int j = 0; j < s; j++) { u0[j] = mua[comb[j]]; u1[j] = mub[comb[j]]; }

    if (d_in_rs(u1, comb, k, p, bmu, invd, n, s)) {
      if (d_in_rs(u0, comb, k, p, bmu, invd, n, s)) { atomicExch(heavy, 1); return; }  // saturated
    } else {
      uint32_t a0 = d_ddk(u0, comb, k, p, bmu, invd, n);
      uint32_t a1 = d_ddk(u1, comb, k, p, bmu, invd, n);
      if (a1 != 0) {
        uint32_t gm = d_mulmod(d_submod(0, a0, p), d_invmod(a1, p, bmu), p, bmu);
        uint32_t full[MAXN];
        for (int i = 0; i < s; i++) full[i] = d_addmod(u0[i], d_mulmod(gm, u1[i], p, bmu), p);
        if (d_in_rs(full, comb, k, p, bmu, invd, n, s)) d_hash_insert(gm, htab, hmask, dcount);
      }
    }
  }
}

int main(int argc, char** argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s <n> <k> [cap]\n", argv[0]); return 1; }
  int n = atoi(argv[1]), k = atoi(argv[2]);
  uint64_t cap = (argc > 3) ? strtoull(argv[3], nullptr, 10) : 4000000000ull;
  if (n > MAXN) { fprintf(stderr, "n=%d exceeds MAXN=%d (raise MAXN, recompile)\n", n, MAXN); return 1; }

  uint32_t p = h_big_prime((uint64_t)n);
  uint32_t g = h_proot(p);
  uint32_t h = h_powmod(g, (p - 1) / (uint32_t)n, p);
  std::vector<uint32_t> mu(n);
  for (int i = 0; i < n; i++) mu[i] = h_powmod(h, (uint32_t)i, p);
  std::vector<uint32_t> invd((size_t)n * n, 0);
  for (int a = 0; a < n; a++) for (int b = 0; b < n; b++)
    if (a != b) invd[(size_t)a * n + b] = h_invmod(h_submod(mu[a], mu[b], p), p);
  uint64_t bmu = (uint64_t)(((__uint128_t)1 << 64) / p);   // floor(2^64 / p)

  uint32_t budget = (uint32_t)n;
  double rho = (double)k / n, john = 1.0 - sqrt(rho), capd = 1.0 - rho;
  printf("n=%d k=%d rho=%.4f p=%u(~n^4) Johnson=%.4f cap=%.4f budget=%u\n",
         n, k, rho, p, john, capd, budget);

  std::vector<uint64_t> nckt((size_t)(MAXN + 1) * (MAXN + 1), 0);
  for (int a = 0; a <= MAXN; a++) for (int b = 0; b <= MAXN; b++)
    nckt[(size_t)a * (MAXN + 1) + b] = h_nck(a, b);

  uint32_t *d_invd, *d_mua, *d_mub, *d_htab, *d_dcount; uint64_t *d_nckt; int *d_heavy;
  CUDA_OK(cudaMalloc(&d_invd, invd.size() * 4));
  CUDA_OK(cudaMemcpy(d_invd, invd.data(), invd.size() * 4, cudaMemcpyHostToDevice));
  CUDA_OK(cudaMalloc(&d_nckt, nckt.size() * 8));
  CUDA_OK(cudaMemcpy(d_nckt, nckt.data(), nckt.size() * 8, cudaMemcpyHostToDevice));
  CUDA_OK(cudaMalloc(&d_mua, n * 4)); CUDA_OK(cudaMalloc(&d_mub, n * 4));
  CUDA_OK(cudaMalloc(&d_dcount, 4)); CUDA_OK(cudaMalloc(&d_heavy, 4));
  uint32_t H = npow2(64u > 4u*(uint32_t)n*(uint32_t)n ? 64u : 4u*(uint32_t)n*(uint32_t)n);
  uint32_t hmask = H - 1;
  CUDA_OK(cudaMalloc(&d_htab, (size_t)H * 4));

  int sstar = 0;
  for (int s = k + 2; s < n; s++) {
    uint64_t total = h_nck(n, s);
    if (total > cap) { printf("  s=%d C=%llu > cap %llu, stop\n", s,
                              (unsigned long long)total, (unsigned long long)cap); break; }
    uint64_t maxI = 0; int arga = 0, argb = 0;
    for (int b = k; b < s; b++) {
      std::vector<uint32_t> mub(n);
      for (int i = 0; i < n; i++) mub[i] = h_powmod(mu[i], (uint32_t)b, p);
      CUDA_OK(cudaMemcpy(d_mub, mub.data(), n * 4, cudaMemcpyHostToDevice));
      for (int a = k; a < n; a++) {
        if (a == b) continue;
        std::vector<uint32_t> mua(n);
        for (int i = 0; i < n; i++) mua[i] = h_powmod(mu[i], (uint32_t)a, p);
        CUDA_OK(cudaMemcpy(d_mua, mua.data(), n * 4, cudaMemcpyHostToDevice));

        CUDA_OK(cudaMemset(d_htab, 0xFF, (size_t)H * 4));   // SENTINEL fill
        CUDA_OK(cudaMemset(d_dcount, 0, 4));
        CUDA_OK(cudaMemset(d_heavy, 0, 4));

        int threads = 256;
        uint64_t blocks64 = (total + threads - 1) / threads;
        int blocks = (int)(blocks64 > 65535 ? 65535 : blocks64);   // grid-stride covers the rest
        incidence_kernel<<<blocks, threads>>>(total, n, k, s, p, bmu,
            d_mua, d_mub, d_invd, d_nckt, d_htab, hmask, d_dcount, d_heavy);
        CUDA_OK(cudaGetLastError());
        CUDA_OK(cudaDeviceSynchronize());

        int heavy; uint32_t dcount;
        CUDA_OK(cudaMemcpy(&heavy, d_heavy, 4, cudaMemcpyDeviceToHost));
        CUDA_OK(cudaMemcpy(&dcount, d_dcount, 4, cudaMemcpyDeviceToHost));
        uint64_t inc = heavy ? 0 : dcount;            // Rust maps saturated (u64::MAX) -> 0 in the max
        if (inc > maxI) { maxI = inc; arga = a; argb = b; }
      }
    }
    bool good = maxI <= budget;
    printf("  s=%d (s-k=%d): maxI=%llu at (%d, %d)  %s\n",
           s, s - k, (unsigned long long)maxI, arga, argb, good ? "GOOD" : "bad");
    if (good) { sstar = s; break; }
  }
  if (sstar > 0) {
    double ds = (double)(n - sstar) / n;
    printf("  => s*=%d, s*-k=%d, delta*=%.4f, defect(s*-k)/n=%.4f  [Johnson %.4f, cap %.4f]\n",
           sstar, sstar - k, ds, (double)(sstar - k) / n, john, capd);
  }
  return 0;
}
