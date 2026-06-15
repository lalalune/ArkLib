# cuda-pg — GPU δ\* far-line incidence engine (#407)

A CUDA port of [`scripts/rust-pg`](../rust-pg) for computing the over-determined
far-line-incidence threshold `δ* = (n − s*)/n` of the smooth-domain Reed–Solomon
proximity gap at prize-scale primes. One CUDA thread per size-`s` subset of `μ_n`;
mirrors the Rust semantics exactly so results are bit-for-bit comparable.

## Why GPU

The computation is embarrassingly parallel over `(direction × subset)`, pure
fixed-modulus integer arithmetic (`p ≈ n⁴ < 2³²` for all `n ≤ 256`, so 32-bit
modmul suffices), with tiny per-thread state and a sparse distinct-count reduction.
Measured CPU baseline (`rust-pg`, 16-core): ~1.1×10⁷ subset-evals/sec → **n=32
takes hours–days**. A one-thread-per-subset GPU kernel does ~10⁹–10¹⁰ evals/sec →
**n=32 in seconds–minutes** (≈400–2000× on an RTX 5080 / H200; this kernel is
integer-compute-bound, so the 5080 is within ~2× of an H200 and is the right card
to develop and validate on). Brute force reaches ~n=40–44; beyond that needs a
closed form (the `C(n,s)` term grows super-exponentially).

## Build & run

```sh
make ARCH=sm_120      # RTX 5080 (Blackwell);  sm_90a = H200;  sm_100a = B200;  native = auto
./pg <n> <k> [cap]    # e.g. ./pg 32 8     (cap = max C(n,s) to enumerate, default 4e9)
```

## Validate against the Rust reference (do this first)

```sh
./validate.sh         # n = 8,12,16,20 — exact match on s*, δ*, per-s maxI
```

Ground-truth cross-checks (must reproduce exactly):
- n=16 k=4 → `s*=7, δ*=0.5625`, `s=6` row `maxI=89`.
- n=20 k=5 → `s*=9, δ*=0.5500`.
- **n=32 p-dependence target** (the subtle cross-witness-γ-collision case that the
  decoupling hypothesis was refuted on, #407): at `n=32`, direction `(17,2)`, the
  over-determined incidence is **897** at `p ∈ {32801, 32833, 65537}` but **705** at
  `p = 32993`, and saturates (`= p`) at `p = 257`. A correct kernel reproduces this
  p-dependence — it is the strongest correctness test (it exercises distinct-γ
  dedup across witnesses, not just per-witness checks). Run with the matching prime
  by adjusting `h_big_prime`, or add a `--prime` override to scan these.

## Notes / next optimizations

- `MAXN=48` compile cap on `n`; raise + recompile for larger `n` (watch register
  spilling of the `[MAXN]` scratch arrays — for production, size scratch to `s`).
- Barrett reduction with the fixed per-run prime (`bmu = ⌊2⁶⁴/p⌋`).
- Distinct-γ count via a per-direction open-addressing hash table (sized `≥ 4n²`,
  so it holds the exact count; `atomicCAS` insert). For pure `s*` search (not exact
  per-row `maxI`) you can early-exit a direction once the count exceeds `budget=n`.
- One kernel launch per direction (`O(n²)` per `s`); each launch is `C(n,s)` threads,
  so launch overhead is negligible. To squeeze more: batch directions on the grid
  `y`-axis and precompute `mua/mub` on-device.
- **Synergy with the math:** the decoupling/closed-form hypotheses are refuted
  (δ\* is p-dependent at n=32), so brute force is genuinely required — and this
  engine is the ground-truth oracle for validating any future closed form at
  n=32, 40.
