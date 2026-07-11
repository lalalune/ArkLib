# Plan (a) — compute `w(64)`: the proxy-face tie-breaker

**Goal.** Produce the single decisive datum `w(64) ∈ {3 (additive → prize-HOLDS direction),
4 (multiplicative → prize-FAILS direction)}`, breaking the `n ≤ 32` object-ambiguity tie for the
over-determined far-line (proxy) face.

**Honest ceiling.** This decides the **proxy face** (`p ≈ n⁴`), not the real cryptographic-`p` BGK
wall. It is real progress on the open dichotomy, **not** a solution of the prize.

## Steps

1. **Use the right engine.** `rust-pg`/`cuda-pg` (indexed by agreement `s`, max over directions =
   exactly `D*_n(m)`). *Not* the deep-band `#bad` kernel `fast_bad_gen.c` — it computes the same
   primitive but a different cross-section, and conflating them is the `objdisent` object-confusion
   trap. Confirmed: `fast_bad_gen` puts `89` at a different coordinate than `D*_n(m)`.

2. **Calibration gate (mandatory).** `./mine` auto-calibrates on launch and must pass bit-exact:
   - `n=8 k=2  → s*=5, δ*=0.3750` (cascade `[9, 5]`, `w=0`)
   - `n=16 k=4 → s=6 maxI=89, s*=7, δ*=0.5625` (cascade `[89, 9]`, `w=1`)
   - `n=32 k=8 → [4096, 89, 89, 9], m*=5, w=2` (GPU; CPU times out ~77 min)
   - p-dependence oracle (cuda only): `n=32` dir `(17,2)` → incidence `897` at
     `p∈{32801,32833,65537}` but `705` at `p=32993`, saturates at `p=257`.

3. **Grind `n=64 k=16`.** GPU-only (`./mine 64` on a CUDA box, e.g. the `nebius-*.sh` 8×H200
   launcher in `../cuda-pg`). Read the worst-direction cascade; `w(64)` = run-length of `89`.

4. **Feasibility reality check FIRST.** README of `cuda-pg` says brute force tops out at `n ≈ 40–44`.
   `n=64` at the binding depth is **likely past the brute wall even on H200**. So:
   - try the full sweep `./mine 64`; if it can't finish, fall back to
   - the **known worst-dir family** only (`(40,16)` and a small neighborhood, plateau depths only)
     via `./mine --shard <i>/<N> 64` across the 8 GPUs;
   - if *that* is still infeasible, **report the brute-force wall honestly** — do not fake `w(64)`.

5. **Land honestly.** A `DISPROOF_LOG` entry + a `#444` comment with the proxy-face `w(64)` verdict,
   explicitly caveated as *not* the real wall. If a `×2` doubling shows up (`w(64)=4`), that is a
   real disproof signal for the proxy face — flag it loudly and cross-check at a second prime.

## Decision table

| outcome | reading |
|---------|---------|
| `w(64) = 3` | additive — consistent with `m*=O(log n)` — prize-HOLDS direction (proxy) |
| `w(64) = 4` | multiplicative — `m*` linear — prize-FAILS direction (proxy) |
| infeasible | report the brute-force wall; the question stays open at the proxy level too |

**Status:** blocked on GPU access for `n=64` (CPU validated through `n=16` here; `n=32` needs GPU).
