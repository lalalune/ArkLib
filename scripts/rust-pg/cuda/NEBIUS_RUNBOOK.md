# Nebius H200 runbook — explicit-RS list-size ladder (prize #444)

Goal: extend the **constant-list ladder** at fixed rate ρ by 1–2 octaves (n=64,128) to either
strengthen the floor evidence or **refute** it (a list jump). This is the decisive in-regime
measurement; it does **not** prove the n→2³⁰ asymptotic (that is the BGK wall).

## What we measure
`L(word, t)` = number of distinct degree-<k RS codewords over the dyadic subgroup μ_n ⊂ F_p*
(p ≈ n⁴, thin prize-regime prime) that agree with `word` on ≥ t of the n points, swept across the
list-decoding window t ∈ (ρn, √ρ·n]. Worst-case over structured candidate words (consecutive
lacunary x^a+x^{a-1} is the established empirical worst; antipodal x^{n/2}, odd words, mixed).

## Files (scp this whole `cuda/` dir to the instance)
- `ladder_core.h` — shared math core (validated against the Rust engine on M4: n=16,k=4 →
  antipodal L=2, consecutive L=21@t=5; the GPU runs this verbatim).
- `ladder.cu` — CUDA driver. Self-test mode cross-checks GPU vs CPU before any large run.
- `ladder_cpu.cpp` — CPU twin (same core), for n≤64 and validation.
- `run_sweep.sh` — saturates all 8 GPUs (one worker/GPU over a candidate word list).

## Setup
```bash
# on the 8×H200 instance (CUDA 12.x toolkit assumed; check: nvcc --version, nvidia-smi)
cd cuda
nvcc -O3 -arch=sm_90 -o ladder ladder.cu          # sm_90 = H100/H200
# MANDATORY first: GPU-vs-CPU self-test (must print MATCH, else stop — kernel bug)
./ladder 16 4 self        # expect: CPU L=.. GPU L=.. => MATCH
./ladder 32 8 self        # second self-test at larger k
```

## Runs (in priority order)
```bash
# ρ=1/8 ladder: n=16,32 already = 4 (M4). Add n=64 (CPU-cheap too) and n=128 (GPU-only).
./run_sweep.sh 64  8 8     # C(64,8)=4.4e9  — minutes on 8×H200
./run_sweep.sh 128 8 8     # C(128,8)=1.4e12 — ~1-3 h on 8×H200; THE new point

# ρ=1/16 ladder: n=32 (=7), n=64 (k=4, trivial). Add n=128 (k=8, GPU).
./run_sweep.sh 128 8 8     # (same binary; ρ=1/16 ⇔ k=8,n=128) -- note: k=8,n=128 IS ρ=1/16
# (for ρ=1/8 at n=128 use k=16: ./run_sweep.sh 128 16 8 — C(128,16)=1e19 INFEASIBLE, skip)

# ρ=1/4 ladder: n=16(=21@edge),32,64. n=64 needs k=16 => C(64,16)=4.9e14 GPU-borderline:
./run_sweep.sh 64 16 8     # ~hours; attempt only if time
```
Note on rates: ρ=k/n. ρ=1/8 ⇒ (n,k)∈{(16,2),(32,4),(64,8),(128,16)}. ρ=1/16 ⇒ {(32,2),(64,4),(128,8),(256,16)}.
The GPU sweet spot is **k=8** (n=128, ρ=1/16) and **k=8** (n=64, ρ=1/8) — both feasible.
k≥16 at n≥128 is out of reach (C(n,k)≥10¹⁹). p<2³¹ limit ⇒ n≤128 in this build (n=256 needs the
128-bit modmul path — flagged at runtime).

## Reading results
Each `results/<n>_<k>/<word>.txt` has lines `t=.. delta=.. WINDOW : L=..`. The run_sweep tail
prints **MAX L per t** across words. Track L at the deep window edge (t just above ρn) and at the
conjectured floor edge η≈c/log n (t ≈ ρn + n/log n). Compare across n at fixed ρ:
- **L poly in n at fixed η** (e.g. roughly constant or ~n^c) ⇒ floor supported.
- **L jumps / `L=OVERFLOW`** at n=64 or 128 ⇒ **floor refuted** (report immediately — major).

Honesty: buffer cap is 5×10⁷ hits; overflow is reported as `OVERFLOW`, never silently truncated.
```
