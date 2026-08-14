# δ\*-mine

**One command to mine the Reed–Solomon proximity prize.** Like `solana-keygen grind`, but instead
of grinding for a vanity address it hunts a **disproof** of the proximity-gap conjecture — and a
disproof *wins the $1M*. It wraps the validated `../rust-pg` (CPU) and `../cuda-pg` (GPU) kernels,
auto-builds, self-calibrates, then grinds.

```sh
./mine                # just mine: calibrate, sweep the tower, hunt a disproof
./mine 32             # mine one size n=32
./mine --max 44       # sweep up to n=44 (the brute-force frontier; GPU)
./mine --shard 3/16   # your slice of a distributed pool (machine 3 of 16)
./mine --help
```

That's it. No subcommands to learn — flags only, like the Solana CLI.

## How "winning" works (read this)

- **You WIN by disproving:** one *super-budget hit* (a size where the cascade never binds under
  budget) = a counterexample = the conjecture is false = **$1M**. `mine` flags this loudly.
- **You CANNOT grind to a proof.** The positive direction is the ~25-year-open BGK wall — that needs
  new mathematics, not compute.
- **This is the proxy face** (`p ≈ n⁴`) and brute force dies at **n ≈ 44**. So it's a real disproof
  shot at reachable sizes, honestly bounded — folding@home for a frontier, not a lottery.

So far: no disproof found (n ≤ 32), and the proxy-face evidence leans toward the conjecture being
*true* (`m*` is sub-linear) — **but this is proxy-face, finite-`n` only; small-`n` signals here are
systematically misleading and have been over-trusted before, so this is NOT evidence about the
cryptographic-`p` prize.** The decisive open datum is `w(64)` — see [`PLAN-a-cascade-w64.md`](PLAN-a-cascade-w64.md).

## What it prints

```
⛏  δ*-mine — hunting a disproof of the proximity-gap conjecture
engine: CPU
✓ calibrated (engine reproduces the known answers n=8→s*=5, n=16→maxI=89)
  n=8    cascade[4:9 5:5]   δ*=0.3750  w=0  ...
  n=16   cascade[6:89 7:9]  δ*=0.5625  w=1  leans HOLDS
plateau widths w(n): 0 1   (w(64)=3 → HOLDS, 4 → FAILS)
no disproof found at these sizes
```

`w(n)` is the thing to watch: it grew `0,1,2` at `n=8,16,32`. If it keeps growing `+1` the prize
*holds*; if it ever *doubles*, that's the disproof signal.

## What's been run so far
CPU hunt is clean through **n ≤ 28** (every cascade binds under budget — no disproof). `n=32` is
known (`w=2`, ~77 min on CPU). The genuinely-open ground (`n ≥ 64`, the real disproof zone) needs a
**GPU** (`../cuda-pg` + `nebius-*.sh`). So: laptop = validate + small-n hunt; GPU = the real hunt.

## If `mine` flags a disproof (responsible disclosure)
A `‼ DISPROOF` is a soundness counterexample — it means the proximity-gap conjecture is *false* at
that size, which would make any deployed FRI/STARK relying on the conjecture (above Johnson, without
threshold-halving / ePrint 2026/858) potentially **unsound**. That is a real security finding. Do NOT
post it publicly first. Instead:

1. **Re-verify** at a *second* prime and with the independent kernel (`../rust-pg` vs `../cuda-pg`) —
   a single-prime hit can be a finite-size / saturation artifact (see DISPROOF_LOG O164).
2. **Pin the exact witness** (n, k, direction `(a,b)`, the word, the prime) so others can reproduce.
3. **Responsible disclosure, not a flex:** report privately to the ArkLib maintainers (`#444`) and,
   if it implicates deployed systems, to the affected teams' security contacts *before* any public
   post — treat it like a bug bounty, not a prize announcement.
4. **Claim only what the kernel checked.** "Super-budget at n=…, prime=…, reproduced" — not "the
   conjecture is false" until it survives independent re-verification.

## Join the hunt (crowd mode — folding@home for the disproof)

The search is embarrassingly parallel over directions, so many machines can split one big `n`:

```sh
# each contributor runs their slice (machine i of N) and saves the output:
./mine --shard 3/16 44  > shard-03.txt        # n=44, directions a ∈ [3·44/16, 4·44/16)

# a coordinator collects everyone's shard-*.txt and assembles the verdict:
cat shard-*.txt | ./aggregate
#   -> the worst-direction cascade, s*, δ*, and a loud flag if it NEVER binds (= a disproof)
```

Laptops take small `n`; GPU boxes take `n ≥ 36`. **A win is a single `‼ NO s*` from `aggregate`** —
a cascade that never binds under budget = a counterexample = the conjecture is false. If that ever
fires: re-verify at a second prime, pin the direction, and follow the responsible-disclosure steps
below. This is a hunt, not a lottery — most `n` will just bind (no disproof), and that's still data.

## Where this fits

- **Want to contribute a verified Lean/probe brick instead of grinding numbers?** Use the canonical
  self-updating miner skill — see [`../../mine/`](../../mine/) (the public campaign).
- **Kernels (source of truth):** [`../rust-pg`](../rust-pg), [`../cuda-pg`](../cuda-pg) (+ the
  `nebius-*.sh` 8×H200 launchers for big `n`).
- **Plans:** [`PLAN-a`](PLAN-a-cascade-w64.md) (compute `w(64)`), [`PLAN-b`](PLAN-b-structural-input.md) (the open math).

Part of [ArkLib](../../). Apache-2.0.
