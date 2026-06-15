# CANDIDATE char-0 closed form: delta* = (1-rho) - log2(n)/n  (constant rate, #407, 2026-06-14)

Char-0 (q-free, p>>n^3) worst-case far-line incidence I_0(delta), crossing budget=n, at CONSTANT RATE
(method = the prime-size-independent (k+1)-subset solve; worst over far pencils a,b>=k != n/2):

| rho | n  | k | crossing w | w-k | log2(n) |
|-----|----|---|-----------|-----|---------|
| 1/8 | 16 | 2 | 6         | 4   | 4       |
| 1/8 | 32 | 4 | 9         | 5   | 5       |
| 1/4 | 16 | 4 | 7         | 3   | 4 (-1)  |

KEY: n*(cap - delta*) = w_delta* - k. For rho=1/8 this is EXACTLY log2(n) at BOTH n=16,32
=> candidate **delta* = (1-rho) - log2(n)/n** (a Theta(log n / n) gap below capacity).
rho=1/4 n=16 gives w-k=3 = log2(16)-1 (one band less; with one rho=1/4 point the rho-dependence
of the additive constant is unpinned).

SIGNIFICANCE / HONEST CAVEATS:
- This Theta(log n / n) gap is MUCH smaller (closer to capacity) than the standing conjecture
  delta* = 1 - rho - Theta(1/log n). At n=32: log2(n)/n = 0.156 vs 1/log2(n) = 0.20. They diverge.
  If the log(n)/n form holds asymptotically, the standing conjecture's window edge is wrong.
- ONLY 3 points, n in {16,32} (tiny); band granularity is coarse (delta* quantized to 1/n);
  the far-pencil set at small n may under-sample the true worst case. NOT confirmed.
- This is the CHAR-0 / budget=n value (= the q-free delta* IF the rigidity reduction holds, which
  the bad-prime bound + char-invariance probes support at prize scale).
- Needs n=64+ at constant rate to confirm/refute (feasible via the (k+1)-subset solve at rho=1/16).
Probe: scripts/probes/probe_char0_deltastar_pin_constrate.py.
