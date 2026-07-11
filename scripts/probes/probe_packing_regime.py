from math import comb, log2
# prize: n domain, k=rho*n, agreement a=(1-delta)*n, delta in window.
# my packing bound: #bad <= C(n,k+1)/C(a,k+1).
# prize budget: qeps = n.   supply budget K = 2^r * C(n/2, r) (r ~ band index).
# Question: is C(n,k+1)/C(a,k+1) <= n (prize) or only <= K (supply, exponential)?
print(f"{'rho':>5}{'n':>5}{'delta':>7}{'k':>5}{'a':>5}{'log2(packing)':>14}{'log2(n=qeps)':>13}{'log2(K_supply)':>15}{'regime':>10}")
for rho in [0.5, 0.25, 0.125]:
    for n in [64, 128, 256]:
        k = int(rho*n)
        # window: delta in (1-sqrt(rho), 1-rho).  pick interior point ~ midway, below 1-rho
        delta = 0.5*((1-rho**0.5) + (1-rho))   # midpoint of window-ish
        a = int(round((1-delta)*n))
        if a <= k+1: continue
        packing = comb(n,k+1)//max(comb(a,k+1),1)
        r = max(1, int(rho*n/2))  # band index proxy
        K = (2**r) * comb(n//2, min(r,n//2))
        lp = log2(packing) if packing>0 else 0
        regime = "PRIZE" if packing <= n else ("supply<K" if packing<=K else "above-K")
        print(f"{rho:>5}{n:>5}{delta:>7.3f}{k:>5}{a:>5}{lp:>14.1f}{log2(n):>13.1f}{log2(max(K,1)):>15.1f}{regime:>10}")
