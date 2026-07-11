from math import comb, log2

# The q-THRESHOLD analysis.
#
# TWO REGIMES (m=1, deep band a0=r+1, pin k_c=r-1, so a0-k_c=2):
#
# FAITHFUL regime: q^{m+1} = q^2 > C(n, a0).  Here #bad is the genuine ALGEBRAIC count:
#   the number of distinct subset-sum / two-symmetric-census values, which is q-INDEPENDENT
#   (a fixed integer determined by the char-0 census). O171 tri-prime invariance confirms this.
#
# SATURATED regime: small q, where DeepBandSaturationDischarge fires:
#   H1: 8*q^{m+1} <= C(n,k+m+1)   and   H2: 4*C(k+m+1,k+1)*C(n-(k+1),m)*q^{m+1} <= C(n,k+m+1)
#   Here pigeonhole forces #bad ~ value-space saturation => #bad can exceed K. eps_mca >= 1/8.
#
# The FAITHFUL threshold (where #bad stops growing, O171 dodge): q^2 > C(n,a0)  =>  q > sqrt(C(n,a0)).
# A4CensusValue's stronger rigidity threshold: p > 4^{2^{m-1}} = 4^{n/2} (for the a=4 exact value).

print("=== q-THRESHOLD: faithful threshold q* and production q (log2 scale) ===")
print(f"{'n':>4} {'r(deep)':>8} {'a0':>4} {'C(n,a0)':>14} {'sqrt-thresh q*':>14} {'log2 q*':>9} {'4^(n/2) thresh log2':>20}")
for (n, rdeep) in [(16,8),(32,16),(64,32),(128,64),(256,128),(1024,512)]:
    a0 = rdeep+1
    cna0 = comb(n, a0) if a0<=n else comb(n,n//2)
    # use the max over the deep window for a worst-case faithful threshold
    maxc = max(comb(n,a) for a in range(n//2-2, n//2+2) if 0<=a<=n)
    qstar = maxc**0.5
    l2 = log2(qstar) if qstar>0 else 0
    rig = (n/2)*2  # log2(4^(n/2)) = n
    print(f"{n:>4} {rdeep:>8} {a0:>4} {maxc:>14} {qstar:>14.3e} {l2:>9.1f} {rig:>20.0f}")

print()
print("Production q range (Ethereum prize): |F| up to 2^256, also BabyBear^2-class, Goldilocks 2^64, etc.")
print("Production rates 1/2,1/4,1/8,1/16 => k = rho*n; deep band r ~ n/2 independent of rate.")
print()
print("VERDICT logic:")
print(" - sqrt(C(n,n/2)) threshold: q* ~ 2^{n/2 - O(log n)}.  For n<=512, q*<2^256 => production q FAITHFUL.")
print(" - The STRONGER A4-style rigidity threshold 4^{n/2} = 2^n: production q=2^256 faithful only for n<=256.")
print(" - For n > 256 at q=2^256: NOT guaranteed faithful by the conservative 2^n rigidity bound;")
print("   the weaker sqrt(C(n,n/2)) ~ 2^{n/2} bound keeps faithful up to n~512.")
