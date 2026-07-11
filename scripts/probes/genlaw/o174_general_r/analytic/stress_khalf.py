import math
def K(n,r): return 2**r*math.comb(n//2,r)
# Candidate: #bad(r) <= K/2 = 2^{r-1} C(n/2, r).  Stress vs proven r=3 = n*C(n/4,2)+1 and central band.
print("r=3 proven vs K/2:")
for n in [16,32,64,128,256]:
    bad3=n*math.comb(n//4,2)+1
    kh=2**(3-1)*math.comb(n//2,3)
    print(f"  n={n}: #bad(r3)={bad3}  K/2={kh}  K/2 - #bad = {kh-bad3}  ok={bad3<=kh}")
print()
# Central band r=n/2 margin: K/2 vs measured (n=16: 104 vs 128). The central band is the tightest.
# We only have n=16 central measured (104). Check K/2 at central for growth:
print("central band r=n/2: K=2^{n/2}C(n/2,n/2)=2^{n/2}, K/2=2^{n/2-1}:")
for n in [16,32,64]:
    r=n//2
    print(f"  n={n} r={r}: K=2^{r}={K(n,r)} K/2={K(n,r)//2}")
# n=16 central #bad=104 <= K/2=128 (margin 1.23x). If the central #bad ~ binom(n,n/2+1)-ish slice grows
# FASTER than 2^{n/2-1}, K/2 would eventually FAIL. Need n=32 central (#bad for r=16, a=17) - infeasible
# to enumerate (C(32,17)=2.3e8) cheaply. So K/2 at central is UNVERIFIED beyond n=16. Flag it.
