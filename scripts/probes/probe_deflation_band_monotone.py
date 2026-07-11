# PROBE: the packing-floor deflation D(a) = C(n,k+1) / C(a,k+1) (Nat floor div)
# Claims to test (the ASSERTED-but-unproven EpsMCAPackingFloor scope note + ASYMPTOTIC GUARD):
#  (A) D(a) is ANTITONE in a on [k+1, n]  (bigger band a => smaller distinct-gamma floor)
#  (B) the REAL-valued ratio R(a) = C(n,k+1)/C(a,k+1) at a = n/2 is ~ 2^(k+1) (the cliff),
#      i.e. it does NOT scale like a sub-Johnson count; for fixed small k it is O(1) in n => the
#      distinct-gamma floor from packing at the deep band is a CONSTANT-factor deflation, NOT
#      a sqrt(n)-type CORE bound. Confirms the packing face collapses (does NOT open a gap).
#  (C) the UNDERLYING real ratio R(a) is itself antitone (the Nat-floor antitony should follow).
from math import comb


def D(n, k, a):  # Nat floor division
    ca = comb(a, k + 1)
    if ca == 0:
        return None
    return comb(n, k + 1) // ca


def R(n, k, a):
    ca = comb(a, k + 1)
    if ca == 0:
        return None
    return comb(n, k + 1) / ca


print("=== (A) Nat-floor antitony of D(a) over a in [k+1, n] ===")
allA = True
for n in [16, 32, 64, 128, 256]:
    for k in [1, 2, 3]:
        prev = None
        ok = True
        for a in range(k + 1, n + 1):
            d = D(n, k, a)
            if prev is not None and d > prev:
                ok = False
            prev = d
        print(f" n={n:4d} k={k}: antitone={ok}")
        allA = allA and ok
print(" (A) ALL antitone:", allA)

print("\n=== (B) cliff at a=n/2: real ratio R(n/2) vs 2^(k+1) ===")
for n in [16, 32, 64, 128, 256, 1024]:
    for k in [1, 2, 3]:
        a = n // 2
        r = R(n, k, a)
        print(f" n={n:5d} k={k} a=n/2={a:4d}: R={r:10.3f}  2^(k+1)={2**(k+1):3d}  ratio/2^(k+1)={r/2**(k+1):.4f}")

print("\n=== (C) real-ratio antitony R(a) (the clean underlying fact) ===")
allC = True
for n in [64, 128, 256]:
    for k in [1, 2, 3]:
        prev = None
        ok = True
        for a in range(k + 1, n + 1):
            r = R(n, k, a)
            if prev is not None and r > prev + 1e-9:
                ok = False
            prev = r
        allC = allC and ok
print(" (C) real ratio antitone everywhere:", allC)

print("\n=== verdict: is D(a) at deep band a~n/2 SUB-Johnson (i.e. ~sqrt(n))? ===")
for n in [256, 1024, 4096]:
    k = 2
    a = n // 2
    print(f" n={n:5d}: D(n/2)={D(n,k,a):4d}  sqrt(n)={n**0.5:7.2f}  Johnson~n={n}  => D is O(1), NOT sqrt(n): packing floor does NOT reach CORE")
