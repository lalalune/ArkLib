from math import comb

# COMPLETE exact data this pass (kernel-verified, digit-for-digit)
# n, r, #bad (global worst over monomial lines)
DATA = [
 (16,3, 97),
 (16,4, 145),
 (16,5, 89),
 (16,6, 113),
 (16,7, 225),
 (16,8, 104),
 (32,3, 897),
 (32,4, 3105),   # NEW this pass: (x^16,x^9)/(x^16,x^25), corner+row confirmed
 (32,5, 1441),
]

print("COMPLETE DATA + K and clean-bound candidates:\n")
print(f"{'n':>3}{'r':>3}{'bad':>6}{'K':>9}{'K/bad':>7} | {'K/2':>7} {'K/4':>7} {'4^r*C(n/2,r)/?':>6}")
allK2=True; allK4=True
for n,r,bad in DATA:
    K=(2**r)*comb(n//2,r)
    k2=bad<=K//2; k4=bad<=K//4
    allK2 = allK2 and k2; allK4=allK4 and k4
    print(f"{n:>3}{r:>3}{bad:>6}{K:>9}{K/bad:>7.2f} | {('OK' if k2 else 'X'):>3}{K//2:>5} {('OK' if k4 else 'X'):>3}{K//4:>5}")
print(f"\n#bad <= K/2 holds at ALL points: {allK2}")
print(f"#bad <= K/4 holds at ALL points: {allK4}")

# The asymptotic margin of the r=3 PROVEN form is 16/3 = 5.33x = K/#bad -> so #bad/K -> 3/16 < 1/4.
print(f"\nr=3 proven asymptotic ratio #bad/K -> 3/16 = {3/16:.4f} (so r=3 satisfies #bad <= K/4 asymptotically; small-n margin {97/448:.4f})")

# Min margin across all data
mm = min(((2**r)*comb(n//2,r))/bad for n,r,bad in DATA)
print(f"\nMIN margin K/#bad across all computed points = {mm:.3f}x (worst case: n=16 r=8)")
print(f"So the cleanest PROVABLE-target bound consistent with all data: #bad <= K/2 (every point), tight-ish only at n=16 r=8 ({256/104:.2f}x)")

# Scaling test: n=16 -> n=32
print("\n=== n-scaling 16->32 (no clean exponent) ===")
for r in (3,4,5):
    b16=dict((rr,b) for nn,rr,b in DATA if nn==16)[r]
    b32=dict((rr,b) for nn,rr,b in DATA if nn==32)[r]
    print(f"  r={r}: {b16} -> {b32}, ratio {b32/b16:.2f}  (n^2 would be 4.0; n^3/... varies)")
