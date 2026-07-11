import math
from math import comb

# Exact calibration data (reproduced digit-for-digit, cd_demand kernel)
# (n, r): worst #bad, maximizer (e,f)
DATA = {
 (16,3): (97,  (8,7)),
 (16,4): (145, (8,5)),
 (16,5): (89,  (9,15)),
 (16,6): (113, (8,10)),
 (16,7): (225, (10,15)),
 (16,8): (104, (9,11)),
 (32,3): (897, (16,15)),
 (32,5): (1441,(17,31)),
}
# r=3 PROVEN closed form
def r3(n): return n*comb(n//4,2)+1

print("=== r=3 proven form check ===")
for n in (16,32,64):
    print(f"  n={n}: n*C(n/4,2)+1 = {r3(n)}")

print("\n=== K budget per (n,r) ===")
for (n,r),(b,ef) in sorted(DATA.items()):
    K = (2**r)*comb(n//2,r)
    print(f"  n={n} r={r}: #bad={b:5d}  K={K:8d}  margin={K/b:.2f}x  maximizer (e,f)={ef}  e-f mod n={(ef[0]-ef[1])%n}  e+f mod n={(ef[0]+ef[1])%n}")

print("\n=== Maximizer exponent normalization (e relative to n/2, f relative to n-1) ===")
for (n,r),(b,ef) in sorted(DATA.items()):
    e,f = ef
    print(f"  n={n} r={r}: e={e}(=n/2{'+' if e>n//2 else ''}{e-n//2 if e!=n//2 else ''}) f={f}(=n-1{'' if f==n-1 else '?'+str(f)}) #bad={b}")
