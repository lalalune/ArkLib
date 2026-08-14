# PROBE: leading-exponent of complete-homogeneous h_r=C(s+r-1,r) over subset-sum e_r=C(s,r)
# at the SYMMETRIC BINDING FOLD r/s = 1/2 (the dossier's load-bearing fold for delta*, NOT the r=s endpoint).
# Claim (F6 prose, never a theorem): log(h_r/e_r)/s -> 0.26... as s->inf with r = s/2.
# Goal: pin the EXACT closed-form constant + find a clean LOWER bound bounded away from 0.
from math import comb, log, lgamma

def logcomb(n, k):  # log C(n,k) via lgamma (no overflow)
    if k < 0 or k > n: return float('-inf')
    return lgamma(n+1) - lgamma(k+1) - lgamma(n-k+1)

print("=== symmetric fold r = s/2, log(h/e)/s ===")
for s in [16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192]:
    r = s // 2
    lh = logcomb(s + r - 1, r)   # log h_r
    le = logcomb(s, r)           # log e_r
    val = (lh - le) / s
    print(f"s={s:5d} r={r:5d}  log(h/e)/s = {val:.6f}")

# exact closed-form limit at r = alpha*s (Stirling/entropy):
# log h_r ~ s*[(1+a)log(1+a) - a log a]
# log e_r ~ s*[ -a log a - (1-a)log(1-a) ]
# L(a) = (1+a)log(1+a) + (1-a)log(1-a)
def L(a):
    return (1+a)*log(1+a) + (1-a)*log(1-a)
print("\n=== exact closed-form limit L(a) = (1+a)ln(1+a) + (1-a)ln(1-a) ===")
for a in [0.25, 0.5, 0.75, 0.9, 0.99]:
    print(f"a={a:.2f}  L(a) = {L(a):.6f}")
print(f"\nL(1/2) exact = (3/2)ln(3/2) + (1/2)ln(1/2) = {1.5*log(1.5)+0.5*log(0.5):.6f}")
print(f"   = (3/2)ln3 - 2ln2 = {1.5*log(3) - 2*log(2):.6f}")
print(f"L(a) INCREASING on (0,1): L(~0)={L(0.0001):.4f} -> L(1^-) -> 2ln2 = {2*log(2):.6f}")
print("MAX leading-exp 2ln2=1.386 at a->1 (r=s endpoint chexp took); BINDING fold a=1/2 = (3/2)ln3-2ln2=0.2616")

# The REAL load-bearing content: L(a) > 0 STRICTLY for all a in (0,1) -> ch leading exp STRICTLY exceeds e.
print("\n=== L(a) > 0 strictly on (0,1)? (the load-bearing 'strictly larger leading exponent') ===")
import random
fails = 0
for _ in range(100000):
    a = random.random()
    if not (0 < a < 1):
        continue
    if L(a) <= 0:
        fails += 1
print(f"L(a)<=0 fails: {fails}/100000  (L(a)>0 strictly <=> ch leading exp > e leading exp)")
