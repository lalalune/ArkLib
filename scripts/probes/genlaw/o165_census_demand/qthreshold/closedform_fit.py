#!/usr/bin/env python3
"""
Closed-form fit / bound search for the high-freq-monomial deep-band #bad count.

VERIFIED exact data (n=16, faithful BabyBear, deep band a0=r+1, worst-case over monomials):
   r:    3    4    5    6    7    8
 #bad:  97  145   89  113  225  104
   K :  448 1120 1792 1792 1024  256

Structural decomposition (distinct gamma = nonzero gammas + [0 present]):
   r=3: 96 nonzero  + 1(=0)              = 97
   r=4: 144 nonzero + 1(=0)              = 145
   r=5: 88 nonzero  + 1(=0)              = 89
   r=6: 112 nonzero + 1(=0)              = 113
   r=7: 224 nonzero + 1(=0)              = 225
   r=8: 104 nonzero + 0(no 0)           = 104

We test candidate CLOSED FORMS and UPPER BOUNDS against these.
"""
from math import comb

n = 16
m = 4  # n = 2^m
half = n//2  # 8 = 2^{m-1}
bad = {3:97, 4:145, 5:89, 6:113, 7:225, 8:104}
nonzero = {3:96, 4:144, 5:88, 6:112, 7:224, 8:104}
K = {r:(1<<r)*comb(half,r) for r in range(3,9)}

print("=== candidate closed-form / bound tests (n=16) ===\n")

# Candidate A: ceiling spectrum closed form SUM_{l<=r, l==r mod2} C(2^{m-1},l) 2^l  (PROVEN ceiling)
def ceil_spec(r):
    return sum(comb(half, l)*(1<<l) for l in range(0, r+1) if (r-l)%2==0)
print("A. PROVEN ceiling spectrum SUM_{l<=r,l==r mod2} C(8,l)2^l  (this is the SUPPLY/ceiling, UPPER bound on deep?):")
for r in range(3,9):
    cs = ceil_spec(r)
    print(f"   r={r}: ceil_spec={cs:>6}  #bad={bad[r]:>4}  bound>=bad? {cs>=bad[r]}  ceil_spec<=K? {cs<=K[r]}")
print()

# Candidate B: the deep band is one level deeper -- spectrum at subset size a0=r+1 with TWO symmetric
#   constraints. Test "ceiling at size a0" vs "ceiling at size r".
# Candidate C: simple combinatorial bounds
print("C. simple bounds:")
for r in range(3,9):
    a0=r+1
    c1 = comb(n, a0)//(a0)             # pack-ish
    c2 = comb(half,2)*comb(half-2, r-1) if r-1<=half-2 else 0
    c3 = n*comb(half-1, r-1)           # n * C(n/2-1, r-1)
    c4 = comb(n,2)*comb(half-1,r-1)//1
    print(f"   r={r}: #bad={bad[r]:>4}  n*C(7,r-1)={n*comb(half-1,r-1):>5}  C(16,2)*?={'':>3}  2^r C(8,r)=K={K[r]}")
print()

# Candidate D: relate nonzero count to 2 * (something) -- they're all even except check
print("D. nonzero gamma counts and divisibility:")
for r in range(3,9):
    nz = nonzero[r]
    print(f"   r={r}: nonzero={nz:>4}  nz/2={nz/2:.1f}  nz/8={nz/8:.2f}  nz/C(8,r)={nz/comb(half,r):.3f}  nz/2^r={nz/(1<<r):.2f}")
print()

# Candidate E: KEY BOUND -- is #bad <= n * 2^{r-1} ?  (linear in n, exponential modest in r)
print("E. test bound  #bad <= n*2^{r-1}  and  #bad <= 2*K/ (small const):")
for r in range(3,9):
    b1 = n*(1<<(r-1))
    print(f"   r={r}: #bad={bad[r]:>4}  n*2^(r-1)={b1:>5}  bad<=that? {bad[r]<=b1}  K={K[r]}  that<=K? {b1<=K[r]}")
print()

# Candidate F: the WINNING practical bound -- #bad <= K with margin; what is the tightest CLEAN
#   upper bound that is BOTH >= all #bad AND <= K (a sandwich proving the obligation)?
print("F. SANDWICH search: find clean B(n,r) with  #bad <= B(n,r) <= K  for all r:")
cands = {
  "2^r * C(n/2-1, r-1)": lambda r: (1<<r)*comb(half-1,r-1),
  "2^(r-1) * C(n/2, r-1)": lambda r: (1<<(r-1))*comb(half,r-1),
  "n * 2^(r-2)": lambda r: n*(1<<(r-2)),
  "C(n/2,r)*2^(r-2)": lambda r: comb(half,r)*(1<<(r-2)),
  "(n/2)*C(n/2-1,r-1)*?": lambda r: half*comb(half-1,r-1),
}
for name, fn in cands.items():
    rows=[]
    okall=True; sandwich=True
    for r in range(3,9):
        v=fn(r)
        ge = v>=bad[r]; le = v<=K[r]
        if not ge: okall=False
        if not (ge and le): sandwich=False
        rows.append(f"r{r}:{v}({'>=' if ge else '<'}bad,{'<=' if le else '>'}K)")
    print(f"   {name:32s} bound>=bad all? {okall}  sandwich(bad<=B<=K)? {sandwich}")
    print(f"        {'  '.join(rows)}")
