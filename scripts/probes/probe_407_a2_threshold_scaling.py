"""
#407 LANE A2 — how does the EXACT threshold c(n) scale, and does the large bad prime
change the bad-SCALAR COUNT (the thing delta* actually depends on)?

(A) SCALING of c(n): max-over-U largest split prime factor of the relation norm.
    We bound it below by sampling and compare to n^3, n^(n/2)-ish, and the Lean
    provable (n^2+n)^(n/2). KEY question: is the true c(n) poly(n) [=> partial closure
    for the prize] or super-poly [=> char-p wall persists in prize regime]?

    The relation norm N(R_U(zeta)) is a product of ~phi(n)=n/2 conjugate values, each of
    size O(|U|^2) in archimedean abs value, so |N| <= (|U|^2 + |U|)^(n/2) -- exactly the
    Lean bound. The LARGEST PRIME FACTOR of a generic integer of size B is typically ~B,
    so c(n) ~ (n^2)^(n/2) = n^n GENERICALLY -- super-poly. We test this prediction.

(B) Does the spurious solution change the COUNT? For n=16 at the largest bad prime 1873,
    compare the bad-scalar count / orbit-count K to the char-0 value. If the count is
    UNCHANGED despite the locus differing, the 'count threshold ~ n^3' claim is about a
    DIFFERENT (coarser) quantity than the locus threshold ~ super-poly.
"""
import itertools, math, random
from sympy import symbols, Poly, cyclotomic_poly, ZZ, factorint, resultant, primitive_root, isprime

X = symbols('X')
def phi(n): return Poly(cyclotomic_poly(n, X), X, domain=ZZ)
def relnorm_lpf_split(U, Phi, n):
    s = Poly(sum(X**i for i in U), X, domain=ZZ)
    R = (s*s - Poly(sum(X**(2*i) for i in U), X, domain=ZZ)) % Phi
    if R.is_zero: return None, None
    N = abs(resultant(Phi.as_expr(), R.as_expr(), X))
    if N == 0: return None, None
    f = factorint(N)
    sf = [int(p) for p in f if (int(p)-1)%n==0]
    return (max(sf) if sf else None), int(N)

# (A) scaling: max split-prime over a sample, and max |N| (Hadamard-type), per n
print("=== (A) c(n) scaling: max split-prime factor (sampled) vs |N| size vs Lean bound ===")
print(f"{'n':>3} {'#sampled':>8} {'max split p found':>20} {'beta=log_n(c)':>14} {'max|N| (log_n)':>14} {'Lean (n^2+n)^(n/2) log_n':>22}")
random.seed(0)
for n in [8, 16, 32, 64]:
    Phi = phi(n)
    nsamp = {8: None, 16: 4000, 32: 1500, 64: 400}[n]
    maxp = 0; maxN = 0
    if nsamp is None:
        Us = [U for w in range(2,n) for U in itertools.combinations(range(n), w)]
    else:
        Us = []
        for _ in range(nsamp):
            w = random.choice([4,6,8] if n<=16 else [6,8,12,16])
            Us.append(tuple(sorted(random.sample(range(n), w))))
    for U in Us:
        lpf, N = relnorm_lpf_split(U, Phi, n)
        if lpf: maxp = max(maxp, lpf)
        if N: maxN = max(maxN, N)
    betap = math.log(maxp)/math.log(n) if maxp else float('nan')
    betaN = math.log(maxN)/math.log(n) if maxN else float('nan')
    lean = (n//1)*((n*n+n)) ; lean_logn = (n//2)*math.log(n*n+n)/math.log(n)
    print(f"{n:>3} {len(Us):>8} {maxp:>20} {betap:>14.2f} {betaN:>14.2f} {lean_logn:>22.1f}")

# (B) does the count change at n=16 across the bad-prime threshold?
print("\n=== (B) n=16, width 8: bad-scalar COUNT and orbit-count K across primes ===")
n = 16; h = 8
def count_K(n, p):
    g = pow(primitive_root(p), (p-1)//n, p)
    mu = [pow(g,j,p) for j in range(n)]
    e1vals = []; cnt = 0
    for U in itertools.combinations(range(n), h):
        S = [mu[i] for i in U]
        e1 = sum(S) % p
        if e1 == 0: continue
        p2 = sum((x*x)%p for x in S) % p
        if (e1*e1-p2)%p==0:
            cnt += 1; e1vals.append(e1)
    rem = set(e1vals); K = 0
    while rem:
        x = next(iter(rem)); rem -= set((u*x)%p for u in mu); K += 1
    return cnt, len(set(e1vals)), K
for p in [1697, 1873, 1889, 2017, 4129, 65537]:  # 1873 = c(16); 1889,2017 > c(16)
    while not (isprime(p) and (p-1)%n==0): p += 1
    cnt, dist, K = count_K(n, p)
    tag = " (=c16, last bad)" if p==1873 else (" (>c16, clean)" if p>1873 else " (<c16, bad)")
    print(f"  p={p:6d} (beta={math.log(p)/math.log(n):.2f}): count={cnt:4d} distinct_e1={dist:3d} K={K}{tag}")
print("  char-0 value (p large): count=64, distinct_e1=48, K=3")
