"""
#407 LANE A2 — THE decisive prize-regime question:
For n=32 with prize prime q ~ n^4..n^5 (= 1.05e6 .. 3.4e7), c(32) ~ 3.2e12 = n^8.3 >> q.
So the e2=0 rigidity transfer FAILS in the prize regime for n=32: there ARE spurious mod-q
e2=0 solutions. Does this CORRUPT the bad-scalar count in the prize regime?

We cannot brute C(32,16). But we can:
 (1) For a sample of prize-regime split primes q ~ n^4 and n^5 at n=32, check whether ANY
     sampled U (char-0 e2 != 0) becomes a spurious mod-q e2=0 solution (count of corruptions).
 (2) Compare to n=16, where c(16)=1873 = n^2.72 < q_prize, so prize regime IS clean (no corruption).

This pins the HONEST scope of the lane A2 partial closure:
  - n=16: c(16) < prize q  => e2=0 locus IS char-0 in prize regime => clean partial closure.
  - n=32+: c(n) >> prize q => spurious solutions EXIST in prize regime => NO clean closure;
    the char-p transfer wall is REAL here (consistent with the KB 'char-p transfer = #389 wall').
"""
import itertools, math, random
from sympy import symbols, Poly, cyclotomic_poly, ZZ, primitive_root, isprime, nextprime

X = symbols('X')
def phi(n): return Poly(cyclotomic_poly(n, X), X, domain=ZZ)

def char0_e2zero(U, Phi):
    s = Poly(sum(X**i for i in U), X, domain=ZZ)
    R = (s*s - Poly(sum(X**(2*i) for i in U), X, domain=ZZ)) % Phi
    return R.is_zero
def char0_e1zero(U, Phi):
    return (Poly(sum(X**i for i in U), X, domain=ZZ) % Phi).is_zero

def split_prime_near(n, target):
    p = target
    while not (isprime(p) and (p-1) % n == 0):
        p += 1
    return p

def corruption_rate(n, qprime, nsamp, width, seed=0):
    """fraction of sampled U (char-0 e2!=0, e1!=0 over Z[zeta]) that are spurious e2=0 mod q."""
    Phi = phi(n)
    g = pow(primitive_root(qprime), (qprime-1)//n, qprime)
    mu = [pow(g, j, qprime) for j in range(n)]
    random.seed(seed)
    corrupt = 0; valid = 0; char0sol = 0
    for _ in range(nsamp):
        U = tuple(sorted(random.sample(range(n), width)))
        if char0_e1zero(U, Phi):
            continue
        if char0_e2zero(U, Phi):
            char0sol += 1
            continue  # genuine char-0 solution, not corruption
        valid += 1
        S = [mu[i] for i in U]
        e1 = sum(S) % qprime
        if e1 == 0:
            continue
        p2 = sum((x*x) % qprime for x in S) % qprime
        if (e1*e1 - p2) % qprime == 0:
            corrupt += 1  # spurious mod-q e2=0
    return corrupt, valid, char0sol

for n in [16, 32]:
    print(f"\n=== n={n}: prize-regime corruption test ===")
    for beta, label in [(4, "q~n^4"), (5, "q~n^5")]:
        q = split_prime_near(n, n**beta)
        corrupt, valid, c0 = corruption_rate(n, q, 4000, n//2)
        print(f"  {label}: q={q} (beta={math.log(q)/math.log(n):.2f}); sampled {valid} char-0-nonzero width-{n//2} U:")
        print(f"    spurious mod-q e2=0 (corruptions): {corrupt}  ({100*corrupt/max(valid,1):.3f}%);  char-0 solutions seen: {c0}")
    # threshold comparison
    cn = {16: 1873, 32: 3184895024161}[n]
    print(f"  c({n}) = {cn} = n^{math.log(cn)/math.log(n):.2f};  prize q~n^4={n**4}, n^5={n**5}")
    verdict = "CLEAN (c < prize q): e2=0 rigidity HOLDS in prize regime => partial closure valid" if cn < n**4 else \
              "CORRUPTED (c >> prize q): spurious solutions exist in prize regime => char-p wall REAL"
    print(f"  ==> {verdict}")
