"""
#407 LANE A2 — n=32 exact threshold via the integer relation-polynomial NORM route
(avoids the C(32,16) ~ 6e8 brute force).

KEY OBSERVATION from n=16 probe: every BAD prime gives #lost=0 — char-0 e2=0 solutions
NEVER disappear mod p. The only defect is SPURIOUS NEW mod-p solutions: a U with
e2(S)=0 mod p but NOT over Z[zeta_n].

For a fixed exponent set U, R_U(zeta) != 0 over C but == 0 mod p iff
   p | N(R_U(zeta))      (the cyclotomic-field norm of the algebraic integer R_U(zeta)),
equivalently p | Res(Phi_n, R_U mod Phi_n)  (resultant). So the set of bad primes for U
is exactly the prime divisors of that norm. The GLOBAL threshold c(n) is therefore
   c(n) = max over all "char-0-nonzero" U  of  (largest prime factor of N(R_U(zeta))).

We cannot enumerate all C(32,16) U. But the n=16 data shows the bad primes are SMALL
(<= n^2.72). We test the HYPOTHESIS that c(n) <= n^3 by:
  (A) confirming the per-U norm-factor bound for a representative + random + structured
      sample of U at n=32 (largest prime factor of the relation norm),
  (B) reporting the max largest-prime-factor found = a LOWER bound on c(32), and checking
      it stays < n^3 = 32768.

We also re-confirm the EXACT structure at n=8 (norm route) to explain WHY c(8) is trivial.
"""
import itertools, math, random
from sympy import symbols, Poly, cyclotomic_poly, ZZ, factorint, primitive_root, isprime, resultant

X = symbols('X')

def phi(n):
    return Poly(cyclotomic_poly(n, X), X, domain=ZZ)

def relpoly(U):
    s = Poly(sum(X**i for i in U), X, domain=ZZ)
    return s*s - Poly(sum(X**(2*i) for i in U), X, domain=ZZ)

def rel_norm(U, Phi, n):
    """N(R_U(zeta)) = Res(Phi_n, R_U mod Phi_n) up to sign; 0 iff char-0 solution."""
    R = relpoly(U) % Phi
    if R.is_zero:
        return 0
    return abs(resultant(Phi.as_expr(), R.as_expr(), X))

def largest_prime_factor(N):
    if N == 0:
        return None
    f = factorint(N)
    return max(f.keys())

def bad_primes_of_U(U, Phi, n):
    N = rel_norm(U, Phi, n)
    if N == 0:
        return None  # char-0 solution; persists, not "bad"
    f = factorint(N)
    # bad SPLIT primes: those p with (p-1)%n==0 (so mu_n exists in F_p)
    return sorted([p for p in f if (int(p)-1) % n == 0])

# --- n=8 : full enumeration of the norm route ---
n = 8
Phi = phi(n)
maxlpf_8 = 0
worst_U = None
allbad8 = set()
for w in range(2, n):
    for U in itertools.combinations(range(n), w):
        bp = bad_primes_of_U(U, Phi, n)
        if bp:
            allbad8 |= set(int(x) for x in bp)
            m = max(int(x) for x in bp)
            if m > maxlpf_8:
                maxlpf_8 = m; worst_U = U
print(f"=== n=8 (full norm enumeration, all widths) ===")
print(f"  set of ALL bad split primes for n=8: {sorted(allbad8)}")
print(f"  c(8) = largest bad split prime = {maxlpf_8 if maxlpf_8 else 'NONE (no split prime divides any relation norm)'}")
print(f"  n^3 = {n**3}\n")

# --- n=16: confirm c(16)=1873 via norm route at width 8 (sampled, to cross-check brute) ---
n = 16
Phi = phi(n)
random.seed(1)
maxlpf_16 = 0
allbad16 = set()
sample = []
# full at small widths + sample width 8
for U in itertools.combinations(range(n), 4):
    sample.append(U)
for _ in range(4000):
    sample.append(tuple(sorted(random.sample(range(n), 8))))
for U in sample:
    bp = bad_primes_of_U(U, Phi, n)
    if bp:
        allbad16 |= set(int(x) for x in bp)
        m = max(int(x) for x in bp)
        maxlpf_16 = max(maxlpf_16, m)
print(f"=== n=16 (norm route; all w=4 + 4000 random w=8) ===")
print(f"  max bad split prime found = {maxlpf_16}  (brute-force exact c(16)=1873; beta={math.log(maxlpf_16)/math.log(16):.3f})")
print(f"  n^3 = {n**3}\n")

# --- n=32: sampled norm route, test c(32) < n^3 hypothesis ---
n = 32
Phi = phi(n)
random.seed(2)
maxlpf_32 = 0
worst32 = None
allbad32 = set()
# structured sample: include the Kambire/extremal-ish coset-ish & random width 16, also smaller widths
samples = []
for _ in range(3000):
    w = random.choice([4,6,8,10,12,14,16])
    samples.append(tuple(sorted(random.sample(range(n), w))))
# add structured: arithmetic-progression and near-coset sets
for step in [1,2,3,4]:
    for start in range(0, n, 2):
        U = tuple(sorted(set((start + j*step) % n for j in range(8))))
        if len(U) >= 4:
            samples.append(U)
nb = 0
for U in samples:
    bp = bad_primes_of_U(U, Phi, n)
    if bp:
        nb += 1
        allbad32 |= set(int(x) for x in bp)
        m = max(int(x) for x in bp)
        if m > maxlpf_32:
            maxlpf_32 = m; worst32 = U
print(f"=== n=32 (norm route; {len(samples)} sampled U, mixed widths) ===")
print(f"  #U with a bad split prime: {nb} / {len(samples)}")
print(f"  largest bad split prime found = {maxlpf_32}", end="")
if maxlpf_32:
    print(f"  (beta=log_32(c)={math.log(maxlpf_32)/math.log(32):.3f},  c/n^3={maxlpf_32/n**3:.4f})  at U={worst32}")
else:
    print()
print(f"  n^3 = {n**3};  n^2.5={n**2.5:.0f};  n^2.72={n**2.72:.0f}")
print(f"  all bad split primes found at n=32 (sample): {sorted(allbad32)[:30]}{' ...' if len(allbad32)>30 else ''}")
print(f"  hypothesis c(32) < n^3=32768 : {'CONSISTENT (max found < n^3)' if (maxlpf_32 and maxlpf_32 < n**3) else 'CHECK'}")
