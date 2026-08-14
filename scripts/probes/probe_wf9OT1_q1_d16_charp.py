"""
wf-OT1 (#444): char-p prize-scale screen of Q1 at d=16.
char-0 is CLEAN (V_16^prim empty, exhaustively). The prize regime is char-p: mod p the
half-basis omega^j (j<8) are NOT Q-independent (all live in F_p), so coincidental
{-1,0,1}-combos can vanish ~ 3^8/p (pigeonhole). HONESTY GATE: a STRUCTURAL failure of Q1
would be an INTEGER point (a genuine vanishing antipodal-free Y over Z[omega]) whose norm is
a fixed integer divisible by ALL prize primes simultaneously. Coincidental mod-p noise does
NOT survive cross-prime. We test:
  per-prime hit count (should ~ 3^8/p), and CROSS-PRIME survival (should be 0).
prize regime: p = n^beta, beta~4..5; here d=16 so p in [16^4, 16^5] = [65536, ~1.05M], p=1 mod 16.
"""
from itertools import product

def is_prime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m); 
        if x in (1,m-1): continue
        ok=False
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: ok=True; break
        if not ok: return False
    return True

def primes_1_mod(n, lo, cap):
    out=[]; p=(lo|1)
    while len(out)<cap:
        if (p-1)%n==0 and is_prime(p): out.append(p)
        p+=2
    return out

def primitive_root_of_unity(p, d):
    # find element of order exactly d in F_p* (d | p-1)
    g=2
    while True:
        if pow(g,(p-1)//2,p)!=1:  # quick non-residue-ish; ensure order
            w=pow(g,(p-1)//d,p)
            if pow(w,d,p)==1 and all(pow(w,d//f,p)!=1 for f in (2,)):  # d=2^mu so only check d/2
                return w
        g+=1

d=16; half=d//2
primes = primes_1_mod(d, d**4, 8)  # prize scale p ~ d^4, 8 primes
print(f"d={d}, half-basis={half}, 3^{half}={3**half}, prize primes (p=1 mod {d}, p>=d^4):")
print("  ", primes)

per_prime_hits = {}
witness_sets = {}  # p -> set of nonempty c-tuples that vanish mod p
for p in primes:
    w = primitive_root_of_unity(p, d)
    basis = [pow(w,j,p) for j in range(half)]
    hits = set()
    for c in product((-1,0,1), repeat=half):
        if any(c):
            s = sum(c[j]*basis[j] for j in range(half)) % p
            if s==0:
                hits.add(c)
    per_prime_hits[p]=len(hits)
    witness_sets[p]=hits
    print(f"  p={p}: per-prime nonempty hits = {len(hits)}  (~3^8/p = {3**half/p:.3f})")

# CROSS-PRIME survival: a structural integer point vanishes mod EVERY prime
common = None
for p in primes:
    common = witness_sets[p] if common is None else (common & witness_sets[p])
print(f"\nCROSS-PRIME survivors (vanish mod ALL {len(primes)} prize primes simultaneously): {len(common)}")
if common:
    print("   SURVIVORS (candidate structural Q1 failures):", list(common)[:5])
else:
    print("   => 0 survivors. The per-prime hits are PIGEONHOLE/mod-p NOISE, not structural.")
    print("   => Q1(*)_16 does NOT fail at prize scale. char-0 cleanness is faithful char-p.")
