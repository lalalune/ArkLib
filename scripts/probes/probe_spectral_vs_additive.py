"""
PROBE: spectral 2r-th moment vs additive energy, to pin which "E_r" the leading forms describe.

For S subset Z_N, the spectral energy
   Spec_r = sum_{b in Z_N} |sum_{x in S} e(bx/N)|^{2r}
         = N * #{(a in S^r, b in S^r): sum a = sum b mod N}     (Parseval/orthogonality)
         = N * AddEnergy_r.
So Spec_r and AddEnergy_r differ ONLY by the global factor N (number of frequencies). The PER-FREQUENCY
average Spec_r / N = AddEnergy_r. NEITHER equals (2r-1)!! (n)_r at r=2 (that's 168 vs additive 120, n=8).

So WHERE does (2r-1)!! come from? It's the GAUSSIAN/Wick moment: for an n-term sum of INDEPENDENT mean-0
unit-variance phases, E|sum|^{2r} = (2r-1)!! n^r (Wick). The char-0 SUBGROUP energy is NOT the independent
model; the falling-factorial (n)_r REPLACES n^r when you enforce DISTINCT indices in the Wick pairing. So
'(2r-1)!!(n)_r' = the Wick formula with sampling-WITHOUT-replacement per contraction. That is a MODEL
prediction (the 'antipodal-matching with distinct pair-values'), NOT the exact additive energy.

CONCLUSION to record: 
 - AddEnergy_r (exact, my LANE-1 partition formula) has leading term L_r = r!(n)_r, NOT (2r-1)!!(n)_r.
 - (2r-1)!!(n)_r is the WICK-MODEL value (independent-pairing with distinct values), an UPPER reference,
   = the 'ff' bound. The exact additive energy is BELOW it (120 < 168, 2528 < 5040).
 - So 'E_r^char0 = (2r-1)!!(n)_r exact at r=2' is only true for the WICK-MODEL energy, not the literal
   additive count. The literal additive E_2 = 2n^2 - n = L_2 + n.
Verify Spec_r = N * AddEnergy_r on a small modulus where S is a genuine subgroup.
"""
import cmath, math

def isprime(m):
    i = 2
    while i * i <= m:
        if m % i == 0:
            return False
        i += 1
    return m > 1

def subgroup(p, n):
    e = (p - 1) // n
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and len({pow(h, i, p) for i in range(n)}) == n:
            return [pow(h, i, p) for i in range(n)]
    return None

def spectral_energy(S, p, r):
    tot = 0.0
    for b in range(p):
        s = sum(cmath.exp(2j * math.pi * b * x / p) for x in S)
        tot += abs(s) ** (2 * r)
    return tot

def add_energy_modp(S, p, r):
    from collections import Counter
    c = Counter({0: 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for x in S:
                nc[(v + x) % p] += m
        c = nc
    return sum(m * m for m in c.values())

print("Spec_r =? p * AddEnergy_r (mod p), genuine subgroup:")
for p, n in [(17, 4), (41, 8), (97, 8)]:
    S = subgroup(p, n)
    for r in [2, 3]:
        spec = spectral_energy(S, p, r)
        add = add_energy_modp(S, p, r)
        print(f"  p={p} n={n} r={r}: Spec={spec:>14.2f}  p*Add={p*add:>14}  ratio={spec/(p*add):.6f}")
