# Empirically validate `mem_sumsetDistinct_signedPowersF` / `admissible_of_primeFactor`
# on NON-Mersenne prime factors q of 2^p - 1 (p prime). The Lean theorem claims: the p-fold
# distinct sumset of G = {±2^j mod q : j<p} is ALL of F_q. We verify via the explicit
# signed-binary witness for every u, and brute-force the full sumset for small q.
from itertools import combinations
from math import comb

def ord2(q, p):
    return pow(2, p, q) == 1 and all(pow(2, d, q) != 1 for d in range(1, p))

def signed_powers(q, p):
    return sorted({pow(2, j, q) for j in range(p)} | {(-pow(2, j, q)) % q for j in range(p)})

def witness_covers_all(q, p):
    # For each u, build T = bits of (2^{p-1} u) mod q, witness e_i = +2^i if i in T else -2^i.
    inv = None
    bad = 0
    for u in range(q):
        w = (pow(2, p-1, q) * u) % q          # w as a residue; lift to its rep in [0,q) < 2^p
        T = [i for i in range(p) if (w >> i) & 1]
        wit = [pow(2, i, q) if (i in set(T)) else (-pow(2, i, q)) % q for i in range(p)]
        if len(set(wit)) != p:                 # must be p DISTINCT signed powers
            bad += 1; continue
        if sum(wit) % q != u:                  # must sum to u
            bad += 1
    return bad

def bruteforce_sumset(q, p):
    G = signed_powers(q, p)
    sums = {sum(c) % q for c in combinations(G, p)}
    return len(sums)

cases = [
    (11, 23), (11, 89),          # 2^11-1 = 2047 = 23 * 89   (composite -> non-Mersenne factors)
    (23, 47), (23, 178481),      # 2^23-1 = 8388607 = 47 * 178481
    (29, 233), (29, 1103), (29, 2089),   # 2^29-1 = 233*1103*2089
    (37, 223),                   # 2^37-1 = 223 * 616318177
    (13, 8191),                  # Mersenne prime control (2^13-1 prime)
]
print(f"{'p':>3} {'q':>8} {'mersenne?':>9} {'ord2=p':>7} {'|G|=2p':>7} {'witness_bad':>11} {'sumset=q':>9}")
for p, q in cases:
    is_mer = (q == 2**p - 1)
    o = ord2(q, p)
    G = signed_powers(q, p)
    gsz = (len(G) == 2*p)
    bad = witness_covers_all(q, p)
    # brute-force only when C(2p,p) is tractable
    bf = ""
    if comb(2*p, p) <= 5_000_000 and q <= 5000:
        bf = "YES" if bruteforce_sumset(q, p) == q else "NO!!"
    print(f"{p:>3} {q:>8} {str(is_mer):>9} {str(o):>7} {str(gsz):>7} {bad:>11} {bf:>9}")
print("\nwitness_bad must be 0 for ALL rows (every u is a sum of p distinct signed powers).")
