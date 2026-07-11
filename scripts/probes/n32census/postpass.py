"""Post-pass for the n=32 census: dedup, independent re-verification, witness/dense split,
cross-check vs the 35 constructed witnesses u_S(X^2), O63 coefficient-spread classes."""
import glob
import itertools
from collections import Counter

p = 2013265921
g0 = 31
N, K, A = 32, 16, 18
LAM = 284861408
E1 = (-LAM) % p  # 1728404513 = g0^((p-1)/4)

H = [pow(g0, (p-1)//N*i, p) for i in range(N)]
G = [pow(g0, (p-1)//16*i, p) for i in range(16)]
w = [(pow(x, 18, p) + LAM*pow(x, 16, p)) % p for x in H]

def inv(a): return pow(a, p-2, p)

rows = set()
for f in sorted(glob.glob('/tmp/n32census/n32_*.txt')):
    for line in open(f):
        rows.add(tuple(map(int, line.split())))
print(f"distinct candidates after dedup: {len(rows)}")
assert len(rows) <= 10**6, "ABORT THRESHOLD: report partial count as LOWER bound"

# independent verification + coefficient extraction (Newton-free direct Lagrange basis coeffs)
def coeffs_of(vals):
    cs = [0]*N
    for i in range(N):
        num = [1]; den = 1
        for j in range(N):
            if i == j: continue
            new = [0]*(len(num)+1)
            for t, a in enumerate(num):
                new[t] = (new[t]-a*H[j]) % p
                new[t+1] = (new[t+1]+a) % p
            num = new
            den = den*(H[i]-H[j]) % p
        c = vals[i]*inv(den) % p
        for t, a in enumerate(num):
            cs[t] = (cs[t]+c*a) % p
    return cs

# the 35 constructed witnesses u_S(X^2)
def poly_from_roots(S):
    c = [1]
    for r_ in S:
        new = [0]*(len(c)+1)
        for t, a in enumerate(c):
            new[t] = (new[t]-a*r_) % p
            new[t+1] = (new[t+1]+a) % p
        c = new
    return c
witness_words = set()
for S in itertools.combinations(G, 9):
    if sum(S) % p != E1: continue
    v = poly_from_roots(S)
    u = [(-a) % p for a in v[:8]]            # u_S deg<=7: x^9 - e1 x^8 = u_S(x) on S
    def evu(x):
        r = 0
        for a in reversed(u): r = (r*x + a) % p
        return r
    witness_words.add(tuple(evu(pow(x, 2, p)) for x in H))
print(f"constructed witness family size (fiber of e1={E1}): {len(witness_words)} (expect 35)")

def digitcode(e, depth):
    ds = []
    for _ in range(depth):
        d = e & 1
        ds.append(d)
        e = (e + d) >> 1
    return tuple(ds)

ags = Counter(); wit = dense = 0; in_constructed = 0
spread_sig = Counter()
spread_counts = Counter()
bad = 0
for v in sorted(rows):
    ag = sum(1 for i in range(N) if v[i] == w[i])
    if ag < A:
        bad += 1; continue
    ags[ag] += 1
    cs = coeffs_of(list(v))
    assert all(c == 0 for c in cs[K:]), "candidate not deg<K!"
    sup_c = [d for d in range(K) if cs[d]]
    is_wit = all(d % 2 == 0 for d in sup_c)
    wit += is_wit; dense += (not is_wit)
    in_constructed += (v in witness_words)
    # O63 spread of the error e = (X^18 + lam X^16) - c : support = {16,18} U sup(c)
    sup_e = sorted(set(sup_c) | {16, 18})
    sig = tuple(len({digitcode(e, l) for e in sup_e}) for l in (1, 2, 3))
    classes3 = frozenset(digitcode(e, 3) for e in sup_e)
    spread_sig[(is_wit, sig)] += 1
    spread_counts[(is_wit, classes3)] += 1

print(f"VERIFIED list size l_32(w,18) = {sum(ags.values())} (failed re-verification: {bad})")
print(f"witness/dense split: {wit} witnesses (all-even support) + {dense} dense")
print(f"census ∩ constructed u_S(X^2) family: {in_constructed} / 35")
print(f"agreement histogram: {dict(sorted(ags.items(), reverse=True))}")
print("O63 spread signatures (is_witness, (#classes mod 2, mod 4, mod 8)) -> count:")
for k, c in sorted(spread_sig.items()):
    print(f"   {k}: {c}")
print("depth-3 class-set signatures (is_witness, frozenset of digit codes) -> count:")
for (isw, cls), c in sorted(spread_counts.items(), key=lambda x: (x[0][0], -x[1])):
    print(f"   wit={isw} classes={sorted(cls)}: {c}")

total = sum(ags.values())
print("\n=== threshold comparison ===")
print(f"  structured core (fiber)              : 35")
print(f"  list / core enrichment ratio          : {total/35:.2f}  (n=16 ratio was 19/3 = 6.33)")
print(f"  per-line bad-scalar count N0(16,9)    : 3280   -> list {'<' if total < 3280 else '>='} 3280")
print(f"  Conjecture-D falsification line       : poly(32)*3280 (e.g. 32*3280 = 104960)")
print(f"  2^(H(rho)/eta) budget, rho=1/2,eta=1/16: 2^16 = 65536 -> list {'<' if total < 65536 else '>='} 65536")
print(f"  abort threshold                       : 10^6")
