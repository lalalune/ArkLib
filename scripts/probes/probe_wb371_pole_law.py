#!/usr/bin/env python3
"""
The pole law probe (k=1): classify bad-count mechanisms for pole-stratum stacks.

FAST is_bad for k=1:  bad(gamma) <=> exists value v with level set
P_v = {i : u0_i + g*u1_i = v}, |P_v| >= n-w, and NOT(u0 const on P_v AND u1 const on P_v).
[Proof: k=1 explainability on S <=> line const on S; S subset of a level set.
 If both rows const on P_v, every S in P_v is jointly explained; else pick S
 containing a witness non-constancy pair, |S|=n-w <= |P_v|.]

Conjecture under test (P-law): for u0 pole-type with w0 = #poles-in-D,
u1 genuine:  bad <= w0 + 1.   P x P: bad <= ??? (collect data).
Scales: (13,6,1,2) structured-exhaustive; (13,12,1,4) targeted structured.
"""
import itertools, random
from collections import Counter

def order_subgroup(q, n):
    for cand in range(2, q):
        seen = set(); x = 1
        for _ in range(q - 1):
            x = (x * cand) % q; seen.add(x)
        if len(seen) == q - 1:
            g = cand; break
    h = pow(g, (q - 1) // n, q)
    return sorted({pow(h, j, q) for j in range(n)})

def make_ctx(q, n, w):
    D = order_subgroup(q, n)
    return dict(q=q, n=n, w=w, D=D, need=n - w)

def fast_bad_set(ctx, u0, u1):
    q, n, need = ctx['q'], ctx['n'], ctx['need']
    out = []
    for g in range(q):
        line = [(u0[i] + g * u1[i]) % q for i in range(n)]
        levels = {}
        for i, v in enumerate(line):
            levels.setdefault(v, []).append(i)
        ok = False
        for v, P in levels.items():
            if len(P) >= need:
                c0 = all(u0[i] == u0[P[0]] for i in P)
                c1 = all(u1[i] == u1[P[0]] for i in P)
                if not (c0 and c1):
                    ok = True; break
        if ok:
            out.append(g)
    return out

def poleval(p, x, q):
    return sum(c * pow(x, i, q) for i, c in enumerate(p)) % q

def polmul(a, b, q):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % q
    return out

# ---------------- scale 1: (13,6,1,2) ----------------
ctx = make_ctx(13, 6, 2)
q, n, w, D = 13, 6, 2, ctx['D']
print(f"scale 1: D = {D}")

# genuine locators: monic deg<=2 nonvanishing on D (deg2 + deg1 + deg0)
genuine_l = []
for a in range(q):
    for b in range(q):
        l = [a, b, 1]
        if all(poleval(l, x, q) for x in D):
            genuine_l.append(l)
for a in range(q):
    l = [a, 1]
    if all(poleval(l, x, q) for x in D):
        genuine_l.append(l)
genuine_l.append([1])
print(f"genuine locators: {len(genuine_l)}")

def genuine_words():
    """all u = R/l, l in genuine_l, R deg <= w+k-1 = 2; dedupe."""
    seen = set()
    for l in genuine_l:
        invs = [pow(poleval(l, x, q), q - 2, q) for x in D]
        for R in itertools.product(range(q), repeat=3):
            u = tuple((poleval(R, x, q) * invs[i]) % q for i, x in enumerate(D))
            if u not in seen:
                seen.add(u)
                yield u

GEN = list(genuine_words())
print(f"distinct genuine words: {len(GEN)}")

# pole-type u0: pure spikes (R0 = 0): u0 = 0 off Z, values on Z
# w0 = 1: Z = {z}; w0 = 2: Z = {z1,z2}
results = Counter(); witnesses = {}
print("\n=== P x G sweep: u0 = pure spike, u1 genuine (exhaustive) ===")
for w0 in (1, 2):
    mx = 0; arg = None
    for Z in itertools.combinations(range(n), w0):
        # spike values up to scaling: first = 1, rest free
        for vals in itertools.product(range(1, q), repeat=w0 - 1):
            sv = (1,) + vals
            u0 = [0] * n
            for j, i in enumerate(Z):
                u0[i] = sv[j]
            u0 = tuple(u0)
            for u1 in GEN:
                b = len(fast_bad_set(ctx, u0, u1))
                if b > mx:
                    mx = b; arg = (u0, u1)
    results[f"PxG w0={w0}"] = mx; witnesses[f"PxG w0={w0}"] = arg
    print(f"  w0={w0}: max bad = {mx}  (conjecture w0+1={w0+1})  witness={arg}")

# spike + nonzero rational part (sampled)
print("\n=== P x G: spike + rational part (sampled) ===")
random.seed(9)
for w0 in (1, 2):
    mx = 0; arg = None
    for _ in range(40000):
        Z = random.sample(range(n), w0)
        u1 = random.choice(GEN)
        ubase = random.choice(GEN)
        u0 = list(ubase)
        for i in Z:
            u0[i] = random.randrange(q)
        u0 = tuple(u0)
        b = len(fast_bad_set(ctx, u0, u1))
        if b > mx:
            mx = b; arg = (u0, u1, tuple(Z))
    print(f"  w0={w0}: max bad = {mx}  witness={arg}")

# P x P (sampled exhaustively-ish for pure spikes; spikes can overlap)
print("\n=== P x P: pure spikes both rows (exhaustive w0,w1<=2) ===")
mx = 0; arg = None
for Z0 in itertools.chain(itertools.combinations(range(n), 1), itertools.combinations(range(n), 2)):
    for sv0 in itertools.product(range(1, q), repeat=len(Z0) - 1):
        u0 = [0] * n
        vals0 = (1,) + sv0
        for j, i in enumerate(Z0):
            u0[i] = vals0[j]
        u0 = tuple(u0)
        for Z1 in itertools.chain(itertools.combinations(range(n), 1), itertools.combinations(range(n), 2)):
            for v1 in itertools.product(range(1, q), repeat=len(Z1)):
                u1 = [0] * n
                for j, i in enumerate(Z1):
                    u1[i] = v1[j]
                u1 = tuple(u1)
                b = len(fast_bad_set(ctx, u0, u1))
                if b > mx:
                    mx = b; arg = (u0, u1)
print(f"  pure-spike PxP: max bad = {mx}  witness={arg}")

# spike + codeword shift (= noisy codewords, both rows): known cap w=2 from
# earlier probe; re-verify with fast engine on samples
print("\n=== sanity: noisy x noisy (sampled, fast engine) ===")
mx = 0
for _ in range(200000):
    u0 = [random.randrange(q)] * n
    for i in random.sample(range(n), random.randrange(0, w + 1)):
        u0[i] = random.randrange(q)
    u1 = [random.randrange(q)] * n
    for i in random.sample(range(n), random.randrange(0, w + 1)):
        u1[i] = random.randrange(q)
    b = len(fast_bad_set(ctx, tuple(u0), tuple(u1)))
    mx = max(mx, b)
print(f"  noisy x noisy: max bad = {mx}")

# ---------------- scale 2: (13,12,1,4) targeted ----------------
print("\n=== scale 2 (13,12,1,4): targeted structured search ===")
ctx2 = make_ctx(13, 12, 4)
q2, n2, w2, D2 = 13, 12, 4, ctx2['D']
inv2 = {x: pow(x, q2 - 2, q2) for x in D2}
sigma2 = {x: (-inv2[x]) % q2 for x in D2}
idx2 = {x: i for i, x in enumerate(D2)}
# sigma orbits on mu_12
seen = set(); orbs2 = []
for x in D2:
    if x in seen: continue
    o = [x]; seen.add(x); y = sigma2[x]
    while y != x:
        o.append(y); seen.add(y); y = sigma2[y]
    orbs2.append(tuple(sorted(o)))
print(f"  sigma orbits on mu_12: {orbs2}")

# genuine sigma-invariant u1 candidates: u1 const on sigma-orbits AND WBSolvable
# (cheap WBSolvable test: det of 13x13? n=12 > 2w+k+1 = 10 -> rank test on 12x10)
def wb_solvable2(y):
    # matrix 12 x (w+1 + w+k) = 12 x 10 over F13: solvable iff rank < 10
    M = []
    for i, x in enumerate(D2):
        row = [(pow(x, t, q2) * y[i]) % q2 for t in range(w2 + 1)] + \
              [(-pow(x, s, q2)) % q2 for s in range(w2 + 1)]
        M.append(row)
    # rank
    r = 0; C = 10
    for col in range(C):
        piv = None
        for row in range(r, n2):
            if M[row][col] % q2:
                piv = row; break
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        ip = pow(M[r][col], q2 - 2, q2)
        for row in range(n2):
            if row != r and M[row][col] % q2:
                f = (M[row][col] * ip) % q2
                for cc in range(C):
                    M[row][cc] = (M[row][cc] - f * M[r][cc]) % q2
        r += 1
    return r < 10

# spike u0 on structured Z (sigma-orbits, mu_4-coset {x: x^4=1}-ish, random)
import random as rnd
rnd.seed(13)
structuredZ = []
for o in orbs2:
    if len(o) <= w2: structuredZ.append(tuple(sorted(o)))
for c in range(3):
    structuredZ.append(tuple(sorted(rnd.sample(D2, 2))))
    structuredZ.append(tuple(sorted(rnd.sample(D2, 4))))
# also coset of mu_4 = {1,5,8,12}: elements of order dividing 4
mu4 = tuple(sorted(x for x in D2 if pow(x, 4, q2) == 1))
structuredZ.append(mu4)
mu2c = []
for x in D2:
    pair = tuple(sorted({x, (-x) % q2}))
    if pair not in mu2c: mu2c.append(pair)
structuredZ.extend([tuple(sorted(set(a) | set(b))) for a, b in itertools.combinations(mu2c[:4], 2)])
structuredZ = [Z for Z in dict.fromkeys(structuredZ) if len(Z) <= w2]
print(f"  structured Z list: {len(structuredZ)}")

# u1: sigma-invariant WBSolvable words (sampled from orbit-value assignments)
inv_candidates = []
tries = 0
while len(inv_candidates) < 400 and tries < 60000:
    tries += 1
    vals = {o: rnd.randrange(q2) for o in orbs2}
    u1 = [0] * n2
    for o, v in vals.items():
        for x in o:
            u1[idx2[x]] = v
    u1 = tuple(u1)
    if wb_solvable2(u1):
        inv_candidates.append(u1)
print(f"  sigma-invariant WBSolvable u1 pool: {len(inv_candidates)}")

mx2 = 0; arg2 = None
for Z in structuredZ:
    Zi = [idx2[x] for x in Z]
    for trial in range(60):
        u0 = [0] * n2
        # spike values: constant 1, or random, or sigma-pattern
        mode = trial % 3
        for j in Zi:
            u0[j] = 1 if mode == 0 else rnd.randrange(1, q2)
        u0 = tuple(u0)
        for u1 in rnd.sample(inv_candidates, min(80, len(inv_candidates))):
            b = len(fast_bad_set(ctx2, u0, u1))
            if b > mx2:
                mx2 = b; arg2 = (Z, u0, u1)
print(f"  scale-2 targeted P x G(sigma-inv): max bad = {mx2}  (w+1={w2+1}, w+3={w2+3})")
if arg2:
    print(f"    witness Z={arg2[0]}")
    print(f"    u0={arg2[1]}")
    print(f"    u1={arg2[2]}")
