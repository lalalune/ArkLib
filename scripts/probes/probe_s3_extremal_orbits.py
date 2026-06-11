# S3 falsifier probe (mask-optimized): orbit decomposition of the extremal stacks of
# RS[F5, (1,2,4,3), 2] at delta=1/4 under G = <translation, scaling, gamma-shift, rotation>.
from itertools import product, combinations
p, n, k = 5, 4, 2
xs = [1, 2, 4, 3]
cws = [tuple((a + b*x) % p for x in xs) for a in range(p) for b in range(p)]
subsets3 = [S for r in (3, 4) for S in combinations(range(n), r)]
words = list(product(range(p), repeat=n))
widx = {w: i for i, w in enumerate(words)}
# extension bitmask per word over the 5 admissible subsets
wext = []
for w in words:
    m = 0
    for bit, S in enumerate(subsets3):
        if any(all(c[i] == w[i] for i in S) for c in cws):
            m |= 1 << bit
    wext.append(m)
def badcount(u0, u1):
    e0, e1 = wext[widx[u0]], wext[widx[u1]]
    both = e0 & e1
    cnt = 0
    for g in range(p):
        line = tuple((a + g*b) % p for a, b in zip(u0, u1))
        if wext[widx[line]] & ~both & 0x1F:
            cnt += 1
    return cnt
extremal = set(); maxbad = 0
for u0 in words:
    for u1 in words:
        c = badcount(u0, u1)
        if c > maxbad: maxbad, extremal = c, set()
        if c == maxbad: extremal.add((u0, u1))
print("max bad:", maxbad, "| #extremal stacks:", len(extremal), flush=True)
def orbit_of(stack):
    seen = {stack}; frontier = [stack]
    while frontier:
        u0, u1 = frontier.pop()
        nxt = []
        for c in [cws[1], cws[5]]:
            nxt.append((tuple((a+e) % p for a, e in zip(u0, c)), u1))
            nxt.append((u0, tuple((a+e) % p for a, e in zip(u1, c))))
        nxt.append((tuple(2*a % p for a in u0), tuple(2*a % p for a in u1)))
        nxt.append((tuple((a+b) % p for a, b in zip(u0, u1)), u1))
        nxt.append((tuple(u0[(i+1) % n] for i in range(n)), tuple(u1[(i+1) % n] for i in range(n))))
        for s in nxt:
            if s not in seen:
                seen.add(s); frontier.append(s)
    return seen
remaining = set(extremal); orbits = []
while remaining:
    s = next(iter(remaining))
    o = orbit_of(s)
    viol = sum(1 for t in o if badcount(*t) != maxbad)
    orbits.append((len(o), len(o & extremal), viol))
    remaining -= o
print("orbit decomposition (size, ∩extremal, invariance-violations):", orbits)
print("#orbits:", len(orbits))
