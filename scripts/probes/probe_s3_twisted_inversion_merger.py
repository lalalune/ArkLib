# Twisted inversion u(x) -> x*u(1/x): index i holds x=2^i; (Tu)[i] = xs[i]*u[(-i)%4] mod 5.
# Does adding T to the group merge the two extremal orbits? T must be an invariance
# (monomial map stabilizing the code) -- violations must be 0.
from itertools import product, combinations
p, n, k = 5, 4, 2
xs = [1, 2, 4, 3]
cws = [tuple((a + b*x) % p for x in xs) for a in range(p) for b in range(p)]
subsets3 = [S for r in (3, 4) for S in combinations(range(n), r)]
words = list(product(range(p), repeat=n))
widx = {w: i for i, w in enumerate(words)}
wext = []
for w in words:
    m = 0
    for bit, S in enumerate(subsets3):
        if any(all(c[i] == w[i] for i in S) for c in cws):
            m |= 1 << bit
    wext.append(m)
def badcount(u0, u1):
    both = wext[widx[u0]] & wext[widx[u1]]
    return sum(1 for g in range(p)
               if wext[widx[tuple((a + g*b) % p for a, b in zip(u0, u1))]] & ~both & 0x1F)
# sanity: T stabilizes the code
def T(u):
    return tuple(xs[i] * u[(-i) % n] % p for i in range(n))
assert all(T(c) in set(cws) for c in cws), "T does not stabilize the code!"
ex0 = ((0,0,0,1),(0,0,1,1))
def gens(u0, u1):
    out = []
    for c in [cws[1], cws[5]]:
        out.append((tuple((a+e)%p for a,e in zip(u0,c)), u1))
        out.append((u0, tuple((a+e)%p for a,e in zip(u1,c))))
    out.append((tuple(2*a%p for a in u0), tuple(2*a%p for a in u1)))
    out.append((tuple((a+b)%p for a,b in zip(u0,u1)), u1))
    out.append((tuple(u0[(i+1)%n] for i in range(n)), tuple(u1[(i+1)%n] for i in range(n))))
    out.append((T(u0), T(u1)))
    return out
seen = {ex0}; frontier = [ex0]
while frontier:
    s = frontier.pop()
    for t in gens(*s):
        if t not in seen:
            seen.add(t); frontier.append(t)
viol = sum(1 for t in seen if badcount(*t) != 4)
print("T stabilizes code: OK")
print("orbit size with twisted inversion:", len(seen), "| violations:", viol)
print("merged both 50k orbits:" , len(seen) == 100000)
