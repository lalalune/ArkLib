#!/usr/bin/env python3
"""
FIRST deep-window doubly-rational probe: (q,n,k,w) = (11,10,1,4).
Window: 2w+k+1 = 10 <= n=10 <= 3w+k-1 = 12; D_def = 3w+k-1-n = 2.
D = mu_10 = F_11^*.  Radius w/n = 2/5; agreement floor n-w = 6.

This is the regime where the staircase lane's absorption provably fails
("lower strip rows open, new mechanism needed") and where WindowRationalBounded's
budget w+3 = 7 is untested.  Conjecture under test: bad <= w+1 = 5 (maybe much less).

Strategy: targeted + random search over doubly-WBSolvable stacks:
  - genuine x genuine (locators nonvanishing on D)
  - pole x genuine, pole x pole (spikes)
  - sigma-invariant (x -> -1/x) members of each
Fast k=1 badness: level-set test.
Track structure of any stack reaching bad >= 4.
"""
import itertools, random

q, n, k, w = 11, 10, 1, 4
D = list(range(1, 11))            # mu_10 = F_11^*
need = n - w                      # 6

def fast_bad_set(u0, u1):
    out = []
    for g in range(q):
        line = [(u0[i] + g * u1[i]) % q for i in range(n)]
        levels = {}
        for i, v in enumerate(line):
            levels.setdefault(v, []).append(i)
        for v, P in levels.items():
            if len(P) >= need:
                if not (all(u0[i] == u0[P[0]] for i in P) and
                        all(u1[i] == u1[P[0]] for i in P)):
                    out.append(g); break
    return out

def poleval(p, x):
    return sum(c * pow(x, i, q) for i, c in enumerate(p)) % q

def polmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % q
    return out

inv = {x: pow(x, q - 2, q) for x in range(1, q)}
sigma = {x: (q - inv[x]) % q for x in D}   # -1/x
idx = {x: i for i, x in enumerate(D)}
# sigma orbits
seen = set(); orbs = []
for x in D:
    if x in seen: continue
    o = [x]; seen.add(x); y = sigma[x]
    while y != x:
        o.append(y); seen.add(y); y = sigma[y]
    orbs.append(tuple(sorted(o)))
print(f"D=mu_10 in F_11; sigma orbits: {orbs}")

# genuine locators: monic deg<=4 nonvanishing on D <=> no roots in F_11^*
# (roots can be 0: l = X^j*... no: 0 not in D so X factors ARE allowed!)
genuine_l = []
for coefs in itertools.product(range(q), repeat=4):
    l = list(coefs) + [1]
    if all(poleval(l, x) for x in D):
        genuine_l.append(l)
print(f"genuine quartic locators: {len(genuine_l)}")

random.seed(23)
def rand_genuine():
    l = random.choice(genuine_l)
    R = [random.randrange(q) for _ in range(w + k)]
    return tuple((poleval(R, x) * pow(poleval(l, x), q - 2, q)) % q for x in D), l, R

def rand_pole(maxspike=w):
    nr = random.randrange(1, maxspike + 1)
    roots = random.sample(D, nr)
    l = [1]
    for r0 in roots:
        l = polmul(l, [(q - r0) % q, 1])
    R = [random.randrange(q) for _ in range(w + k)]
    u = []
    for x in D:
        lx = poleval(l, x)
        u.append(random.randrange(q) if lx == 0 else (poleval(R, x) * pow(lx, q - 2, q)) % q)
    return tuple(u), roots

def make_sig_inv_genuine(tries=20000):
    """sigma-invariant genuine words: search R,l with l sigma-symmetric, R giving
       u(sigma x) = u(x)."""
    out = []
    for _ in range(tries):
        u, l, R = rand_genuine()
        if all(u[idx[x]] == u[idx[sigma[x]]] for x in D):
            out.append(u)
    return out

print("\n--- random sweeps (fast badness) ---")
best = {}
for tag, gen0, gen1, NS in [
    ("G x G", rand_genuine, rand_genuine, 120000),
    ("P x G", rand_pole, rand_genuine, 120000),
    ("P x P", rand_pole, rand_pole, 120000)]:
    mx = 0; arg = None
    for _ in range(NS):
        a = gen0(); b = gen1()
        u0 = a[0]; u1 = b[0]
        bs = fast_bad_set(u0, u1)
        if len(bs) > mx:
            mx = len(bs); arg = (u0, u1, a[1:], b[1:], bs)
    best[tag] = (mx, arg)
    print(f"  {tag}: max bad = {mx} (budget w+3={w+3}, w+1={w+1})")
    if mx >= 3:
        print(f"     u0={arg[0]}\n     u1={arg[1]}\n     meta0={arg[2]} meta1={arg[3]} bad={arg[4]}")

# sigma-invariant targeted
print("\n--- sigma-invariant targeted ---")
siginv = make_sig_inv_genuine()
print(f"  sigma-invariant genuine pool: {len(siginv)}")
mx = 0; arg = None
pool = siginv if len(siginv) >= 2 else []
for _ in range(min(len(pool) ** 2, 60000)):
    u0 = random.choice(pool); u1 = random.choice(pool)
    bs = fast_bad_set(u0, u1)
    if len(bs) > mx:
        mx = len(bs); arg = (u0, u1, bs)
print(f"  sig-inv G x G: max bad = {mx}")
if arg and mx >= 3:
    print(f"     u0={arg[0]}\n     u1={arg[1]} bad={arg[2]}")

# sigma-invariant pole spikes on orbits x sigma-invariant genuine
mx = 0; arg = None
for _ in range(60000):
    # spike on union of sigma-orbits, sigma-invariant values
    chosen = random.sample(orbs, random.randrange(1, 3))
    Z = [x for o in chosen for x in o]
    if len(Z) > w: continue
    u0 = [0] * n
    for o in chosen:
        v = random.randrange(1, q)
        for x in o:
            u0[idx[x]] = v
    u0 = tuple(u0)
    u1 = random.choice(pool) if pool else rand_genuine()[0]
    bs = fast_bad_set(u0, u1)
    if len(bs) > mx:
        mx = len(bs); arg = (u0, u1, bs)
print(f"  sig-spike x sig-genuine: max bad = {mx}")
if arg and mx >= 3:
    print(f"     u0={arg[0]}\n     u1={arg[1]} bad={arg[2]}")

# noisy codewords (within distance w of constants)
print("\n--- noisy x noisy + mixed ---")
def rand_noisy():
    u = [random.randrange(q)] * n
    for i in random.sample(range(n), random.randrange(0, w + 1)):
        u[i] = random.randrange(q)
    return tuple(u)
mx = 0; arg = None
for _ in range(150000):
    u0 = rand_noisy(); u1 = rand_noisy()
    bs = fast_bad_set(u0, u1)
    if len(bs) > mx:
        mx = len(bs); arg = (u0, u1, bs)
print(f"  noisy x noisy: max bad = {mx}")
if arg and mx >= 4:
    print(f"     {arg}")
mx = 0; arg = None
for _ in range(150000):
    u0 = rand_noisy(); u1 = rand_genuine()[0]
    bs = fast_bad_set(u0, u1)
    if len(bs) > mx:
        mx = len(bs); arg = (u0, u1, bs)
print(f"  noisy x genuine: max bad = {mx}")
if arg and mx >= 4:
    print(f"     {arg}")
