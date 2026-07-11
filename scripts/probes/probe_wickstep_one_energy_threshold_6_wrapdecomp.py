import math

def order(a, p):
    o = 1; cur = a % p
    while cur != 1:
        cur = (cur * a) % p; o += 1
    return o

def gen_of(p):
    for a in range(2, p):
        if order(a, p) == p - 1:
            return a
    return None

def subgroup(p, n, gen):
    h = pow(gen, (p - 1) // n, p)
    sub = []; cur = 1
    for _ in range(n):
        sub.append(cur); cur = (cur * h) % p
    return sub

def additive_energy(p, sub):
    # E_2 = #{(a,b,c,d) in sub^4 : a+b = c+d mod p}
    from collections import Counter
    cnt = Counter()
    for a in sub:
        for b in sub:
            cnt[(a + b) % p] += 1
    return sum(v * v for v in cnt.values())

def additive_energy_no_wrap(p, sub):
    # same but using INTEGER sums (no mod p) -- the char-0 / "no wraparound" count
    from collections import Counter
    cnt = Counter()
    for a in sub:
        for b in sub:
            cnt[a + b] += 1   # integer, no mod
    return sum(v * v for v in cnt.values())

p = 40961
g = gen_of(p)
print("E_2 = additive energy of mu_n in Z_p.  closed form (char-0, p>2^n): 3n^2-3n")
for n in [8, 16, 32, 64, 128, 256, 512]:
    if (p-1) % n: continue
    sub = subgroup(p, n, g)
    E2mod = additive_energy(p, sub)
    E2int = additive_energy_no_wrap(p, sub)
    cf = 3*n*n - 3*n
    print("  n=%4d  E2(modp)=%8d  E2(noWrap/char0)=%8d  3n^2-3n=%8d  wrap_excess=%6d  char0_matches=%s"
          % (n, E2mod, E2int, cf, E2mod - E2int, E2int == cf))
