# Drill into the trinomial cyclotomic-cap VIOLATIONS: print explicit witnesses where
# inc > gcd(i-j,j-k,n) and inc > gcd(i-k,n), to extract the constraint-lemma mechanism.
# Also test the TRUE in-tree cap (the bare degree i-k) holds, and whether inc | n.
import itertools, math
from sympy import isprime

def mu_gen(p, n):
    if (p - 1) % n != 0:
        return None
    def order(a):
        o = 1; x = a % p
        while x != 1:
            x = (x * a) % p; o += 1
        return o
    for g in range(2, p):
        if order(g) == p - 1:
            return pow(g, (p - 1) // n, p)
    return None

def mu_n(p, n):
    h = mu_gen(p, n)
    if h is None:
        return None
    s = []; x = 1
    for _ in range(n):
        s.append(x); x = (x * h) % p
    return sorted(set(s))

viol = []
deg_viol = 0       # violations of the proven bare-degree cap inc <= i-k  (should be 0)
divn_viol = 0      # violations of inc | n
for n in [4, 8, 16]:
    cands = [p for p in range(n + 1, 20000)
             if isprime(p) and (p - 1) % n == 0 and (p - 1) // n >= 2]
    picks = cands[:3]
    big = [p for p in cands if p > n ** 3]
    if big:
        picks.append(big[0])
    if n == 16 and 65537 in cands:
        picks.append(65537)
    if n in (4, 8) and 257 in cands:
        picks.append(257)
    for p in picks:
        S = mu_n(p, n)
        if S is None:
            continue
        for k, j, i in itertools.combinations(range(0, min(n + 2, 9)), 3):
            for c1 in S[:4]:
                for c2 in S[:4]:
                    roots = [x for x in S if x != 0 and
                             (pow(x, i, p) - c1 * pow(x, j, p) - c2 * pow(x, k, p)) % p == 0]
                    inc = len(roots)
                    if inc == 0:
                        continue
                    gA = math.gcd(math.gcd(i - j, j - k), n)
                    if inc > (i - k):
                        deg_viol += 1
                    if n % inc != 0:
                        divn_viol += 1
                    if inc > gA and len(viol) < 12:
                        viol.append((n, p, i, j, k, c1, c2, inc, gA, i - k))

print("bare-degree-cap (inc <= i-k) violations [proven, must be 0]:", deg_viol)
print("inc-divides-n violations:", divn_viol)
print("sample cyclotomic-cap violations (n,p,i,j,k,c1,c2 | inc, gcd(i-j,j-k,n), i-k):")
for v in viol:
    n,p,i,j,k,c1,c2,inc,gA,ik = v
    print(f"  n={n} p={p} (i,j,k)=({i},{j},{k}) c1={c1} c2={c2} | inc={inc} gcdcap={gA} degcap={ik}")
