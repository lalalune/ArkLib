# O145: classification at two more instances.
# Instance A: n=16, m=4, r=3: stack (X^12, X^8), k=5; band e1=e2=e3=e5=e6=e7=0 over
#   12-subsets of mu_16 (C(16,12)=1820). Fiber unions: 3 of 4 quartic fibers (4 expected).
# Instance B: n=32, m=2, r=4: stack (X^8, X^6), k=5; band e1=e3=0 over 8-subsets of mu_32
#   (C(32,8)=10.5M). Fiber unions: C(16,4)=1820 expected.
from itertools import combinations
def subgroup_gen(p, n):
    for g in range(2, p):
        x, elems = 1, set()
        for _ in range(p-1):
            x = x*g % p; elems.add(x)
        if len(elems) == p-1:
            return pow(g, (p-1)//n, p)
def esymms(elems, mmax, p):
    pws = [sum(pow(a, j, p) for a in elems) % p for j in range(1, mmax+1)]
    e = [1]
    for j in range(1, mmax+1):
        s = 0
        for i in range(1, j+1):
            s += (-1)**(i-1) * e[j-i] * pws[i-1]
        e.append(s * pow(j, p-2, p) % p)
    return e[1:]
# Instance A
print("Instance A: n=16, (X^12, X^8), k=5", flush=True)
solsA = {}
for p in (97, 113, 193, 257):
    gen = subgroup_gen(p, 16)
    H = [pow(gen, i, p) for i in range(16)]
    S = set()
    for idx in combinations(range(16), 12):
        elems = [H[i] for i in idx]
        e = esymms(elems, 7, p)
        if e[0] == 0 and e[1] == 0 and e[2] == 0 and e[4] == 0 and e[5] == 0 and e[6] == 0:
            S.add(idx)
    solsA[p] = S
    print(f"  p={p}: solutions = {len(S)}", flush=True)
common = set.intersection(*solsA.values())
# quartic fibers: x -> x^4 maps gen^i to gen^(4i); fiber over gen^(4j) = {i : i = j mod 4}
fibersA = set()
for T in combinations(range(4), 3):
    fibersA.add(tuple(sorted([j + 4*l for j in T for l in range(4)])))
print(f"  common = {len(common)}; fiber unions = {len(fibersA)}; equal: {common == fibersA}", flush=True)
# Instance B
print("Instance B: n=32, (X^8, X^6), k=5", flush=True)
for p in (193, 257):
    gen = subgroup_gen(p, 32)
    H = [pow(gen, i, p) for i in range(32)]
    cnt = 0
    fib = 0
    sols = set()
    for idx in combinations(range(32), 8):
        s1 = 0
        for i in idx: s1 += H[i]
        if s1 % p: continue
        s3 = sum(pow(H[i], 3, p) for i in idx) % p
        if s3 == 0:
            sols.add(idx)
    fibersB = set()
    for T in combinations(range(16), 4):
        fibersB.add(tuple(sorted([i for i in T] + [i+16 for i in T])))
    print(f"  p={p}: solutions = {len(sols)}; fiber unions = {len(fibersB)};"
          f" fibers⊆sols: {fibersB <= sols}; equal: {sols == fibersB}", flush=True)
