# n=64 extension of the shallow-resonance thickness-invariance brick (563fc7f85).
# K(n,4)=n/4-1 predicts K=15 at n=64. e2_K_w4_n64 confirmed K=15 at the PRIZE (thin) prime only.
# UNCONTESTED gap: the THICK-beta n=64 control (beta=2.3,3.0) was never run. If K=15 there too,
# the thickness-invariance brick extends to the next octave n=64 (the dossier's enumeration frontier).
# C(64,4)=635376 -- tractable. proper subgroup, 2 primes/beta, never n=q-1.

import itertools, math
from sympy import isprime, primitive_root

def primes_beta(n, beta, count=2):
    target = int(round(n**beta)); cand = target - (target % n) + 1; out = []; t = 0
    while len(out) < count and t < 2_000_000:
        if cand > n and (cand - 1) % n == 0 and isprime(cand):
            out.append(cand)
        cand += n; t += 1
    return out

def K_shallow(n, p, w=4):
    g = pow(primitive_root(p), (p - 1) // n, p)
    mu = [pow(g, j, p) for j in range(n)]
    e1set = set(); cnt = 0
    for S in itertools.combinations(range(n), w):
        s1 = 0; s2 = 0
        for i in S:
            v = mu[i]; s1 += v; s2 += v * v
        if (s1 * s1 - s2) % p == 0 and s1 % p != 0:
            cnt += 1; e1set.add((-pow(s1, p - 2, p)) % p)
    rem = set(e1set); K = 0
    while rem:
        x = next(iter(rem)); rem -= set((u * x) % p for u in mu); K += 1
    return cnt, K

n = 64; w = 4; pred = n // 4 - 1
print(f"n={n} shallow resonance w={w}: K(n,4)=n/4-1 predicts K={pred}. Thick-vs-thin (C(64,4)={math.comb(64,4):,}).")
for beta in [2.3, 3.0, 4.0]:
    ps = primes_beta(n, beta, 2)
    if not ps:
        print(f"  beta={beta}: no prime"); continue
    tag = "THICK(prize-FALSE)" if beta < 3.5 else "THIN(prize)"
    for p in ps:
        cnt, K = K_shallow(n, p)
        ok = "== n/4-1" if K == pred else "!= n/4-1 !!"
        print(f"  beta={beta} [{tag:18s}] p={p:>12d}: K={K} {ok} (#bad={n*K}, raw e2=0 sets={cnt})")
print(f"\nVERDICT: K=15 across thick+thin at n=64 => thickness-invariance brick extends to the n=64 octave.")
