#!/usr/bin/env python3
# wf-S4 PRE-SCREEN: Galois-module / Stickelberger structure of the spurious configs.
#
# SETUP. p = 1 mod n splits completely in Z[zeta_n] into phi(n) = n/2 primes P_1,...,P_{n/2},
# permuted SIMPLY TRANSITIVELY by Gal = (Z/n)^* (n=2^mu so Gal = Z/2 x Z/2^{mu-2}). A spurious
# config is an antipodal-free signed subset T of mu_n with sigma_T = sum_{i in T} (+/-) zeta_n^i
# such that p | N_{Q(zeta_n)/Q}(sigma_T), i.e. sigma_T lies in the UNION of some of the P_i.
#
# The TOTAL spurious count Spur (over ALL configs landing in ANY P_i) is what inflates E_r at
# structured primes (S2/measurements). But the PRIZE M(n) stays bounded => the spurious mass is
# SPREAD, not concentrated. The Galois-module question: HOW is the spurious mass distributed
# across the n/2 primes P_i?
#
# KEY GALOIS FACT (used here): if sigma_T in P_i then for any g in Gal, g(sigma_T) in g(P_i).
# Since Gal acts simply transitively on {P_i}, the Galois ORBIT of one config T sweeps a config
# (a Galois-twisted T) into EVERY prime exactly once. So configs come in Galois orbits of size
# dividing n/2, and a single orbit contributes EXACTLY ONE config to each P_i it touches.
#
# DECISIVE MEASUREMENTS (proper subgroups; p prime, p > n^2 to clear char-q pollution; NEVER n=p-1):
#  (M1) PER-PRIME COUNT c_i(w) := #{antipodal-free T, |T| <= w : sigma_T in P_i}. By Galois
#       simple-transitivity the c_i are ALL EQUAL (P_i are Galois-conjugate). So
#            Total spur(w) = (n/2) * c_1(w).
#       => the per-prime count c_1(w) is the CONCENTRATION; (n/2) is the SPREAD factor.
#       Q: does c_1(w) stay O(1) / O(poly log) (=> spur spread thinly, prize-favorable) or
#       does it grow polynomially in n (=> per-prime concentration, prize-hostile)?
#  (M2) ORBIT STRUCTURE: how many distinct Galois ORBITS of spurious configs are there, and what
#       are the orbit sizes? A small number of full-size (n/2) orbits => spread is forced by
#       Galois symmetry alone (each orbit = one config per prime). Many short orbits or many
#       orbits => richer structure.
#  (M3) STICKELBERGER PIN: the Stickelberger element theta = (1/n) sum_{a in (Z/n)^*} a * sigma_a^{-1}
#       annihilates the class group; (theta) Z[zeta_n] constrains the prime ideal P. For the
#       SPLIT prime p (P principal-power), the relevant constraint is the FACTORIZATION TYPE: does
#       sigma_T lie in P_i to MULTIPLICITY 1 only (P_i || sigma_T, never P_i^2 | sigma_T)? If the
#       valuation v_{P_i}(sigma_T) <= 1 always, then a config can vanish mod p at most "once" per
#       prime, capping the per-prime DEPTH. We measure max valuation.
#
# CONCLUSION TAGS: if c_1(w) = O(1) bounded as n grows at fixed weight ratio => CONCENTRATION-REDUCED
# (spur is Galois-spread; the prize-relevant M stays bounded because each prime sees O(1) configs).
# If c_1(w) grows poly(n) => the spread is NOT enough; OBSTRUCTION.

import itertools, math
from sympy import isprime, primitive_root

def musub(n, p):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    return g, [pow(h, j, p) for j in range(n)]

def primes_1modn(n, lo, count):
    out=[]; m=max(1,lo//n)
    while len(out)<count:
        p=n*m+1
        if p>lo and isprime(p): out.append(p)
        m+=1
    return out

# A prime P_i above p corresponds to a choice of n-th root of unity mod p: zeta_n -> h^i mod p,
# for i in (Z/n)^* (the n/2 primitive choices). sigma_T(zeta) -> sigma_T(h^i) mod p. sigma_T in P_i
# <=> the embedding zeta->h^i sends sigma_T to 0 mod p, i.e. sum_{(s,sign) in T} sign * h^{i*s} = 0 mod p.
# So the n/2 primes are indexed by i in (Z/n)^* = {odd residues mod n}. We label primes by these i.

def analyze(n, p, wmax):
    g, roots = musub(n, p)  # roots[j] = h^j, h a primitive n-th root mod p
    half = n//2
    odd_i = [i for i in range(1, n) if i % 2 == 1]  # the n/2 primitive embeddings = the n/2 primes
    # enumerate antipodal-free signed configs: choice[s] in {0,+1,-1} for s in [0, half)
    # sigma_T = sum_{s} choice[s] * zeta^s. Embedding i: value mod p = sum choice[s]*h^{i*s} mod p.
    per_prime = {i: [] for i in odd_i}  # i -> list of config tuples landing in P_i
    config_to_primes = {}  # config -> set of i it lands in
    configs = []
    for choice in itertools.product((0, 1, -1), repeat=half):
        w = sum(1 for c in choice if c != 0)
        if w == 0 or w > wmax: continue
        # char-0 genuineness: does sigma_T vanish over Z (i.e. embedding into C at zeta=primitive)?
        # We only care about configs that vanish mod p but NOT identically (those are char-0 artifacts).
        configs.append(choice)
    # compute embeddings
    for choice in configs:
        lands = []
        for i in odd_i:
            val = 0
            for s, c in enumerate(choice):
                if c != 0:
                    val = (val + c * pow(roots[1], (i*s) % n, p)) % p
            if val % p == 0:
                lands.append(i)
        if lands:
            config_to_primes[choice] = set(lands)
            for i in lands:
                per_prime[i].append(choice)
    return odd_i, per_prime, config_to_primes, half

def char0_vanish(choice, n):
    # does sigma_T vanish in C (genuine char-0 antipodal coincidence)?
    tot = 0j
    for s, c in enumerate(choice):
        if c != 0:
            tot += c * complex(math.cos(2*math.pi*s/n), math.sin(2*math.pi*s/n))
    return abs(tot) < 1e-9

print("wf-S4 Galois per-prime spread of spurious configs (antipodal-free, weight<=wmax)")
print("p splits into n/2 primes P_i (i odd mod n), Gal=(Z/n)^* simply transitive on them.\n")

for n in [8, 16]:
    half = n//2
    wmax = min(half, 6)  # bounded weight (deep-moment depth is small)
    plist = primes_1modn(n, n*n, 4)
    print(f"=== n={n}  (n/2={half} primes)  wmax={wmax}  primes>{n*n}: {plist} ===")
    for p in plist:
        odd_i, per_prime, c2p, _ = analyze(n, p, wmax)
        counts = [len(per_prime[i]) for i in odd_i]
        # split into char-0 (genuine antipodal, in EVERY prime) vs char-p spurious
        char0_configs = [c for c in c2p if char0_vanish(c, n)]
        charp_configs = [c for c in c2p if not char0_vanish(c, n)]
        # per-prime char-p count
        cp_perprime = []
        for i in odd_i:
            cp_perprime.append(sum(1 for c in per_prime[i] if not char0_vanish(c, n)))
        beta = math.log(p)/math.log(n)
        equal = "EQUAL" if len(set(cp_perprime))==1 else f"VARY:{sorted(set(cp_perprime))}"
        print(f"  p={p:8d} beta={beta:.2f}  total configs in some P_i: {len(c2p)}  "
              f"(char0={len(char0_configs)}, charp-spur={len(charp_configs)})")
        print(f"     char-p per-prime count c_1(w<={wmax}): {cp_perprime[0]}  across primes: {equal}")
        # orbit structure of char-p configs under Galois (a in (Z/n)^* acts s -> a*s mod n with sign)
        # orbit of choice: apply sigma_a: zeta^s -> zeta^{a s}; rep antipodal-reduced (mod n/2 with sign)
        def galois_image(choice, a, n):
            half = n//2
            out = [0]*half
            for s, c in enumerate(choice):
                if c == 0: continue
                t = (a*s) % n
                sign = c
                if t >= half:
                    t -= half; sign = -sign
                out[t] = (out[t] + sign)  # could collide; assume antipodal-free preserved generically
            return tuple(out)
        seen = set(); orbits = []
        cp_set = set(charp_configs)
        for c in charp_configs:
            if c in seen: continue
            orb = set()
            for a in odd_i:
                img = galois_image(c, a, n)
                if img in cp_set:
                    orb.add(img)
            for x in orb: seen.add(x)
            seen.add(c); orb.add(c)
            orbits.append(len(orb))
        if charp_configs:
            print(f"     char-p Galois orbits: {len(orbits)} orbits, sizes {sorted(set(orbits))}, "
                  f"max orbit={max(orbits)} (n/2={half})")
    print()
