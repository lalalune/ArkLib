# Finer rule-3 on the shallow e2=0 resonance: the COUNT K(n,4)=n/4-1 is thickness-invariant (push 563fc7f85).
# But does the STRUCTURE of the n/4-1 orbit representatives differ thin-vs-thick? Two same-count families can
# still differ in WHICH e1-values appear (their multiplicative-order / coset structure). If the e1-orbit
# representatives have a thin-only algebraic signature (e.g. all of a special multiplicative order, or all in
# a sub-coset), the resonance could still hide a thin lever despite equal count. If the orbit STRUCTURE is
# also thickness-invariant (same relative pattern), the rule-3 FAIL is total (count AND structure thin-blind).
#
# Object per (n,beta,p): the e2=0, e1!=0, width-4 subsets => their e1-values e1 = -(sum)^{-1}... actually
# alpha = -1/e1(S); we track the dilation-orbit reps of e1(S) and characterize them by:
#   (i) multiplicative order of e1-rep in F_p^*  (mod the n-subgroup ambiguity -> order of e1^n, the coset index)
#   (ii) whether the rep lies IN mu_n (the subgroup itself) or a nontrivial coset
#   (iii) the partition of the n/4-1 orbits by coset-index of e1
# All are dilation-invariant (mu_n acts; coset index of e1 is well-defined mod the subgroup).
# Compare the PATTERN across thick beta=2.3,3.0 and thin beta=4,5. proper subgroup, multi-prime, never n=q-1.

import itertools, math
from sympy import isprime, primitive_root, n_order

def primes_beta(n, beta, count=2):
    target = int(round(n**beta)); cand = target - (target % n) + 1; out = []
    t = 0
    while len(out) < count and t < 400000:
        if cand > n and (cand - 1) % n == 0 and isprime(cand):
            out.append(cand)
        cand += n; t += 1
    return out

def resonance_structure(n, p, w=4):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)          # generator of mu_n
    mu = [pow(h, j, p) for j in range(n)]
    muset = set(mu)
    e1set = set()
    for S in itertools.combinations(range(n), w):
        s1 = 0; s2 = 0
        for i in S:
            v = mu[i]; s1 += v; s2 += v * v
        if (s1 * s1 - s2) % p == 0 and s1 % p != 0:
            e1set.add(s1 % p)
    # dilation-orbit reps under mu_n
    rem = set(e1set); reps = []
    while rem:
        x = next(iter(rem)); rem -= set((u * x) % p for u in mu); reps.append(x)
    # characterize each rep:
    #  - in_subgroup: is e1-rep itself in mu_n?
    #  - coset_order: multiplicative order of (rep^n) = order in the quotient F_p^*/mu_n (size m=(p-1)/n)
    in_sub = sum(1 for x in reps if x in muset)
    m = (p - 1) // n
    coset_orders = []
    for x in reps:
        xn = pow(x, n, p)               # lands in the subgroup of m-th... actually order divides m
        coset_orders.append(n_order(xn, p) if xn != 1 else 1)
    # normalize coset-orders as fractions of m (the quotient size) -> thickness-comparable
    co_norm = sorted(set(round(o / m, 4) for o in coset_orders))
    return len(reps), in_sub, sorted(set(coset_orders)), co_norm, m

print("FINER rule-3: structure of the n/4-1 resonance orbit reps thin-vs-thick (count already = n/4-1, beta-flat).")
print("Track: #reps, #reps IN mu_n, multiplicative orders of e1-rep^n (coset/quotient orders), normalized by m=(p-1)/n.\n")
for n in [16, 32]:
    pred = n // 4 - 1
    print(f"=== n={n}  (n/4-1={pred}) ===")
    for beta in [2.3, 3.0, 4.0, 5.0]:
        if math.comb(n, 4) > 30_000_000:
            print(f"  beta={beta}: too big"); continue
        ps = primes_beta(n, beta, 2)
        if not ps:
            print(f"  beta={beta}: no prime"); continue
        tag = "THICK" if beta < 3.5 else "THIN "
        for p in ps:
            K, in_sub, corders, co_norm, m = resonance_structure(n, p)
            print(f"  beta={beta} [{tag}] p={p:>9d} m={m:>7d}: K={K} in_mu_n={in_sub} "
                  f"coset_orders={corders} (norm/m={co_norm})")
    print()
print("READ: if #reps-in-mu_n and the normalized coset-order PATTERN are the SAME across thick+thin")
print("=> structure thickness-invariant too => rule-3 FAIL is TOTAL (count AND structure thin-blind).")
print("If a thin-only signature appears (e.g. reps in-subgroup only at thin beta) => a residual thin signal.")
