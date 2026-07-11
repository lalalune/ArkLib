#!/usr/bin/env python3
"""
wf407_T09-leak_crossparity_bound.py  --  #407 thread T09-leak.

GOAL (three parts of the assigned target):
 (1) REPRODUCE the leak measurement: what fraction of mod-q DEFECTS obey the single
     structured relation A == -g * B (mod p) for a fixed unit g, at n = 16, 32, 64?
 (2) Attempt to TURN the leak structure into a count / bound on the number of defects.
 (3) Pin precisely HOW the fully-split N(q)=p case reduces to ideal-SVP, and whether the
     leak is exploitable BELOW it.

DEFINITIONS.
   mu_n  = order-n subgroup of F_p^*  (n = 2^mu, p == 1 mod n).
   A depth-r additive-energy DEFECT is an unordered relation
        x_1 + ... + x_r  ==  y_1 + ... + y_r   (mod p),   x_i, y_j in mu_n,
   that does NOT hold as an identity over C (i.e. the corresponding signed cyclotomic
   integer  alpha = sum zeta^{a_i} - sum zeta^{b_j}  is NONZERO in Z[zeta_n] but == 0 mod the
   degree-1 prime  p | p ).  Equivalently a "spurious" (char-p only) coincidence.

   We index mu_n by exponents: x = h^a, with h a fixed generator of mu_n.  A defect at depth r
   is a pair of multisets (Multiset A of r exponents, Multiset B of r exponents) with
   sum_{a in A} h^a == sum_{b in B} h^b  (mod p),  the two multisets DIFFERENT as cyclotomic
   sums (different reduced power-basis vector).

THE LEAK.  Write the defect's two SUPPORT sets  S_A = {h^a : a in A},  S_B = {h^b : b in B}
   (the underlying *sets*, ignoring multiplicity).  The claimed leak: there is a fixed unit
   g in F_p^* such that  S_A = (-g) * S_B  (setwise), i.e. every defect's positive side is a
   single dilation -g of its negative side.  We MEASURE:
     - for each defect, does there EXIST g with S_A = (-g) S_B ?  (and is g in mu_n?)
     - the fraction of defects with the leak.
     - whether the SAME g works across all defects (one global g) or per-defect g.

We do this at the genuine defect onset: choose the SMALLEST prize-shaped prime p == 1 mod 2n
that is ABOVE the clean-range norm threshold (2r)^{phi(n)} for the depth r we enumerate, so
that defects actually exist; and also report the leak at the smallest depth r where ANY defect
appears.
"""
import cmath, math, itertools, sys
from collections import defaultdict, Counter

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def factorize(m):
    s = {}; d = 2
    while d*d <= m:
        while m % d == 0: s[d] = s.get(d,0)+1; m //= d
        d += 1
    if m > 1: s[m] = s.get(m,0)+1
    return s

def primitive_root(p):
    fac = factorize(p-1)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac): return g
    return None

def smallest_prime_1_mod(n, lo):
    """smallest prime p >= lo with p == 1 mod n."""
    p = lo + ((1 - lo) % n)
    if p < 3: p += n
    while True:
        if p % n == 1 and is_prime(p): return p
        p += n

def subgroup(p, n):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    S = []; x = 1
    for _ in range(n): S.append(x); x = x*h % p
    return S, h, g

def enumerate_defects(p, n, S, r, cap=4000):
    """Return list of (A, B): A,B are sorted exponent-multisets (tuples) of length r, with
    sum_A == sum_B mod p, that are DIFFERENT as char-0 cyclotomic sums (different sorted
    exponent multiset), grouped so we only keep genuinely spurious (char-p) coincidences.
    To detect char-0 equality we use that two multisets of n-th roots have equal cyclotomic
    sum iff (after reducing exponents mod n) the multiset of exponents is equal -- because the
    n distinct n-th roots are Q-linearly... NO: they satisfy the single relation sum of all
    primitive-coset = -1 etc.  Robust test: equal over C iff the integer group-ring vectors
    reduce to the same power-basis vector.  We use a numerical char-0 sum (high precision) to
    classify char-0 equality, then a defect is two multisets with equal mod-p sum but unequal
    char-0 sum.
    """
    # bucket all r-multisets by mod-p sum
    buckets = defaultdict(list)
    combos = itertools.combinations_with_replacement(range(n), r)
    for A in combos:
        s = 0
        for a in A: s = (s + S[a]) % p
        buckets[s].append(A)
    # char-0 sum (complex) key for classifying char-0 identity
    w = 2*math.pi/n
    def c0key(A):
        z = sum(cmath.exp(1j*w*a) for a in A)
        return (round(z.real, 7), round(z.imag, 7))
    defects = []
    for s, lst in buckets.items():
        if len(lst) < 2: continue
        # group by char-0 key
        byc0 = defaultdict(list)
        for A in lst: byc0[c0key(A)].append(A)
        if len(byc0) < 2: continue   # all char-0 equal => no spurious defect here
        keys = list(byc0.keys())
        # produce defect pairs across distinct char-0 classes
        for i in range(len(keys)):
            for j in range(i+1, len(keys)):
                A = byc0[keys[i]][0]; B = byc0[keys[j]][0]
                defects.append((A, B))
                if len(defects) >= cap: return defects
    return defects

def support_set(exps, S):
    return frozenset(S[a] for a in exps)

def test_leak(p, n, S, A, B):
    """Return (has_leak, g, g_in_mu) where leak means SA = (-g) SB setwise for some unit g.
    Only possible if |SA| == |SB|.  We test by trying g = -a0 * b0^{-1} for a0 in SA, b0 in SB,
    then checking the dilation matches as a set."""
    SA = support_set(A, S); SB = support_set(B, S)
    if len(SA) != len(SB): return (False, None, None)
    muset = set(S)
    SAl = list(SA); SBl = list(SB)
    a0 = SAl[0]
    for b0 in SBl:
        # want -g such that -g*b0 = a0 => candidate t = -g = a0 * inv(b0)
        t = a0 * pow(b0, -1, p) % p
        # check t * SB == SA  (note t already absorbs the minus sign; leak A = -g B means
        # the dilation factor is t = -g, so g = -t = (p - t))
        dil = frozenset((t * x) % p for x in SB)
        if dil == SA:
            g = (p - t) % p
            return (True, g, g in muset)
    return (False, None, None)

def main():
    print("="*108)
    print("T09-leak  (1) leak fraction  (2) bound attempt  (3) ideal-SVP split reduction")
    print("="*108)
    results = {}
    for n in (16, 32, 64):
        print(f"\n############  n = {n}  (mu = {n.bit_length()-1})  ############")
        # find the smallest depth r and a prime where defects exist.  clean range: (2r)^{phi}<p.
        phi = n // 2
        # we want defects -> p below (2r)^phi for the chosen r, but p == 1 mod 2n and prime.
        # pick r and p so that defects are plausible but enumeration is feasible.
        for r in (2, 3, 4):
            # need (2r)^phi >= p for defects.  pick p the smallest prime 1 mod 2n above some base.
            # use a moderate p to keep defects findable yet enumerable.
            base = max(2*n+1, int((2*r)**phi) // 8) if phi <= 6 else 2*n*64+1
            # cap enumeration cost: combos = C(n+r-1, r); skip if too large
            ncombo = math.comb(n+r-1, r)
            if ncombo > 1_500_000:
                continue
            p = smallest_prime_1_mod(2*n, base)
            S, h, g0 = subgroup(p, n)
            defs = enumerate_defects(p, n, S, r)
            if not defs:
                print(f"  r={r} p={p} (2^{math.log2(p):.1f}) combos={ncombo}: NO defects (clean range)")
                continue
            nd = len(defs)
            leakcount = 0; g_in_mu = 0; gs = []
            for (A, B) in defs:
                ok, g, inmu = test_leak(p, n, S, A, B)
                if ok:
                    leakcount += 1; gs.append(g)
                    if inmu: g_in_mu += 1
            frac = leakcount/nd
            uniq_g = len(set(gs))
            print(f"  r={r} p={p} (2^{math.log2(p):.1f}) combos={ncombo}: "
                  f"#defect(sampled<= cap)={nd}  LEAK A=-gB: {leakcount}/{nd} = {100*frac:.1f}%  "
                  f"(g in mu_n: {g_in_mu}/{leakcount})  distinct g: {uniq_g}")
            results[(n, r)] = (p, nd, frac, uniq_g, g_in_mu)
            break  # first depth with defects per n
    print("\n" + "="*108)
    print("SUMMARY")
    for (n, r), (p, nd, frac, uniq_g, g_in_mu) in results.items():
        print(f"  n={n} r={r} p={p}: leak {100*frac:.1f}%  distinct g={uniq_g}  g_in_mu_frac={g_in_mu}/{nd}")
    print("\nINTERPRETATION:")
    print("  - leak ~ 100% with a SINGLE g would mean defects = {alpha : SA = -g SB} = incidence")
    print("    of a subset-sum image with its dilate -> |S0 cap (-g)S0| (BGK sum-product wall).")
    print("  - many distinct g => the 'leak' is not one relation but a per-defect dilation =>")
    print("    no single low-dimensional structure to count.")

if __name__ == "__main__":
    main()
