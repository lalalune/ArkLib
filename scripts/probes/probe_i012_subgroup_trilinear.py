#!/usr/bin/env python3
"""
probe_i012_subgroup_trilinear.py   (IDEA I012, effective-sumproduct family, issue #444)

CLAIM UNDER TEST (I012)
-----------------------
"Subgroup-trilinear": replace the p^{1/4} in the Petridis-Shparlinski trilinear bound
(di Benedetto Lemma 4.1)
    | sum_{x in X, y in Y, z in Z} a_x b_y c_z e_p(axyz) |  <<  p^{1/4} |X|^{3/4}|Y|^{3/4}|Z|^{7/8}
by an in-regime n^c (c<1/4), by exploiting that for X=Y=Z=mu_n the collinear / coplanar
triples of the underlying point-plane (Rudnev) incidence are Beukers-Smyth cyclotomic
torsion-coset points (Theta(n)), not the generic Theta(n^2).

This would make di Benedetto's exponent (currently nontrivial only for H >= p^{1/4})
nontrivial INSIDE n < p^{1/4} (the prize regime), the first power-saving below p^{1/4}.

WHAT THIS PROBE MEASURES (all over PROPER mu_n: n=2^mu, n | p-1, p PRIME, p >> n^3,
                          m=(p-1)/n >> 1, NEVER n=p-1):

 (T1) THE DIRECT TRILINEAR SUM over the subgroup itself, X=Y=Z=mu_n:
        T(a) = sum_{x,y,z in mu_n} e_p(a x y z).
      Since mu_n is multiplicatively closed, xyz ranges over mu_n with multiplicity =
      #{(x,y,z): xyz = w} = n^2 (constant) for each w in mu_n. So
        T(a) = n^2 * sum_{w in mu_n} e_p(a w) = n^2 * eta_a,   |T| = n^2 * |eta_a|.
      => the "trilinear sum over the subgroup" is EXACTLY n^2 times the object we are
      trying to bound. Verify this identity, and compare |T| to the I012-claimed bound
      n^{2+1/4-eta} and to the di-Benedetto Lemma-4.1 bound p^{1/4} n^{19/8}.
      KEY CONSEQUENCE: bounding T(a)<=n^{2+1/4-eta} is LITERALLY equivalent to bounding
      |eta_a| <= n^{1/4-eta} -- i.e. it ASSUMES square-root-or-better cancellation, the
      very thing we want. Circular for the subgroup itself.

 (T2) THE COLLINEAR-TRIPLE / PRODUCT-ENERGY count that drives the Rudnev point-plane
      input -- the actual content the p^{1/4} encodes. For the trilinear form the
      relevant incidence is the multiplicative energy of the product map:
        E_prod(X,Y,Z) = #{(x1,y1,z1,x2,y2,z2) in (XxYxZ)^2 : x1 y1 z1 = x2 y2 z2}.
      Measure E_prod for X=Y=Z=mu_n (the I012 case) and compare to:
        - generic Cartesian-cube energy ~ |X||Y||Z| (here n^3, the diagonal lower bound)
        - the count for X,Y,Z = ADDITIVE sumsets/diff-sets of subgroup fibers (what
          di Benedetto ACTUALLY feeds to Lemma 4.1 -- NOT sub-tori).
      The I012 premise is that the subgroup case has Theta(n) "bad" structure; test it.

 (T3) THE PREMISE CHECK: in di Benedetto's proof of Thm 3.1 the sets fed to Lemma 4.1 are
        X = {x1+x2+x3}, Y = {y1+y2+y3}, Z = {z1-z2}   (ADDITIVE combinations of fibers).
      These are NOT multiplicative sub-tori. Measure how torus-like they are: fraction of
      X that lies in mu_n (a torsion coset) vs. spread over F_p. If X,Y,Z are generic
      (spread), the Beukers-Smyth torsion-coset improvement CANNOT apply -- the I012
      premise is factually wrong about the operative sets.

HONEST TAGS: [PROVEN] exact identity / [MEASURED] exact finite-field count.
"""
import sympy
import itertools
import math
import cmath
import json

def find_prime(n):
    """p prime, n | p-1, p ~ n^4 (p>>n^3), m=(p-1)/n != 1 (never n=p-1)."""
    m = n**3  # so p ~ n^4
    while True:
        m += 1
        p = m * n + 1
        if sympy.isprime(p) and p > n**3 and m != 1:
            return p

def subgroup(p, n):
    """The 2-power multiplicative subgroup mu_n of F_p* (n=2^mu, n|p-1)."""
    g = sympy.primitive_root(p)
    m = (p - 1) // n
    h = pow(g, m, p)           # generator of mu_n
    return [pow(h, j, p) for j in range(n)]

def eta(p, mun, a):
    """eta_a = sum_{x in mu_n} e_p(a x)."""
    s = 0j
    for x in mun:
        s += cmath.exp(2j * math.pi * (a * x % p) / p)
    return s

def max_eta(p, mun):
    """M(mu_n) = max_{a != 0} |eta_a|."""
    best = 0.0
    barg = None
    for a in range(1, p):
        v = abs(eta(p, mun, a))
        if v > best:
            best = v; barg = a
    return best, barg

def trilinear_sum_subgroup(p, mun, a):
    """T(a) = sum_{x,y,z in mu_n} e_p(a x y z), direct triple loop (small n only)."""
    s = 0j
    for x in mun:
        for y in mun:
            axy = (a * x * y) % p
            for z in mun:
                s += cmath.exp(2j * math.pi * (axy * z % p) / p)
    return s

def product_energy(p, X, Y, Z):
    """E_prod = #{x1y1z1 = x2y2z2}: count via histogram of products mod p."""
    from collections import Counter
    c = Counter()
    for x in X:
        for y in Y:
            xy = (x * y) % p
            for z in Z:
                c[(xy * z) % p] += 1
    return sum(v * v for v in c.values())

def main():
    out = {"probe": "i012_subgroup_trilinear", "regime": "proper mu_n, n=2^mu, n|p-1, p prime, p>>n^3, m=(p-1)/n!=1", "cases": []}

    # ---- T1: exact identity |T_subgroup| = n^2 |eta|, and the circularity it exposes ----
    print("="*78)
    print("T1: direct trilinear sum over the subgroup itself  T(a)=sum_{x,y,z in mu_n} e_p(axyz)")
    print("    identity:  T(a) = n^2 * eta_a   (mu_n multiplicatively closed)")
    print("="*78)
    for mu in [3, 4, 5]:
        n = 2**mu
        p = find_prime(n)
        mun = subgroup(p, n)
        M, aM = max_eta(p, mun)
        # verify identity at the maximizing frequency a=aM and at a couple others
        ids = []
        for a in [aM, 1, 3]:
            T = trilinear_sum_subgroup(p, mun, a)
            n2eta = (n * n) * eta(p, mun, a)
            err = abs(T - n2eta)
            ids.append((a, abs(T), abs(n2eta), err))
        identity_ok = all(e < 1e-6 for (_, _, _, e) in ids)
        # bounds at the maximizer
        Tmax = (n * n) * M
        lemma41 = (p**0.25) * (n**(0.75 + 0.75 + 0.875))   # p^{1/4} n^{19/8}
        i012_claim = n**(2 + 0.25)                          # n^{2+1/4} (eta=0 boundary of claim)
        floor = n**2 * math.sqrt(n * math.log(p / n))       # n^2 * sqrt(n log(p/n))
        rec = {
            "n": n, "p": p, "beta": math.log(p) / math.log(n),
            "M_eta_max": M, "a_max": aM,
            "identity_T_eq_n2_eta_OK": identity_ok,
            "identity_samples": [{"a": a, "|T|": tt, "|n2eta|": nn, "err": ee} for (a, tt, nn, ee) in ids],
            "|T|_max = n2*M": Tmax,
            "lemma41_bound p^1/4 n^19/8": lemma41,
            "i012_claim_bound n^(2+1/4)": i012_claim,
            "floor n2*sqrt(n log(p/n))": floor,
            "M/sqrt(n)": M / math.sqrt(n),
            "M/sqrt(n log(p/n))": M / math.sqrt(n * math.log(p / n)),
        }
        out["cases"].append({"T1": rec})
        print(f"  n={n} p={p} beta={rec['beta']:.3f}")
        print(f"    identity T(a)=n^2 eta_a verified: {identity_ok}  (samples a in {{aM,1,3}})")
        print(f"    M=max|eta|={M:.3f}  M/sqrt(n)={M/math.sqrt(n):.3f}  M/sqrt(n log(p/n))={rec['M/sqrt(n log(p/n)']:.3f}" if False else
              f"    M=max|eta|={M:.3f}  M/sqrt(n)={M/math.sqrt(n):.3f}")
        print(f"    |T|_max=n^2*M={Tmax:.3e}   Lemma4.1 bnd p^1/4 n^19/8={lemma41:.3e}   I012 n^(2+1/4)={i012_claim:.3e}")
        print(f"    => bounding |T|<=n^(2+1/4-eta) <=> |eta|<=n^(1/4-eta): "
              f"have M={M:.2f}, n^(1/4)={n**0.25:.2f}  -> M {'<=' if M<=n**0.25 else '>'} n^(1/4) "
              f"({'sub-quarter (already past target!)' if M<=n**0.25 else 'EXCEEDS n^1/4 => I012 bound FALSE for the subgroup itself'})")
        print()

    # ---- T2 & T3: product-energy of sub-tori vs additive sumsets (the operative sets) ----
    print("="*78)
    print("T2/T3: product-energy E_prod and the di-Benedetto operative-set premise")
    print("="*78)
    for mu in [3, 4]:
        n = 2**mu
        p = find_prime(n)
        mun = subgroup(p, n)
        munset = set(mun)
        # (I012 case) X=Y=Z=mu_n
        E_sub = product_energy(p, mun, mun, mun)
        # generic diagonal lower bound for a product map on a Cartesian cube of size n is n^3
        # (each product value w has its representation count; diagonal contributes |X||Y||Z|)
        diag = n**3
        # additive sumset X = {x1+x2+x3}, diff-set Z = {z1-z2}  (what Lemma 4.1 is ACTUALLY fed)
        sum3 = sorted({(a + b + c) % p for a in mun for b in mun for c in mun} - {0})
        diff2 = sorted({(a - b) % p for a in mun for b in mun} - {0})
        E_add = product_energy(p, sum3, sum3, diff2)
        # T3 premise: how torus-like are the operative sets? fraction inside mu_n.
        frac_sum3_in_mun = sum(1 for v in sum3 if v in munset) / max(1, len(sum3))
        frac_diff2_in_mun = sum(1 for v in diff2 if v in munset) / max(1, len(diff2))
        rec = {
            "n": n, "p": p,
            "E_prod(mu_n,mu_n,mu_n)": E_sub,
            "diag_lower n^3": diag,
            "E_sub / n^3": E_sub / diag,
            "E_sub / n^4 (generic-cube upper ~|sets|^2/|range| baseline)": E_sub / n**4,
            "|sum3 set|": len(sum3), "|diff2 set|": len(diff2),
            "E_prod(sum3,sum3,diff2)": E_add,
            "frac_sum3_in_mun": frac_sum3_in_mun,
            "frac_diff2_in_mun": frac_diff2_in_mun,
        }
        out["cases"].append({"T2T3": rec})
        print(f"  n={n} p={p}")
        print(f"    E_prod(mu_n^3) = {E_sub}   (= n^3*? : E/n^3 = {E_sub/diag:.3f})")
        print(f"      [mu_n^3 product map: each w in mu_n has exactly n^2 reps => E = n*(n^2)^2 = n^5]")
        print(f"      check n^5 = {n**5}, E_sub = {E_sub}  match={E_sub==n**5}")
        print(f"    operative sets (di Benedetto): |sum3|={len(sum3)} (vs n={n}), |diff2|={len(diff2)}")
        print(f"      frac of sum3 inside mu_n (torus) = {frac_sum3_in_mun:.4f}  "
              f"=> {'NEARLY ALL on torus' if frac_sum3_in_mun>0.5 else 'SPREAD off torus (NOT a sub-torus)'}")
        print(f"      frac of diff2 inside mu_n (torus) = {frac_diff2_in_mun:.4f}  "
              f"=> {'NEARLY ALL on torus' if frac_diff2_in_mun>0.5 else 'SPREAD off torus (NOT a sub-torus)'}")
        print(f"    E_prod(sum3,sum3,diff2) = {E_add}")
        print()

    with open("scripts/probes/i012_subgroup_trilinear_results.json", "w") as f:
        json.dump(out, f, indent=2, default=str)
    print("wrote scripts/probes/i012_subgroup_trilinear_results.json")

if __name__ == "__main__":
    main()
