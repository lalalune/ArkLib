#!/usr/bin/env python3
"""
#407 C2 — the DECISIVE structural test: is the char-p moment anomaly #spurious_r
concentrated on GAP-CONSTRAINED (count-lane-relevant) configs, or on GENERIC ones?

WHY THIS IS THE QUESTION.
  The moment E_r(F_p) = (1/p) sum_b |eta_b|^{2r} counts ALL collisions
  sum_{i} x_i = sum_j y_j (mod p) among r-fold sums of mu_n — UNSTRUCTURED.
  The char-p anomaly #spurious_r turns on at r* ~ beta (=4 for p~n^4); we confirmed
  this (probe_407_conn_c2_crossover_scan).

  The COUNT lane is DIFFERENT: it counts only configs S with the GAP constraints
  e_i(S)=0 for i in {1,..,2m-1}\{m} (a measure-zero structured slice), and asks
  whether such S can be a NON-coset (= a char-p-spurious config contributing a NEW
  bad scalar e_m outside the char-0 sumset).

  If the moment anomaly is dominated by GENERIC (gap-VIOLATING) collisions, then the
  count lane could still be char-0-clean even though the moment is anomalous — a
  genuine BGK bypass. If instead char-p collisions ALSO appear among gap-constrained
  configs at the same r*, the count lane re-hits the wall.

TEST.
  For n small (so we can enumerate), at a NON-saturated prime p, split the char-p
  excess by whether the colliding config is a coset-union (char-0-structured) or not.
  Concretely we directly enumerate size-(rm) subsets S of mu_n with the gap
  constraints satisfied OVER F_p, and check:
    (G1) does any gap-valid S over F_p FAIL to be a coset-union?  (= char-p spurious)
    (G2) at what config size rm does the FIRST char-p spurious gap-valid S appear,
         as a function of p?  Does it scale like p <= (rm)^{n/2} (height bound) or
         like saturation p <~ |Sigma_r|?

  We sweep p across a wide non-saturated range for each n, and for each config size
  find the SMALLEST p at which a spurious gap-valid config exists (the 'spurious
  threshold prime' p_spur(n, size)). If p_spur grows like (size)^{n/2} the count
  lane is BGK-hard; if p_spur stays <~ |Sigma| (saturation) the prize regime is safe.
"""
import sys, math, itertools
from collections import defaultdict
from sympy import isprime, primitive_root, nextprime
from math import comb

def fp_root(n,p):
    g0=primitive_root(p)
    g=pow(g0,(p-1)//n,p)
    return g

def gap_indices(m):
    return [i for i in range(1,2*m) if i!=m]

def elem_sym(pts, k, p):
    # k-th elementary symmetric poly of pts mod p, via Newton-free direct (k small)
    s=0
    for c in itertools.combinations(pts,k):
        prod=1
        for x in c: prod=(prod*x)%p
        s=(s+prod)%p
    return s

def scan_n(n, m, rvals, primes):
    """For each config-multiplicity r in rvals, find smallest prime p in `primes`
    (p===1 mod n, root exists) at which a NON-COSET gap-valid config of size rm exists."""
    h=n//2
    gaps=gap_indices(m)
    results={}
    # precompute subsets once per size
    for r in rvals:
        size=r*m
        if comb(n,size)>1_500_000:
            results[r]=(size,None,"too many subsets")
            continue
        subs=list(itertools.combinations(range(n),size))
        first_spur_p=None; nonsat_checked=0; total_noncoset_evidence=0
        sat_p=None
        for p in primes:
            if p%n!=1: continue
            try: g=fp_root(n,p)
            except Exception: continue
            if g is None: continue
            roots=[pow(g,j,p) for j in range(n)]
            # saturation check on Sigma_r (distinct r-fold sums of mu_n)
            # (cheap proxy: |distinct e_m over all coset configs| vs p)
            noncoset=0
            for S in subs:
                pts=[roots[j] for j in S]
                ok=True
                for i in gaps:
                    if elem_sym(pts,i,p)!=0: ok=False; break
                if not ok: continue
                es=set(S)
                if not all(((j+h)%n) in es for j in S):
                    noncoset+=1
            nonsat_checked+=1
            if noncoset>0:
                total_noncoset_evidence+=1
                if first_spur_p is None:
                    first_spur_p=p
        results[r]=(size, first_spur_p, f"{total_noncoset_evidence}/{nonsat_checked} primes had spurious")
    return results

def main():
    # height bound prediction: p_spur ~ (size)^{n/2}; saturation ~ |Sigma_r|
    print("="*100)
    print("C2 GAP-vs-GENERIC — does char-p spurious appear among GAP-CONSTRAINED configs,")
    print("and at what prime threshold? (height bound (rm)^{n/2} vs saturation |Sigma_r|)")
    print("="*100)
    for (n,m,rvals) in [(8,2,[2,3,4]), (12,2,[2,3,4]), (16,2,[2,3]), (16,4,[2]), (24,2,[2,3])]:
        # sweep a wide band of primes p === 1 mod n, from small (saturated) up
        primes=[]
        p=n+1
        while len(primes)<400 and p< n*4000:
            if isprime(p): primes.append(p)
            p+=n
        res=scan_n(n,m,rvals,primes)
        print(f"\n--- n={n} m={m}  primes p===1 mod n in [{primes[0]},{primes[-1]}] ({len(primes)} primes) ---")
        for r in rvals:
            size,fp,note=res[r]
            height=size**(n//2)
            sigma= (n**r)/( (2**r)*math.factorial(r) )  # rough |Sigma_r|
            if fp is None:
                if note and "too many" in note:
                    print(f"  r={r} size={size}: {note}")
                else:
                    print(f"  r={r} size={size}: NO spurious in band (max p={primes[-1]}); "
                          f"height bound (rm)^(n/2)~2^{math.log2(height):.0f}, |Sigma_r|~{sigma:.0f}  [{note}]")
            else:
                print(f"  r={r} size={size}: FIRST spurious at p={fp} (saturated? |Sigma_r|~{sigma:.0f}, "
                      f"p/|Sigma_r|={fp/sigma:.2f})  [{note}]")
    print("\nINTERPRETATION: if spurious only at p <~ |Sigma_r| (p/|Sigma_r|<~1) => spurious=>saturated")
    print(" => prize (non-saturated, p>>|Sigma_r|) is SAFE for the count, regardless of moment r*.")
    print(" If spurious persists at p>>|Sigma_r| (non-saturated) => count lane re-hits BGK.")

if __name__=="__main__":
    main()
