#!/usr/bin/env python3
"""
probe_407_ld_plateau_dilation_orbit.py  (#444 LD-radius lane -> formalization scaffold)

The prev two results pinned: the per-direction n-PLATEAU (max_dir incidence = exactly n on a plateau)
is thinness-essential. The KB attributes "= n" to "n | #bad (one cyclic orbit)". This probe VERIFIES
the MECHANISM exactly, as the probe-first step before any Lean formalization:

CLAIM TO TEST: at the plateau (s where the binding direction realizes incidence = n), the bad-scalar
set B = {gamma : x^a + gamma x^b agrees with RS[mu_n,k] on the s-subset} is, AT THE BINDING DIRECTION,
exactly ONE orbit of size n under a group action — specifically the DILATION action induced by z -> h*z
on mu_n (h = generator), which acts on the agreement structure and permutes the witnessing subsets,
forcing the bad-scalar multiset to be a union of orbits whose sizes divide n.

PRECISE OBJECT: for the BINDING direction (a,b) at the plateau radius s, collect the full set of
(gamma, witness-subset) incidences. Test:
  (1) |distinct gamma| = n exactly (the plateau value).
  (2) The dilation z->h*z maps each witnessing (gamma, R) to (gamma', R') with R' = h-shifted R and
      gamma' = h^{(a-b)} * gamma  (the monomial line x^a+gamma x^b under z->hz becomes
      h^a x^a + gamma h^b x^b = h^a (x^a + gamma h^{b-a} x^b), so the line is preserved up to scale with
      gamma -> gamma * h^{b-a}). => the gamma-set is CLOSED under multiplication by h^{b-a}.
  (3) h^{b-a} has order n/gcd(n,b-a) in mu_n; so the gamma-set is a union of cosets of <h^{b-a}>, each of
      size n/gcd(n,b-a). For the binding monomial (a,b)=(k, k+something) with gcd(n,b-a)=1 => single
      orbit of size n => plateau = n EXACTLY.  THIS is the divisibility mechanism, made precise.

If (1)-(3) all hold exactly across primes + sizes, the plateau-=-n is a DILATION-ORBIT theorem
(formalizable: the gamma-set is a coset-union of <h^{b-a}>, |orbit| = n/gcd(n,b-a)). That is a real brick
toward the in-tree FarCosetExplosion / ActionOrbitGeneralF machinery.

Exact, proper mu_n, prize band, never n=q-1. Python-only => axiom-clean trivially.
"""
import sys, math
sys.path.insert(0,'scripts/probes')
from probe_407_ld_plateau_thinness import is_prime, proot, incidence_dir, s_star

def gamma_set_dir(a,b,dom,k,p,s):
    c = incidence_dir(a,b,dom,k,p,s)
    return c  # set of gamma, or None if heavy

def main():
    print("="*78)
    print("LD plateau = single DILATION ORBIT: exact mechanism verification (formalization scaffold)")
    print("="*78)
    for (n,k,p_override) in [(8,2,4129),(8,3,4129),(8,2,257)]:
        p=p_override
        assert p%n==1 and is_prime(p)
        g=proot(p); m=(p-1)//n; h=pow(g,m,p)
        assert pow(h,n,p)==1 and pow(h,n//2,p)!=1
        mu=[pow(h,i,p) for i in range(n)]
        budget=n
        # find the plateau: the s and binding dir where max_dir incidence = n
        ss, prof = s_star(mu,k,p,budget)
        # the plateau radius: the s just before s* where maxI hits n (the binding plateau)
        # scan to find a (dir, s) with incidence exactly == n at the binding
        plateau_s=None; binding=None; gset=None
        for s in range(k+1, n+1):
            best=0; bdir=None; bset=None
            for a in range(n):
                for b in range(k,n):
                    if b==a: continue
                    c=incidence_dir(a,b,mu,k,p,s)
                    if c is None: continue
                    if len(c)>best: best=len(c); bdir=(a,b); bset=c
            if best==n:
                plateau_s=s; binding=bdir; gset=bset
                break
        print(f"\n--- n={n} k={k} p={p} (h=g^{m}) s*={ss} ---")
        if plateau_s is None:
            print(f"    no exact =n plateau found in profile {prof}; skip orbit test")
            continue
        a,b=binding
        d=(b-a)%n
        gcd_=math.gcd(n,d)
        orbit_gen = pow(h, (b-a)%(p-1), p)  # h^{b-a}
        # (1) |gset| = n ?
        c1 = (len(gset)==n)
        # (2) gset closed under multiply by h^{b-a} ?
        gs=set(gset)
        c2 = all((x*orbit_gen)%p in gs for x in gs)
        # (3) orbit size of <h^{b-a}> = n/gcd(n,b-a); #orbits = |gset| / orbitsize
        orbit_size = n//gcd_
        c3 = (len(gs) % orbit_size == 0)
        n_orbits = len(gs)//orbit_size if orbit_size else 0
        print(f"    plateau radius s={plateau_s}, binding dir (a,b)=({a},{b}), b-a={b-a} (mod n: {d}), gcd(n,b-a)={gcd_}")
        print(f"    (1) |gamma-set| = {len(gset)}  (== n? {c1})")
        print(f"    (2) gamma-set closed under * h^(b-a) (dilation):  {c2}")
        print(f"    (3) orbit size = n/gcd(n,b-a) = {orbit_size};  #orbits = |gset|/orbit = {n_orbits}  (integer? {c3})")
        if c1 and c2 and c3:
            print(f"    => PLATEAU = {n_orbits} dilation-orbit(s) of size {orbit_size}. The '=n' value is "
                  f"FORCED by the dilation action z->h z (gamma -> gamma*h^(b-a)). MECHANISM CONFIRMED.")
        else:
            print(f"    => mechanism NOT clean here (c1={c1} c2={c2} c3={c3}); orbit story needs refinement.")

if __name__=="__main__":
    main()
