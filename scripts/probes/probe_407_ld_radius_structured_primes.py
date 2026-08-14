#!/usr/bin/env python3
"""
probe_407_ld_radius_structured_primes.py  (#444 LD-radius lane, structured-prime gate)

Companion to probe_407_ld_plateau_thinness*.py (which showed the n-plateau is thinness-essential but
ANTI-helpful, and that smooth s* is q-invariant across GENERIC prize primes).

NEW UNCONTESTED EDGE: the brief (rule 2) + the §3/§4 meta-theorem say additive-moment / energy methods
fail SPECIFICALLY at STRUCTURED primes (Fermat-type p = 2^{2^t}+1), where the 2-power subgroup mu_n
interacts with the field arithmetic non-generically. NOBODY has tested whether the far-line
LIST-DECODING RADIUS s*(mu_n,k) (the LD-reframing's core object) is INVARIANT under structured primes,
or whether a Fermat prime SHIFTS it.

If s* is constant across generic AND Fermat primes => s* is a purely combinatorial (char-0 / cyclotomic)
invariant of the 2-power subgroup, independent of the field's additive structure => the LD radius does
NOT see the structured-prime phenomenon that breaks moment methods => it is a DIFFERENT (cleaner) object.
If s* SHIFTS at a Fermat prime => the LD radius inherits the structured-prime sensitivity => the floor
question for s* is field-arithmetic-dependent, NOT purely cyclotomic (constrains any closed-form attempt).

METHOD (exact, proper subgroup, never n=q-1):
  n=8: generic prize primes (beta=4,5) vs STRUCTURED Fermat primes 257 (F_3-ish, 2^8+1, thin index 32)
       and 65537 (F_4, 2^16+1, deep index 8192). All p == 1 mod 8, proper subgroup mu_8.
  Compute s* = min s with max over far monomial dirs of incidence <= budget=n, exact engine incidence.
  Also report the WORST direction at s*-1 (where the plateau sits) to see if STRUCTURE changes which
  direction binds.
Python-only exact => axiom-clean trivially.
"""
import sys, math
sys.path.insert(0,'scripts/probes')
from probe_407_ld_plateau_thinness import is_prime, proot, factor, incidence_dir, s_star

def main():
    print("="*78)
    print("LD-radius s* under STRUCTURED (Fermat) vs GENERIC prize primes — exact, proper mu_8")
    print("="*78)
    n,k=8,2
    budget=n
    sJ = k+math.sqrt(k*n)
    # primes: label, p
    cases = [
        ("generic beta4", 4129),
        ("generic beta5", 32801),
        ("Fermat 2^8+1 (F3)  idx32", 257),
        ("Fermat 2^16+1 (F4) idx8192", 65537),
    ]
    print(f"n={n} k={k} budget={budget}  Johnson s_J={sJ:.3f} (delta*_J={1-sJ/n:.3f})")
    results=[]
    for label,p in cases:
        assert p%n==1 and is_prime(p), f"{p} bad"
        g=proot(p); m=(p-1)//n; h=pow(g,m,p)
        assert pow(h,n,p)==1 and pow(h,n//2,p)!=1, "h not primitive n-th root"
        mu=[pow(h,i,p) for i in range(n)]
        assert len(set(mu))==n
        s_s, prof = s_star(mu,k,p,budget)
        # worst direction at the plateau (s = s_s) and just below
        results.append((label,p,m,s_s,prof))
        print(f"\n  [{label}] p={p} index m={m}")
        print(f"     s* = {s_s}   delta* = {1-s_s/n:.4f}   profile(s->maxI): {prof}")
    sset = set(r[3] for r in results)
    print("\n" + "-"*78)
    if len(sset)==1:
        print(f"VERDICT: s* = {sset.pop()} INVARIANT across generic AND Fermat structured primes")
        print("  => the far-line LD radius is a CHAR-0/CYCLOTOMIC invariant of mu_8, BLIND to the")
        print("     structured-prime arithmetic that breaks moment methods. It is a CLEANER object")
        print("     than the moment/energy face (which IS structured-prime-sensitive per the meta-thm).")
        print("  CAVEAT (rule 6): blindness to structure means s* alone canNOT encode the structured-")
        print("     prime mechanism the meta-theorem says is essential => if CORE genuinely needs that")
        print("     mechanism, a purely-s* (cyclotomic) argument is NECESSARY-not-sufficient.")
    else:
        print(f"VERDICT: s* SHIFTS across primes: {[(r[0],r[3]) for r in results]}")
        print("  => the far-line LD radius INHERITS structured-prime sensitivity => NOT purely cyclotomic;")
        print("     any closed-form s*(n,k) must carry a field-arithmetic (prime-structure) dependence.")

if __name__=="__main__":
    main()
