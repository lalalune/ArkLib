#!/usr/bin/env python3
"""DECISIVE: is the MCA bad-scalar count DOMAIN-INDEPENDENT? (does delta* depend on the domain?)

For fixed (p,n,k) and radius delta, compute the exact worst-line bad-scalar count for the
smooth multiplicative subgroup AND for MANY other n-subsets of F_p^*.  If the count is the
SAME for all domains, delta* is domain-blind (kills N1/N1'/S3 and confirms the list-decoding
coupling: delta* = a function of (n,k) alone).  If ANY domain differs, the domain matters and
the smooth-specific hypotheses survive.  Pre-registered, exact arithmetic.
"""
import itertools, random
exec(open('/tmp/probe_n1_energy_vs_badcount.py').read().split('# ---- run')[0])

random.seed(11)
print("DOMAIN-BLINDNESS TEST: bad-count distribution over n-subsets (smooth flagged)")
print(f"{'p':>4} {'n':>3} {'k':>2} {'delta':>6} {'#domains':>9} {'badcounts(distinct)':>22} {'smooth':>7}")
for (p,n,k,deltas) in [(7,6,3,[0.30,0.37,0.45]),(11,5,3,[0.20,0.31,0.42]),(13,4,3,[0.10,0.21,0.35]),(13,4,2,[0.20,0.30,0.45])]:
    if (p-1)%n!=0: continue
    H=tuple(mult_subgroup(p,n))
    allpts=[x for x in range(1,p)]
    # enumerate ALL n-subsets if feasible, else sample
    subs=list(itertools.combinations(allpts, n))
    if len(subs) > 60:
        subs = random.sample(subs, 60)
    if H not in subs: subs=[H]+subs
    for delta in deltas:
        counts={}
        smooth_bc=None
        feasible=True
        for D in subs:
            bc=bad_count_at_delta(p,list(D),k,delta)
            if bc is None: feasible=False; break
            counts[bc]=counts.get(bc,0)+1
            if D==H: smooth_bc=bc
        if not feasible:
            print(f"{p:>4} {n:>3} {k:>2} {delta:>6} {'--':>9} {'infeasible':>22} {'--':>7}")
            continue
        distinct=sorted(counts.keys())
        print(f"{p:>4} {n:>3} {k:>2} {delta:>6} {len(subs):>9} {str(distinct):>22} {str(smooth_bc):>7}")
