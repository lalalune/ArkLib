#!/usr/bin/env python3
"""
THE CLEANEST decisive #444 test: B-vs-p ANTI-CORRELATED prime pairs.

A natural experiment that fully separates the field-size confound from B-coupling.  Among
primes p = 1 mod 8, the 1-D subgroup sup B = max_{b!=0}||eta_b|| is NON-monotone in p:

   p=97  -> B=5.461   (LARGER B)        p=113 -> B=5.114   (SMALLER B, but LARGER p)
   p=241 -> B=6.339   (LARGER B)        p=257 -> B=6.101   (SMALLER B, but LARGER p)

So in each pair the SMALLER prime has the LARGER B.  Now compute the EXACT in-tree worst-case
mcaEvent bad-gamma COUNT (probe_exact_epsmca_ladder.eps_profile_syndrome, validated vs naive
word-level) for RS[mu_8, k] at both primes of each pair.  Three mutually exclusive outcomes:

  (FIELD)  count grows with p (113 > 97, 257 > 241):  the count is driven by FIELD SIZE
           (more scalars => more bad gamma), epsMCA = count/p ~ const Theta(1).  B IRRELEVANT.
  (B-WALL) count grows with B (97 > 113, 241 > 257, i.e. AGAINST p):  the count RE-COUPLES
           to the sup B -- the prize wall lives in the >=2-D incidence after all.
  (BLIND)  count IDENTICAL across the pair (like the 1-D far-line incidence = n exactly):
           B-blind AND p-blind => a purely combinatorial / L2 invariant => MAJOR reframe.

EXACT, no sampling.  PROPER smooth mu_8.  This is the measurement lalalune asked for.
"""
import importlib.util, os, math, cmath
_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "ladder", os.path.join(_here, "probe_exact_epsmca_ladder.py"))
ladder = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(ladder)

def sup_B(mu,p):
    w=2j*math.pi/p; B=0.0; arg=None
    for b in range(1,p):
        s=sum(cmath.exp(w*((b*x)%p)) for x in mu)
        if abs(s)>B: B=abs(s); arg=b
    return B,arg

# (smaller prime has LARGER B in each pair) -- n=8
PAIRS_N8 = [(97,113),(241,257)]
# also a non-anti-correlated control pair for n=4 (B monotone in p there)
def main():
    n=8
    for k in [6]:   # n-k=2 keeps p^4 enumeration feasible at p~100-260
        rho=k/n
        print(f"\n{'='*82}")
        print(f"RS[mu_{n}, k={k}]  rho={rho:.3f}  Johnson={1-math.sqrt(rho):.3f}  "
              f"capacity={1-rho:.3f}   EXACT in-tree mcaEvent")
        print(f"{'='*82}")
        for (pa,pb) in PAIRS_N8:
            muA=ladder.smooth_domain(pa,n); muB=ladder.smooth_domain(pb,n)
            Ba,_=sup_B(muA,pa); Bb,_=sup_B(muB,pb)
            print(f"\n  --- PAIR (p={pa}, p={pb}): smaller prime {pa} has B={Ba:.4f}, "
                  f"larger prime {pb} has B={Bb:.4f} "
                  f"({'B anti-correlated with p' if (pa<pb and Ba>Bb) else 'NOT anti-corr'}) ---")
            bestA,_=ladder.eps_profile_syndrome(pa,n,k)
            bestB,_=ladder.eps_profile_syndrome(pb,n,k)
            ms=sorted(bestA.keys(), reverse=True)
            print(f"     {'m':>3} {'delta':>7} | {'count@'+str(pa):>10} | {'count@'+str(pb):>10} | verdict")
            for m in ms:
                cA=bestA[m]; cB=bestB[m]
                delta=1-m/n
                if cA==0 and cB==0:
                    v="(both 0)"
                elif cA==cB:
                    v="IDENTICAL => B-blind AND p-blind (combinatorial invariant)"
                elif (cA>cB):   # smaller prime (larger B) has MORE => tracks B against p
                    v="LARGER at smaller-p/larger-B => RE-COUPLES to B (wall)"
                else:           # cB>cA : larger prime has more => field-size driven
                    v="larger at larger-p => FIELD-SIZE driven (B irrelevant)"
                print(f"     {m:>3} {delta:>7.3f} | {cA:>10} | {cB:>10} | {v}")
            # summary: also report epsMCA = count/p to see the probability scale
            print(f"     [epsMCA = count/p at the binding m: ", end="")
            mb = max((m for m in ms if bestA[m]>0 or bestB[m]>0), default=ms[-1])
            print(f"m={mb}: {bestA[mb]}/{pa}={bestA[mb]/pa:.4f} vs "
                  f"{bestB[mb]}/{pb}={bestB[mb]/pb:.4f}]")

if __name__=="__main__":
    main()
