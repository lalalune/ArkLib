#!/usr/bin/env python3
"""
SHARPENED decisive #444 test (controls the field-size confound).

The crude "count varies across p" test is confounded: a larger field has more scalars gamma,
so the bad-gamma COUNT can grow with p even if the mechanism is B-INDEPENDENT (the count could
be ~ c*p with c fixed => epsMCA = count/p constant, a pure field-saturation Theta(1), NOT B).
The 1-D far-line case escaped this because the incidence was EXACTLY constant (=n, not ~p).

To isolate B-coupling we compare primes of NEAR-EQUAL MAGNITUDE but DIFFERENT B.  Among primes
p = 1 mod n in a narrow band, the 1-D subgroup sup B = max_{b!=0}||eta_b|| still varies (the
period spectrum is sensitive to the multiplicative structure of p, not just |F|).  If the EXACT
worst-case epsMCA bad-gamma COUNT is the SAME for two near-equal-magnitude primes with different
B, the count is B-blind.  If the prime with larger B has a larger count (at equal magnitude),
epsMCA re-couples to B.

We report, per witness threshold m:  count(p) for each prime, and whether the count ordering
matches the B ordering AT EQUAL MAGNITUDE.

EXACT in-tree mcaEvent (probe_exact_epsmca_ladder.eps_profile_syndrome, validated vs naive).
PROPER smooth mu_n (n=2^a, n|p-1), p>>n, NEVER n=q-1.
"""
import importlib.util, os, math, cmath
_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "ladder", os.path.join(_here, "probe_exact_epsmca_ladder.py"))
ladder = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(ladder)

def is_prime(m):
    if m < 2: return False
    for d in range(2, int(m**0.5)+1):
        if m % d == 0: return False
    return True

def primes_cong1_band(n, lo, hi):
    out=[]; p = lo - (lo % n) + 1
    if p < lo: p += n
    while p <= hi:
        if p > 2 and p % n == 1 and is_prime(p): out.append(p)
        p += n
    return out

def sup_B(mu, p):
    w = 2j*math.pi/p; B=0.0
    for b in range(1,p):
        s=0j
        for x in mu: s += cmath.exp(w*((b*x)%p))
        if abs(s)>B: B=abs(s)
    return B

def main():
    # n,k chosen for EXACT exhaustive feasibility (cost ~ p^{2(n-k)+1}); narrow prime band.
    for (n,k,lo,hi) in [(4,3,60,400),(4,2,60,260),(8,6,80,360)]:
        primes = primes_cong1_band(n,k_lo_hi(lo),hi) if False else primes_cong1_band(n,lo,hi)
        rho=k/n
        print(f"\n{'='*80}\nRS[mu_{n}, k={k}] rho={rho:.3f}  Johnson={1-math.sqrt(rho):.3f}  "
              f"band p in [{lo},{hi}]  (EXACT mcaEvent)\n{'='*80}")
        data=[]
        for p in primes:
            mu = ladder.smooth_domain(p,n)
            B = sup_B(mu,p)
            best,_ = ladder.eps_profile_syndrome(p,n,k)
            data.append((p,B,best))
        # show B and the relationship of B to p (B should NOT be a clean function of p)
        print(f"  {'p':>6} {'B':>9} {'B/sqrtn':>8}   counts-by-threshold")
        ms = sorted(data[0][2].keys(), reverse=True)
        for (p,B,best) in data:
            cs = " ".join(f"m{m}:{best[m]}" for m in ms)
            print(f"  {p:>6} {B:>9.5f} {B/math.sqrt(n):>8.4f}   {cs}")
        # for each threshold, regress count on p and on B: which explains it?
        print(f"\n  threshold analysis (does count track p [field-saturation] or B [wall]?):")
        for m in ms:
            ps  = [d[0] for d in data]
            Bs  = [d[1] for d in data]
            cs  = [d[2][m] for d in data]
            if max(cs)==0:
                print(f"    m={m}: all counts 0"); continue
            # count/p : if ~constant, count is field-saturating (Theta(1) prob), NOT B
            cop = [c/p for (p,_,_),c in zip([(d[0],0,0) for d in data],cs)]
            cop = [cs[i]/ps[i] for i in range(len(ps))]
            cop_spread = (max(cop)-min(cop))/(sum(cop)/len(cop)) if sum(cop)>0 else 0
            # at NEAR-equal magnitude, does larger B give larger count?
            # pearson-ish sign test between B and count after removing p-trend (use count/p vs B)
            n_=len(cs)
            mB=sum(Bs)/n_; mC=sum(cop)/n_
            cov=sum((Bs[i]-mB)*(cop[i]-mC) for i in range(n_))
            vB=sum((Bs[i]-mB)**2 for i in range(n_)); vC=sum((cop[i]-mC)**2 for i in range(n_))
            corr = cov/math.sqrt(vB*vC) if vB>0 and vC>0 else 0.0
            verdict=""
            if cop_spread < 0.03:
                verdict="count/p CONSTANT => field-saturating Theta(1), B-BLIND"
            elif abs(corr) > 0.7:
                verdict=f"count/p CORRELATES with B (corr={corr:+.2f}) => RE-COUPLES"
            else:
                verdict=f"count/p varies but NOT with B (corr={corr:+.2f}) => not B-driven"
            print(f"    m={m} delta={1-m/n:.3f}: count/p spread={cop_spread:.4f}  "
                  f"corr(count/p, B)={corr:+.3f}  =>  {verdict}")

def k_lo_hi(x): return x
if __name__=="__main__":
    main()
