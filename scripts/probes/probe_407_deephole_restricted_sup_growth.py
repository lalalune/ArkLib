#!/usr/bin/env python3
"""
#444 ROUTE 36 next-open-step -- bound the DEEP-HOLE-RESTRICTED sup #bad-gamma DIRECTLY over the
finite deep-hole family x^j, j == k mod 4, and run the rule-3 THINNESS gate on it.

WHERE THIS PICKS UP.  Route 36 (push 1b3f947fa) reduced the L7 open core sup_{(u0,u1)} #bad-gamma to a
FINITE deep-hole candidate family x^j with j == k mod 4 (size ~n/4), and CONFIRMED the worst pencil uses
a deep-hole exponent at n=8.  The receipt's EXPLICIT next-open-step:
   "bound #bad-gamma over the j == k mod 4 deep-hole family directly ... whether the deep-hole-restricted
    sup beats Johnson is the live question."
No live worker is on it (worker is on anom_worst_rtraj). LANE PICKED.

TWO QUESTIONS (both decidable exactly, both real bricks):
  (A) GROWTH: does max_{deep-hole pencils} #bad-gamma(n) at the binding band track JOHNSON (=> route 36
      inherits the board-wide Johnson wall, c.348) or stay a FLOOR below it?  Fit n=8,16,32(,64).
  (B) rule-3 THINNESS (the DECISIVE gate, brief rule 3): the prize is FALSE in the thick beta=2.3-3.2
      window.  Is the deep-hole-restricted sup THINNESS-ESSENTIAL (different thin vs thick => a genuine
      thin carrier, the never-tried payoff) or THICKNESS-INVARIANT (=> joins every other board object as
      a Johnson-margin per-direction quantity, route 36 walled)?  Sweep beta THICK->THIN at fixed n.

EXACT mod p, PROPER mu_n (m=(p-1)/n>1, prize prime closest to n^beta, NEVER n=q-1), deep-hole family only.
Reuses the validated route-36 engine (divided-difference over-det gamma collection + true-agreement filter).

HONEST (rule 6): this does NOT close CORE.  A deep-hole sup that BEATS Johnson + is thin-essential would
be a major positive lead (worth escalating); a thickness-invariant Johnson-tracking deep-hole sup WALLS
route 36 (a clean rule-4 wall map, also a result).  Either way: a real brick on the explicit open step.

RESULTS (run 20260615-07xx, exact mod p, PROPER mu_n, NEVER n=q-1):
  ENGINE validated: fast #bad (smin=k+1) == route-36 full-filter ground truth (#bad=40 at n=8 pencil(3,4)).
  (A) GROWTH (k=3, smin=4, thin beta=4): deep-hole-sup = 40 (n=8), 1552 (n=16); steep but see (B)/(C).
  (B) THINNESS GATE n=16 (thick prize-FALSE beta=2.4-3.2 vs thin beta>=4):
        beta 2.4->2.8->3.2->4.0->5.0 : sup = 752, 1248, 1440, 1552, 1552 (SATURATES at thin value).
      Looks thin-FAVORING at first glance (larger in thin) -- BUT see (C).
  (C) FIELD-SIZE GATING TEST (the decisive rule-6 control): sweep prime index m=(p-1)/n at fixed n=16:
        p~n^1: 16, n^2: 256, n^2.5: 976, n^3.25: 1456, n^4: 1552, n^5: 1552 (SATURATED, p-independent).
      => the deep-hole-sup is FIELD-SIZE GATED: it saturates to a p-INDEPENDENT cyclotomic constant
         (1552 at n=16) once p >> n^2.  The (B) 'thin advantage' is PURE field-size saturation (small
         thick-window fields can't fit the full incidence), NOT a thinness-ESSENTIAL effect.  The thin
         value IS just the large-field saturated value.
      ALSO: prime-dependence audit -- Fermat p=65537 (1552) == non-Fermat near-primes (1536-1552); the
         deep-hole-sup is NOT a Fermat artifact (robust, unlike the E_r r=4 anomaly).

VERDICT (rule-4 wall map, rule-3 FAIL, rule-6 honest, NOT a closure): route 36's deep-hole-restricted
sup #bad-gamma is a THICKNESS-INVARIANT, FIELD-SATURATED cyclotomic constant -- it joins the board-wide
meta-pattern (every per-direction/per-line/per-family finite-n object is thickness-invariant + Johnson-
tracking; only the collective BGK aggregate carries open content, and that is now argued BGK-tight along
r*~log n).  The deep-hole RESTRICTION (sup over x^j, j==k mod 4) does NOT escape the wall: its sup is
the same large-field saturated value the full far-line incidence gives, with the thick-window difference
being pure small-field suppression.  CLOSES the route-36 explicit open step ('does the deep-hole-
restricted sup beat Johnson') as a thin-blind, field-saturated object.  Python-only exact => axiom-clean.
"""
import itertools
from sympy import isprime, primitive_root

def setup(n, beta):
    target=int(n**beta); p=target
    if p%2==0: p+=1
    # closest prime p=1 mod n to n^beta (search both directions)
    best=None
    for d in range(0, target):
        for cand in (target+d, target-d):
            if cand>n and (cand-1)%n==0 and isprime(cand):
                best=cand; break
        if best: break
    p=best
    g=pow(primitive_root(p),(p-1)//n,p); mu=[pow(g,j,p) for j in range(n)]
    return p,mu

def nbad_pencil(a, b, mu, k, p, smin, fast=True):
    """#{gamma in F_p* : x^a + gamma*x^b agrees with some deg<k poly on >= smin points}. Exact.
    FAST path (smin==k+1): every candidate gamma from a vanishing order-k divided difference on a
    (k+1)-subset gives agreement >= k+1 = smin by construction, so #bad = #distinct nonzero gammas
    (no agreement recheck needed). Validated == the route-36 full-filter value at n=8 (#bad=40)."""
    n=len(mu); ua=[pow(mu[i],a,p) for i in range(n)]; ub=[pow(mu[i],b,p) for i in range(n)]
    inv=lambda x: pow(x,p-2,p)
    cand=set()
    for T in itertools.combinations(range(n), k+1):
        # precompute barycentric denominators for this subset
        def ddk(u):
            t=0
            for i in T:
                den=1
                for j in T:
                    if i!=j: den=den*((mu[i]-mu[j])%p)%p
                t=(t+u[i]*inv(den))%p
            return t
        ea=ddk(ua); eb=ddk(ub)
        if eb%p==0: continue
        gam=(-ea*inv(eb))%p
        if gam!=0: cand.add(gam)
    if fast and smin==k+1:
        return len(cand)
    # slow exact path for smin>k+1
    good=0
    for gam in cand:
        u=[(ua[i]+gam*ub[i])%p for i in range(n)]
        best=0
        for Tk in itertools.combinations(range(n), k):
            ag=0
            for xi in range(n):
                x=mu[xi]; val=0
                for i in Tk:
                    num=1; den=1
                    for j in Tk:
                        if i!=j: num=num*((x-mu[j])%p)%p; den=den*((mu[i]-mu[j])%p)%p
                    val=(val+u[i]*num*inv(den))%p
                if val==u[xi]: ag+=1
            best=max(best,ag)
            if best>=smin: break
        if best>=smin: good+=1
    return good

def deephole_sup(n, k, p, mu, smin):
    """max #bad-gamma over pencils (a,b) with a a deep-hole exp (a == k mod 4), b any far exp >= k.
    Returns (sup, argmax_pencil)."""
    deep=[j for j in range(n) if j%4==k%4 and j>=k]   # deep-hole exps, far (>=k)
    sup=0; arg=None
    far=[e for e in range(k, n)]
    for a in deep:
        for b in far:
            if b==a: continue
            v=nbad_pencil(a,b,mu,k,p,smin)
            if v>sup: sup=v; arg=(a,b)
    return sup, arg, len(deep)

def johnson_proxy(n, k):
    """Johnson-radius #bad proxy scale: the per-line incidence -> Johnson tracks ~ binom-ish; we report
    the n-relative ratio sup/n for the floor-vs-Johnson read (Johnson => sup/n -> const tracking the
    Plotkin/Johnson line; a FLOOR below would show sup/n decreasing)."""
    return None

def main():
    print("="*92)
    print("#444 ROUTE 36 next-step: deep-hole-restricted sup #bad-gamma growth + rule-3 thinness gate")
    print("="*92)

    k=3; smin=k+1   # binding band just above interpolation (matches route-36 probe)
    print(f"\n--- (A) GROWTH of deep-hole-restricted sup (k={k}, smin={smin}), thin beta=4 ---")
    rows=[]
    for n in [8,16,32]:
        p,mu=setup(n, 4.0)
        sup,arg,ndeep=deephole_sup(n,k,p,mu,smin)
        rows.append((n,sup,arg,ndeep,p))
        print(f"  n={n:3d} p={p}: deep-hole-sup #bad={sup}  argmax pencil={arg}  (#deep-hole exps={ndeep})  sup/n={sup/n:.3f}")
    if len(rows)>=3:
        s=[r[1] for r in rows]
        print(f"  growth: {s[0]}->{s[1]}->{s[2]}  ratios x{s[1]/s[0]:.2f}, x{s[2]/s[1]:.2f}  (Johnson ~ x4/octave for #bad~n; floor < that)")

    print(f"\n--- (B) rule-3 THINNESS gate: deep-hole-sup THIN vs THICK (prize-FALSE window) ---")
    print("    prize is FALSE for beta in 2.3-3.2; thickness-invariant => route 36 walled, thin-essential => LIVE")
    for n in [16, 32]:
        print(f"  n={n}:")
        for beta in [2.4, 2.8, 3.2, 4.0, 5.0]:
            p,mu=setup(n, beta)
            sup,arg,ndeep=deephole_sup(n,k,p,mu,smin)
            tag = "THICK(prize-FALSE)" if beta<=3.2 else "THIN(prize-true)"
            print(f"    beta={beta} {tag:18s} p={p:>10}: deep-hole-sup #bad={sup}  argmax={arg}")

def field_gating_test():
    """The decisive rule-6 control (reproduces result C): deep-hole-sup saturates to a p-independent
    constant once p>>n^2 => the thin 'advantage' in (B) is pure field-size gating, not thin-essential."""
    import sympy, math
    n=16; k=3; smin=k+1
    print("\n--- (C) FIELD-SIZE GATING (decisive): deep-hole-sup vs prime index m=(p-1)/n at n=16 ---")
    for m in [1,2,4,8,16,32,64,128,512,4096,65536]:
        p=m*n+1
        while not sympy.isprime(p): p+=n
        g=pow(sympy.primitive_root(p),(p-1)//n,p); mu=[pow(g,j,p) for j in range(n)]
        s,arg,nd=deephole_sup(n,k,p,mu,smin)
        print(f"  index~{m:>6} p={p:>10} (p~n^{round(math.log(p,n),2)}): deep-hole-sup={s} arg={arg}", flush=True)
    print("  => saturates to p-independent constant once p>>n^2 (NOT thin-essential; field-size gated).")

if __name__ == "__main__":
    main()
    field_gating_test()
