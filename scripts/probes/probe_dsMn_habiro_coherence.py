#!/usr/bin/env python3
"""
probe_dsMn_habiro_coherence.py  (NOT committed; scratch)

ATTACK on M(n) from the Habiro-ring / q-at-root-of-unity angle.

Setup:  p prime, p = 1 mod n,  n = 2^mu.  mu_n = unique order-n multiplicative subgroup of F_p.
        eta_b = sum_{y in mu_n} e_p(b*y),   M(n) = max_{b != 0} |eta_b|.
Tower:  mu_2 < mu_4 < ... < mu_n,   eta_b^{(k)} = eta_b^{(k-1)} + eta_{b*om}^{(k-1)}
        where om is a primitive 2^k-th root in F_p (dyadic butterfly).

The Habiro-ring philosophy (Wagner 2510.04782, footnote 1.1):
   the Habiro ring = functions with a Taylor expansion around EVERY root of unity zeta,
   coefficients in Z[zeta]; "treat all roots of unity equally / look at the other roots too".
For us the analogue is: the family k -> eta_b(mu_{2^k}) is a single coherent object as
zeta = generator of mu_{2^k} ranges over 2-power roots of unity.

THE HABIRO HYPOTHESIS being tested:
   Does coherence up the tower FORCE a sup-norm bound that the single level does not?
   Concretely: is there a Habiro-COHERENT worst-frequency family  b_k*  (one b that stays
   near-worst at every level) whose eta grows CONTROLLABLY (sub-BGK, e.g. O(sqrt(n)) not
   O(sqrt(n log p)))?  If the worst frequency at each level is INCOHERENT (jumps around),
   then no tower constraint helps and we collapse to single-level BGK.

Tests:
  (T1) compute M(n) at each level k, and the argmax frequency set.
  (T2) coherence of the worst frequency: track the level-k argmax b_k*, push it down via
       the butterfly (b -> b and b -> b*om), see if a SINGLE b can be near-worst at all levels.
  (T3) "coherent worst family" growth: for the b that is worst at the TOP level, trace
       |eta_b^{(k)}| down the tower.  Does it grow like sqrt(n) (Habiro-tame) or carry the
       full sqrt(n log p) amplification?
  (T4) butterfly amplification per step: |eta^{(k)}| / max(|eta_b^{(k-1)}|,|eta_{bom}^{(k-1)}|).
       BGK no-go says cross-term can ALIGN giving up to factor 2; Habiro hope = systematic
       sub-2 because the two halves are q-coherent (conjugate Taylor data).
"""
import cmath, math

def find_prime(nmin, n):
    # smallest prime p > nmin with p = 1 mod n
    p = nmin + (n - nmin % n) % n + 1
    while True:
        # ensure p = 1 mod n
        if p % n != 1:
            p += 1; continue
        if all(p % d for d in range(2, int(p**0.5)+1)):
            return p
        p += n

def subgroup(p, n):
    # generator g of F_p^*, then h = g^((p-1)/n) generates mu_n
    # find primitive root
    def is_prim(g):
        seen=set(); x=1
        for _ in range(p-1):
            x=(x*g)%p; seen.add(x)
        return len(seen)==p-1
    g=2
    while not is_prim(g): g+=1
    h=pow(g,(p-1)//n,p)
    S=[]; x=1
    for _ in range(n):
        S.append(x); x=(x*h)%p
    return sorted(set(S)), h

def eta(b, S, p):
    z=0j
    for y in S:
        z+=cmath.exp(2j*math.pi*((b*y)%p)/p)
    return z

def Mn_and_argmax(S, p):
    best=-1; arg=[]
    for b in range(1,p):
        m=abs(eta(b,S,p))
        if m>best+1e-9:
            best=m; arg=[b]
        elif abs(m-best)<1e-6:
            arg.append(b)
    return best, arg

def main():
    print("="*78)
    print("HABIRO-COHERENCE TEST on M(n) = max_b |eta_b(mu_n)|, mu_n = 2-power subgroup")
    print("="*78)
    # Build a tower for a fixed prime p = 1 mod 2^mu (so all sub-subgroups live in F_p).
    mu_top = 5            # n = 32 at top
    n_top = 2**mu_top
    p = find_prime(400, n_top)   # need p reasonably > n to be in the right regime but small enough to brute force
    print(f"p = {p}  (p mod {n_top} = {p % n_top}),  top n = {n_top}")
    # subgroups mu_{2^k} for k=1..mu_top, all inside F_p
    S_top, h_top = subgroup(p, n_top)
    # mu_{2^k} = { h_top^{ (n_top/2^k) * j } }
    towers={}
    for k in range(1, mu_top+1):
        nk=2**k
        step=pow(h_top,(n_top//nk),p)
        Sk=[]; x=1
        for _ in range(nk): Sk.append(x); x=(x*step)%p
        towers[k]=sorted(set(Sk))
        assert len(towers[k])==nk

    print("\n(T1) per-level M(n) and the sqrt(n log p) / sqrt(2 n ln p) ratios:")
    print(f"{'k':>2} {'n':>4} {'M(n)':>9} {'sqrt(n)':>9} {'M/sqrtn':>8} {'M/sqrt(2n ln p)':>16} {'#argmax':>8}")
    argmaxes={}
    for k in range(1,mu_top+1):
        nk=2**k
        M,arg=Mn_and_argmax(towers[k],p)
        argmaxes[k]=set(arg)
        sn=math.sqrt(nk)
        bgk=math.sqrt(2*nk*math.log(p))
        print(f"{k:>2} {nk:>4} {M:>9.4f} {sn:>9.4f} {M/sn:>8.4f} {M/bgk:>16.4f} {len(arg):>8}")

    print("\n(T2) COHERENCE of the worst frequency across the tower.")
    print("    Butterfly pushes level-k freq b to level-(k+1) candidates {b, b*om_inv-ish}.")
    print("    Question: is a single b near-worst at EVERY level? (Habiro coherence)")
    # For each b in 1..p-1, record its NORMALIZED rank-quality at each level: |eta_b^{(k)}|/M_k
    Mk={}
    for k in range(1,mu_top+1):
        Mk[k]=max(abs(eta(b,towers[k],p)) for b in range(1,p))
    # find b maximizing the MINIMUM over k of |eta_b^{(k)}|/M_k  (the most coherent worst family)
    best_b=None; best_minq=-1; profile=None
    for b in range(1,p):
        qs=[abs(eta(b,towers[k],p))/Mk[k] for k in range(1,mu_top+1)]
        mq=min(qs)
        if mq>best_minq:
            best_minq=mq; best_b=b; profile=qs
    print(f"    most-coherent-worst b* = {best_b}, min over levels of |eta_b|/M_k = {best_minq:.4f}")
    print(f"    its per-level quality |eta_b*^(k)|/M_k: " +
          " ".join(f"k{k}={profile[k-1]:.3f}" for k in range(1,mu_top+1)))

    print("\n(T3) growth of the TOP-worst frequency traced DOWN the tower:")
    Mtop,argtop=Mn_and_argmax(towers[mu_top],p)
    btop=argtop[0]
    print(f"    top worst b = {btop}")
    print(f"{'k':>2} {'n':>4} {'|eta_b(k)|':>11} {'/sqrt(n)':>9} {'/M_k':>7}")
    for k in range(1,mu_top+1):
        nk=2**k
        v=abs(eta(btop,towers[k],p))
        print(f"{k:>2} {nk:>4} {v:>11.4f} {v/math.sqrt(nk):>9.4f} {v/Mk[k]:>7.4f}")

    print("\n(T4) per-step butterfly amplification  |eta^(k)| / max(|halves|), at the top-worst b:")
    print("     (Habiro hope: systematically < 2; BGK no-go: can hit ~2 when halves align)")
    # eta_b^{(k)} = eta_b^{(k-1)} + eta_{b*om}^{(k-1)}, om primitive 2^k-th root.
    # half-subgroup of mu_{2^k} is mu_{2^{k-1}}; the dilate is om * mu_{2^{k-1}}.
    amps=[]
    for k in range(2,mu_top+1):
        nk=2**k
        # om = a primitive 2^k-th root: generator of mu_{2^k}
        # mu_{2^{k-1}} = towers[k-1]; om*mu_{2^{k-1}} = the other coset
        H=towers[k-1]
        # pick om in mu_{2^k} not in mu_{2^{k-1}}
        om=[y for y in towers[k] if y not in set(H)][0]
        a=eta(btop,H,p)
        bb=sum(cmath.exp(2j*math.pi*((btop*(om*y%p))%p)/p) for y in H)
        full=a+bb
        amp=abs(full)/max(abs(a),abs(bb),1e-12)
        amps.append(amp)
        print(f"    k={k}: |eta|={abs(full):.4f}  |halfA|={abs(a):.4f} |halfB|={abs(bb):.4f}  amp={amp:.4f}")
    print(f"    mean per-step amp = {sum(amps)/len(amps):.4f}  (2.0 = full alignment / no Habiro gain)")

    print("\nVERDICT heuristic:")
    print(" - If (T2) best_minq is close to 1 and (T3) shows the top-worst b is near-worst at")
    print("   ALL levels with growth ~ sqrt(n)*const  => Habiro coherence MIGHT give a tame law.")
    print(" - If best_minq is small / argmax sets disjoint across levels / amp ~ 2  => the worst")
    print("   frequency is INCOHERENT up the tower; no Habiro constraint; collapses to BGK.")

if __name__=="__main__":
    main()
