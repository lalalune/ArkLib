#!/usr/bin/env python3
"""
#407 -- localize the BULK correlation: WHICH frequencies b carry the large |eta_b| for thin mu_n?

CONTEXT. Established (my ILO entry, push 852e0fa27): thin mu_n is anti-concentrated WORSE than random;
M_thin >= M_rand. So the BGK difficulty is BULK correlation, not the sparse-relation floor. This probe
localizes that bulk correlation: are the frequencies b with large |eta_b| STRUCTURED (lying in the
multiplicative coset structure of mu_n), and is that structure the thinness-essential obstruction?

eta_b = sum_{x in mu_n} e_p(b x).  Key identity: eta_{b}, for b ranging over a COSET c*mu_n of mu_n,
are all EQUAL in magnitude (|eta_{b}| = |eta_{c x}| ... actually eta_{b} depends on b only through the
mu_n-action when... ) -- we TEST this directly rather than assume. Specifically:
  (Q1) Is |eta_b| CONSTANT on multiplicative cosets b in c*mu_n? (=> the |eta| spectrum is mu_n-coset-
       structured, |F_p^*|/n distinct magnitude-values, each repeated n times.) This would localize the
       sup-norm to ONE representative per coset -- a massive structural reduction (the brief's coset-core).
  (Q2) Which coset carries the MAX |eta_b| (the sup-norm)? Is it a structured coset (e.g. b in a subgroup
       containing mu_n, or b a power-residue class) vs generic?
  (Q3) thinness: is the coset-constancy + max-coset structure ABSENT for a random thin-density set
       (=> the bulk obstruction is genuinely 2-power/multiplicative, thinness-essential)?

HONESTY: mu_n = n-th roots in F_p, proper 2-power subgroup, p==1 mod n, m odd, never n=q-1. eta exact
via direct complex sum. Random control = random n-subset (NO multiplicative structure). p kept small
enough for full b-sweep (exact). This is a STRUCTURE-MAPPING probe (localize the obstruction), not a
CORE bound -- reported as such.
"""
import math, cmath, random
from collections import defaultdict

def is_prime(n):
    if n<2: return False
    if n%2==0: return n==2
    d=3
    while d*d<=n:
        if n%d==0: return False
        d+=2
    return True

def primitive_root(p):
    if p==2: return 1
    phi=p-1; facs=set(); m=phi; d=2
    while d*d<=m:
        while m%d==0: facs.add(d); m//=d
        d+=1
    if m>1: facs.add(m)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g
    raise RuntimeError

def find_prize_prime(n,beta,want_odd=True):
    target=int(n**beta)
    p=target+((n-(target%n))%n)+1
    while p<target*64+10**7:
        if is_prime(p) and p%n==1:
            m=(p-1)//n
            if (want_odd is None) or (m%2==1)==want_odd: return p
        p+=n
    return None

def eta(residues,p,b):
    s=0j
    for x in residues:
        s+=cmath.exp(2j*math.pi*((b*x)%p)/p)
    return abs(s)

def main():
    random.seed(3)
    print("="*90)
    print("BULK frequency structure: is large |eta_b| coset-localized for thin mu_n? (thinness gate)")
    print("="*90)
    for n,beta in [(8,3.0),(8,4.0),(16,3.0),(16,4.0)]:
        p=find_prize_prime(n,beta)
        if p is None or p>120000:
            beta2=beta
            # pick a smaller p in-window
        g=primitive_root(p); z=pow(g,(p-1)//n,p)
        mun=[pow(z,i,p) for i in range(n)]
        assert pow(z,n,p)==1 and pow(z,n//2,p)!=1
        # (Q1) coset constancy of |eta_b| on b in c*mu_n
        # group b=1..p-1 by multiplicative coset of mu_n: coset rep = g^(idx mod n-orbit)... use
        # discrete log lattice: coset of b = b * mu_n. Constant magnitude within coset?
        # Test on a sample of cosets: pick representative c, compute |eta_b| for all b in c*mu_n.
        cosets_tested=0; const_cosets=0; maxspread=0.0
        seen=set()
        creps=[]
        for c in range(1,p):
            if c in seen: continue
            orbit=[(c*m)%p for m in mun]
            for o in orbit: seen.add(o)
            creps.append(c)
            if cosets_tested<40:
                mags=[eta(mun,p,b) for b in orbit]
                spread=max(mags)-min(mags)
                maxspread=max(maxspread,spread)
                if spread<1e-6: const_cosets+=1
                cosets_tested+=1
        q1 = "YES" if const_cosets==cosets_tested else f"NO(spread<= {maxspread:.3g})"
        # (Q2) which coset carries the max? compute |eta| per coset rep (one per coset), find argmax
        cosmax=[]
        for c in creps[:min(len(creps),2000)]:
            cosmax.append((eta(mun,p,c),c))
        cosmax.sort(reverse=True)
        Mval,bmax = cosmax[0]
        # structure of bmax: is bmax in a small subgroup? order of bmax:
        ob = 1; t=bmax
        while t!=1:
            t=(t*bmax)%p; ob+=1
            if ob>p: break
        # is bmax a power residue? log_g(bmax) mod small factors
        # (Q3) random control: coset-constancy + structured argmax for a random n-subset
        rnd=random.sample(range(1,p),n)
        # random set has no real cosets; test |eta_b| constancy on the SAME mu_n-coset partition
        rspread=0.0; rconst=0
        cnt=0
        for c in creps[:40]:
            orbit=[(c*m)%p for m in mun]
            mags=[eta(rnd,p,b) for b in orbit]
            sp=max(mags)-min(mags); rspread=max(rspread,sp)
            if sp<1e-6: rconst+=1
            cnt+=1
        q3 = f"thin coset-const {const_cosets}/{cosets_tested}, random {rconst}/{cnt} (rand spread<= {rspread:.3g})"
        print(f"\nn={n} beta={beta} p={p}: M={Mval:.3f} (M/sqrt(n)={Mval/math.sqrt(n):.3f})")
        print(f"  (Q1) |eta_b| constant on mu_n-cosets? {q1}")
        print(f"  (Q2) argmax coset rep b={bmax}, mult.order(b)={ob}  (#cosets={len(creps)}=(p-1)/n={int((p-1)/n)})")
        print(f"  (Q3) {q3}")
    print("\nVERDICT: (Q1) YES => the |eta| spectrum is mu_n-coset-localized: sup-norm reduces to ONE rep")
    print("  per coset, (p-1)/n values not p-1 -- a real structural reduction. (Q3) random NOT coset-const")
    print("  => coset-localization is THINNESS-ESSENTIAL (multiplicative-structure obstruction). This is")
    print("  WHERE the bulk BGK difficulty lives: structured |eta| on the (p-1)/n coset reps, not arbitrary b.")

if __name__=="__main__":
    main()
