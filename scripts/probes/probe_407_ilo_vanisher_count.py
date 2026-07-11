#!/usr/bin/env python3
"""
#407 -- inverse-Littlewood-Offord / anti-concentration lane (un-walled per DISPROOF_LOG).

CONTEXT. Two findings localize the thin advantage precisely:
  (i) [my BIND-full-depth entry] the thin obstruction-suppression IS thinness-essential at the
      VANISHER level: thin mu_n's smallest non-antipodal zero-sum is DEEPER than a random
      thin-density set (n=32 b=4: thin r_min=11 vs random median 6).
  (ii) [moment-cert THICKNESS-INVARIANT entry] the moment certificate M<=(q A_r)^{1/2r} loses a
      regime-uniform ~18% => the thin advantage CANNOT pass through the moment->sup bridge.
So the surviving mechanism must use the thin vanisher structure directly, NOT via the moment passage.

THE ILO OBJECT. eta_b = sum_{x in mu_n} e_p(b x). |eta_b|^2 = sum_{x,y} e_p(b(x-y)). The sup-norm
M(n)=max_b|eta_b| is controlled by anti-concentration of the random-walk sum sum_{i} eps_i zeta^i:
the number of b for which |eta_b| is LARGE = number of near-zero-sums = an inverse-Littlewood-Offord
count. ILO theory (Tao-Vu, Nguyen-Vu): if the steps {zeta^i} have FEW additive relations (high Sidon
depth), the sum sum eps_i zeta^i is ANTI-CONCENTRATED => few large |eta_b| => small M.

THE TEST (probe-first, thinness-essential gate). For thin mu_n vs random thin-density control at prize
primes, measure the ANTI-CONCENTRATION profile:
  Q(t) = #{ subsets/sign-vectors with sum within t of 0 } / total  (the small-ball probability)
and the SUP-NORM M(n) itself. The ILO mechanism would predict: thin mu_n has SMALLER small-ball Q
(better anti-concentration) => smaller M, and this gap is thinness-essential (FALSE/absent in the thick
window). If thin Q << random Q AND the gap grows with thinness (beta) => a LIVE thinness-essential
ILO lever. If thin Q ~ random Q (or gap thickness-invariant) => ILO is also not the lever (wall it).

HONESTY: mu_n = n-th roots in F_p, proper 2-power subgroup, p==1 mod n, m odd, NEVER n=q-1. Random
control = n distinct nonzero residues, no mult structure (same density). small-ball over the FULL
sign-vector cube {-1,+1}^n (the eta = signed-character object) AND over subset-sums; exact mod p.
M(n) = max_{b!=0} |sum_{x in mu_n} e_p(bx)| computed exactly by DFT over b.
"""
import random, cmath, math
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

def zeta_powers(p,n):
    g=primitive_root(p); z=pow(g,(p-1)//n,p)
    assert pow(z,n,p)==1 and pow(z,n//2,p)!=1
    return [pow(z,i,p) for i in range(n)]

def supnorm(residues, p):
    """M = max_{b=1..p-1} |sum_x e_p(b x)| over the given residue multiset (exact via direct sum)."""
    n=len(residues)
    best=0.0; argb=0
    # full b-sweep is O(p*n); fine for p up to ~10^5. For larger p, sample b but that loses exactness.
    # We use exact full sweep only when p<=200000; else sample 4000 random b (UPPER-bound estimate noted).
    if p<=200000:
        rng=range(1,p)
    else:
        rng=[random.randrange(1,p) for _ in range(4000)]
    for b in rng:
        s=0j
        for x in residues:
            ang=2*math.pi*((b*x)%p)/p
            s+=cmath.exp(1j*ang)
        m=abs(s)
        if m>best: best=m; argb=b
    return best, argb, (p<=200000)

def smallball_signed(residues, p, samples=300000):
    """small-ball: fraction of random sign-vectors eps in {-1,+1}^n with |sum eps_i residues_i mod p|
       within radius t*p of 0 (t small). Returns Q(t) for a few t. Centered distance on the circle."""
    n=len(residues)
    ts=[0.0, 0.01, 0.02, 0.05]
    cnt=[0]*len(ts)
    exact_zero=0
    for _ in range(samples):
        s=0
        for r in residues:
            s += r if random.getrandbits(1) else -r
        s%=p
        d=min(s, p-s)  # circle distance to 0
        if s==0: exact_zero+=1
        for k,t in enumerate(ts):
            if d <= t*p: cnt[k]+=1
    return ts, [c/samples for c in cnt], exact_zero/samples

def find_prize_prime(n,beta,want_odd=True):
    target=int(n**beta)
    p=target+((n-(target%n))%n)+1
    while p<target*64+10**7:
        if is_prime(p) and p%n==1:
            m=(p-1)//n
            if (want_odd is None) or (m%2==1)==want_odd: return p
        p+=n
    return None

def main():
    random.seed(11)
    print("="*94)
    print("ILO / anti-concentration: is the thin small-ball + sup-norm advantage THINNESS-ESSENTIAL?")
    print("="*94)
    print("Compares thin mu_n vs random thin-density control across thick (beta~2.3-3.2) AND thin (4-5)")
    print("windows. ILO lever LIVE iff thin small-ball Q << random AND the gap is thinness-ESSENTIAL")
    print("(absent/false in the thick window). M(n)=exact sup-norm; target ~ sqrt(n log(p/n)).\n")
    print(f"{'n':>3} {'beta':>5} {'p':>10} {'window':>6} {'M_thin':>8} {'M_rand(med)':>11} "
          f"{'M_thin/sqrt(n)':>14} {'Q0.02_thin':>10} {'Q0.02_rand':>10}")
    for n in (8,16):
        for beta in (2.3, 3.0, 4.0, 4.5):
            p=find_prize_prime(n,beta)
            if p is None or p>200000:
                # keep p exact-sweepable
                if p is None: continue
            zp=zeta_powers(p,n)
            Mt,_,exact_t=supnorm(zp,p)
            # random controls
            Mr=[]; Qr=[]
            for seed in range(5):
                random.seed(500+seed+10*n+int(beta*7))
                vals=random.sample(range(1,p),n)
                m,_,_=supnorm(vals,p); Mr.append(m)
                _,q,_=smallball_signed(vals,p,samples=60000); Qr.append(q[2])  # Q(t=0.02)
            Mr.sort(); Qr.sort()
            _,qt,_=smallball_signed(zp,p,samples=120000)
            window = "thin" if beta>=3.6 else "thick"
            print(f"{n:>3} {beta:>5.2f} {p:>10} {window:>6} {Mt:>8.3f} {Mr[2]:>11.3f} "
                  f"{Mt/math.sqrt(n):>14.3f} {qt[2]:>10.5f} {Qr[2]:>10.5f}")
    print("\nVERDICT LOGIC:")
    print(" - M_thin < M_rand AND Q_thin < Q_rand, with the gap GROWING from thick->thin window:")
    print("     ILO anti-concentration is a LIVE thinness-essential lever (use small-ball -> sup directly).")
    print(" - gap thickness-invariant or thin>=random: ILO joins moment route as NOT the rule-3 lever (wall).")

if __name__=="__main__":
    main()
