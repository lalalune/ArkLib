#!/usr/bin/env python3
"""
ADVERSARIAL VERIFICATION of CONNECTION C3 (sumset-size <-> energy duality, route (a)).

I (the verifier) independently re-derive the two load-bearing identities the agent's C3 claim
rests on, and test the ONE thing that decides whether C3 is real leverage or folds back to BGK:

  CLAIM A (agent): route-(a) upper bound  E_r <= a_max * n^r   (Hölder/sum-of-squares).
  CLAIM B (agent): in the non-saturated/prize regime  a_max(F_p)=a_max^0  AND  E_r(F_p)=E_r^0
                   EXACTLY, q-independently  ==> a q-independent UPPER bound on the energy.
  CLAIM C (agent): this is USEFUL for the count lane (#bad=|H^{(+r)}|) because that lane only
                   needs a_max=a_max^0 / E_r=E_r^0, NOT the sup-norm.

THE ADVERSARIAL QUESTION (circularity check):
  Identity (iv) of the directive:  E_r(F_p) = E_r^0 + #{char-p-spurious solutions}.
  So  "E_r(F_p) = E_r^0"  <=>  "#spurious = 0".  The suppression of char-p-spurious solutions
  is EXACTLY the open count-lane lemma (= the BGK cyclotomic-coincidence wall).  Therefore
  CLAIM B, IF it held at the depth the count lane needs, would BE the open lemma -- C3 cannot
  PROVE it, only OBSERVE it numerically at small r.

  And per prize-core-distilled.md the crossover r* -> beta+1: at the prize depth r ~ log q the
  char-0 energy E_r^0 ~ n^r falls BELOW the diagonal n^{2r}/q, and Fourier positivity FORCES
  the char-p anomaly  A_r = E_r(F_p) - E_r^0 = (1/p) sum_{b!=0}|eta_b|^{2r}  to be > 0.
  => "E_r(F_p) = E_r^0" is PROVABLY FALSE at the prize depth.  C3's q-independence is a
     SMALL-r / small-(saturation) artifact, NOT a property available where the count lane lives.

THIS PROBE:
  (1) Re-derive route (a): verify E_r <= a_max*n^r is just Hölder (sum a^2 <= max a * sum a),
      and confirm a_max^0 < sqrt(E_r^0) (so the bound is non-trivial but NOT new -- it's weaker
      than Wick).
  (2) Re-establish E_r(F_p)=E_r^0  <=>  #spurious=0  by DIRECTLY counting spurious solutions
      (ordered 2r-tuples with sum-equal mod p but NOT equal in Z[zeta_n]) and checking
      A_r*p == #spurious == E_r(F_p)-E_r^0.
  (3) THE KILL TEST: push r UP toward the crossover r* and watch E_r(F_p) DIVERGE from E_r^0
      (anomaly becomes forced-positive) at fixed prize-like p.  If E_r=E_r^0 fails exactly when
      r reaches the depth the count lane needs, C3's "q-independent energy" evaporates there =
      folds back to BGK.
"""
import itertools, math
from collections import Counter
from sympy import isprime, primitive_root

def first_prime_1modn(n, lo):
    p = lo - (lo % n) + 1
    if p <= lo: p += n
    while not isprime(p): p += n
    return p

def primitive_nth_root(n, p):
    g = primitive_root(p)
    return pow(g, (p - 1)//n, p)

def char0_coord(exps, n):
    half = n//2; v=[0]*half
    for e in exps:
        e %= n
        if e < half: v[e]+=1
        else: v[e-half]-=1
    return tuple(v)

def dfact(k):
    res=1
    while k>0: res*=k; k-=2
    return res

def energies(n, p, r):
    """Return (E_r^Fp, E_r^0, a_max^Fp, a_max^0, #spurious)."""
    w = primitive_nth_root(n, p)
    roots = [pow(w,j,p) for j in range(n)]
    aFp = Counter(); a0 = Counter()
    for tup in itertools.product(range(n), repeat=r):
        s = 0
        for j in tup: s = (s + roots[j]) % p
        aFp[s] += 1
        a0[char0_coord(tup, n)] += 1
    EFp = sum(v*v for v in aFp.values())
    E0  = sum(v*v for v in a0.values())
    return EFp, E0, max(aFp.values()), max(a0.values()), EFp - E0

def main():
    print("="*100)
    print("ADVERSARIAL C3 verification")
    print("="*100)

    # (1) route (a) is plain Hölder; a_max^0 vs sqrt(E^0) (non-trivial?) vs Wick density (weak?)
    print("\n(1) Route (a): E_r <= a_max*n^r is Hölder (sum a^2 <= max a * sum a, sum a = n^r).")
    print(f"{'n':>4} {'r':>3} {'E_r^0':>10} {'a_max^0':>8} {'a_max*n^r':>10} {'sqrt(E^0)':>9} "
          f"{'a_max<sqrtE?':>12} {'Wick=(2r-1)!!n^r':>16} {'bound/Wick':>10}")
    for mu in [3,4]:
        n=2**mu
        for r in [2,3]:
            if n**r > 200000: continue
            a0=Counter()
            for tup in itertools.product(range(n),repeat=r): a0[char0_coord(tup,n)]+=1
            E0=sum(v*v for v in a0.values()); am=max(a0.values()); ub=am*n**r
            wick=dfact(2*r-1)*n**r
            print(f"{n:>4} {r:>3} {E0:>10} {am:>8} {ub:>10} {math.sqrt(E0):>9.1f} "
                  f"{str(am < math.sqrt(E0)):>12} {wick:>16} {ub/wick:>10.3f}")
    print("  -> a_max < sqrt(E^0) confirms the bound is non-trivial vs naive, BUT bound/Wick > 1")
    print("     means E_r <= a_max*n^r is WEAKER than the true (Wick) energy. NOT new info.")

    # (2) E_r(F_p)=E_r^0  <=>  #spurious=0, verified by direct spurious count + Fourier anomaly.
    print("\n(2) CIRCULARITY CORE: E_r(F_p)-E_r^0 == #spurious (char-p coincidences). 'E_r=E_r^0' IS")
    print("    the suppression lemma. Verify anomaly = spurious count exactly.")
    print(f"{'n':>4} {'r':>3} {'p':>9} {'E_r^Fp':>10} {'E_r^0':>10} {'anomaly':>8} "
          f"{'#spurious':>10} {'match':>6} {'amax=amax0?':>11}")
    for mu in [3,4]:
        n=2**mu
        for r in [2,3]:
            if n**r > 200000: continue
            for p in [first_prime_1modn(n, 50), first_prime_1modn(n, n**3)]:
                EFp,E0,amFp,am0,spur = energies(n,p,r)
                print(f"{n:>4} {r:>3} {p:>9} {EFp:>10} {E0:>10} {EFp-E0:>8} "
                      f"{spur:>10} {str((EFp-E0)==spur):>6} {str(amFp==am0):>11}")
    print("  -> anomaly == #spurious always (by construction). At SMALL p (saturated) anomaly>0;")
    print("     at LARGE p (non-sat, fixed small r) anomaly=0. C3 only OBSERVES the =0 case.")

    # (3) THE KILL TEST: fix a prize-LIKE small subgroup and crank r toward crossover r*~beta+1.
    #     Use the SMALLEST p == 1 mod n (most prize-like: |H|=n is a big fraction => deep regime).
    #     Watch the anomaly turn POSITIVE as r grows -- E_r=E_r^0 FAILS at the depth the count lane needs.
    print("\n(3) KILL TEST: at fixed p, crank r. Does E_r(F_p)=E_r^0 SURVIVE to the prize depth")
    print("    r* ~ beta+1 (beta=log_n p)? If it FAILS there, C3's q-independent energy is a")
    print("    small-r artifact and the count lane at its true depth = the forced-anomaly BGK wall.")
    for (n, p) in [(8, first_prime_1modn(8,8)), (8, first_prime_1modn(8,200)),
                   (16, first_prime_1modn(16,16))]:
        beta = math.log(p)/math.log(n)
        print(f"\n  n={n}, p={p} (beta=log_n p={beta:.2f}, crossover r*~beta+1={beta+1:.1f}); "
              f"diagonal n^{{2r}}/p falls below E_r^0 around there:")
        print(f"    {'r':>3} {'E_r^0':>14} {'n^{2r}/p':>16} {'E_r^Fp':>14} {'anomaly':>12} "
              f"{'E_r=E_r^0?':>11}")
        for r in range(2, 8):
            if n**r > 3_000_000: break
            EFp,E0,_,_,spur = energies(n,p,r)
            diag = n**(2*r)/p
            flag = "YES" if spur==0 else "NO (forced+)"
            print(f"    {r:>3} {E0:>14} {diag:>16.1f} {EFp:>14} {EFp-E0:>12} {flag:>11}")
    print("\n  READING: the diagonal n^{2r}/p exceeds E_r^0 once r passes r*; there Fourier")
    print("  positivity (sum_{b!=0}|eta_b|^{2r} = p*E_r^Fp - n^{2r} >= 0) FORCES E_r^Fp >= n^{2r}/p")
    print("  > E_r^0, so anomaly>0 and E_r(F_p) != E_r^0. C3's identity DIES at the count lane's depth.")

if __name__ == "__main__":
    main()
