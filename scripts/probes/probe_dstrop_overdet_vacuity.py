#!/usr/bin/env python3
"""
probe_dstrop_overdet_vacuity.py (#444)

The log-concavity probe found total #bad == C(n/2, w/2) EXACTLY at every w, i.e.
the over-determined p_3 constraint added NOTHING beyond the p_1 antipodal-closure.
That is the load-bearing observation. Test it directly and at higher t:

  (1) Is every p_1 char-0 zero (antipodal-closed S, n=2^mu) automatically a
      p_3 char-0 zero?  (-> p_3 vacuous given p_1)
  (2) More generally for any ODD power p_j (gcd(j,n)=1): does antipodal-closure
      of S force antipodal-closure of {j*a mod n}?  YES iff (a -> j*a) commutes
      with antipodal shift +n/2, which it ALWAYS does: j*(a+n/2) = j*a + j*n/2,
      and j odd => j*n/2 == n/2 mod n. So {j*a} is antipodal-closed whenever S is.
      => ALL odd-power constraints are SIMULTANEOUSLY vacuous given p_1.
  (3) Does ANY constraint cut the count? Test EVEN powers p_2, p_4 (gcd>1): these
      can be non-vacuous. Compute the genuine over-det count with an even power.
  (4) Conclusion for delta*: the char-0 over-det far-line incidence on ODD readouts
      = the SINGLE antipodal-closure count C(n/2,w/2). This is exactly the
      coset-union / orbit-count object already in-tree (SeedCensusDyadicChain:
      binding configs = 2-power coset-unions). NEW-HANDLE vs reduces-to-orbit?
"""
import itertools, math

def antipodal_closed(S, n):
    h = n // 2
    Sset = set(S)
    return all(((a + h) % n) in Sset for a in Sset)

def pj_char0_zero(S, j, n):
    img = [(j * a) % n for a in S]
    return antipodal_closed(img, n)

print("=== (1)+(2) ODD powers vacuous given p_1 (antipodal closure)? ===")
for n in (8, 16, 32):
    h = n // 2
    allok = True
    counterex = None
    for w in range(2, h + 1, 2):
        for S in itertools.combinations(range(n), w):
            if antipodal_closed(S, n):  # p_1 zero
                for j in (3, 5, 7, 9, 11, 13, 15):
                    if math.gcd(j, n) == 1:
                        if not pj_char0_zero(S, j, n):
                            allok = False
                            counterex = (w, S, j)
                            break
            if counterex:
                break
        if counterex:
            break
    print(f"  n={n}: every antipodal-closed S is also p_j-zero for all odd j coprime to n? "
          f"{allok}" + (f"  COUNTEREX={counterex}" if counterex else ""))

print("\n=== (3) does an EVEN power p_2 cut the count (non-vacuous over-det)? ===")
for n in (16, 32):
    h = n // 2
    for w in (2, 4, 6, 8):
        p1cnt = 0
        p1p2cnt = 0
        for S in itertools.combinations(range(n), w):
            if antipodal_closed(S, n):
                p1cnt += 1
                if pj_char0_zero(S, 2, n):
                    p1p2cnt += 1
        print(f"  n={n} w={w}: #p1-zero={p1cnt}  #(p1 AND p2-zero)={p1p2cnt}  "
              f"C(n/2,w/2)={math.comb(h, w//2)}  p2 cuts? {p1p2cnt < p1cnt}")

print("""
INTERPRETATION:
 (2) PROVES (elementarily): for n=2^mu, j odd => j*(n/2)=n/2 mod n, so multiplication
     by any odd j is antipodal-equivariant; hence p_j char-0 vanishing == p_1 char-0
     vanishing for EVERY odd readout simultaneously. The far-line readouts p_1,p_3,...
     are all ODD powers => the OVER-DETERMINED system on a 2-power subgroup COLLAPSES
     to the SINGLE p_1 antipodal-closure constraint. #bad = C(n/2, w/2) exactly.
 => The over-det char-0 count is NOT volume-bounded by a tropical/matroid argument;
    it is EXACTLY the antipodal-closure (2-power coset-union) count, which is the
    SAME orbit-count object already formalized (SeedCensusDyadicChain coset-union /
    OrbitCountCrossingLaw |B|=N*S). REDUCES-TO-ORBIT-COUNT, not a new handle.
""")
