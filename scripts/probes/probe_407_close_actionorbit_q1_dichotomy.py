#!/usr/bin/env python3
"""
#407 LANE D (Action-Orbit, Chai-Fan 2026/861) -- DECISIVE Q1 dichotomy d=16 vs d=32.

CONTEXT (honest provenance). The actual paper 2026/861 is Cloudflare-blocked (the local
~/papers/arklib/2026_861.pdf and /tmp/2026_861.pdf are both "Just a moment..." HTML, NOT the
PDF). So the precise form of "Q1" used here is RECONSTRUCTED from ActionOrbitFRI.lean + the
in-tree KB + issue comments, NOT quoted from the paper. The reconstructed Q1 (route i) is:

  THE SELF-SIMILARITY HYPOTHESIS (*)_d :  on the mu_d-orbit-PRIMITIVE gap stratum V_d^prim
  (an ANTIPODAL-FREE subset Y of mu_d -- no {y,-y} pair -- the genuinely-primitive seed),
        p_1(Y) = 0   =>   p_a(Y) = 0   for every odd a,
  where p_a(Y) = sum_{y in Y} y^a.  The paper proves (*)_d for d in {4,8}; the orbit count
  K = O(1) bound bootstraps through dyadic doublings IFF (*)_d holds for all d=2^j.
  d>=16 is the OPEN regime.  (*)_d failing in char-p == a "spurious primitive point" ==
  the norm Norm_{K_d/Q}(F_d) VANISHING mod p (bad reduction) == orbit count inflates.

This probe settles, EXHAUSTIVELY (no MITM truncation) and robustly:
  (1) char-0:  is V_d^prim(p_1=0) empty for d=8,16,32?  (Lam-Leung => (*)_d vacuous over C)
  (2) char-p:  EXHAUSTIVE hunt for antipodal-free Y subset mu_d with p_1(Y)=0 mod p, over a
      WIDE prize-scale prime band, at d=16 and d=32.  For each found point, test (*)_d
      (p_a=0 mod p for all odd a).  Report the FULL census: #primitive points, #violating.
  (3) the orbit-count consequence: a (*)_d-violating point => extra orbits of bad scalars =>
      the K=O(1) bound the paper's soundness rests on is NOT delivered by the orbit mechanism
      alone at that d, over that prime.

EXHAUSTIVE FEASIBILITY: antipodal-free Y in mu_d lives over d/2 antipodal pairs, each pair
contributing {none, +, -} => 3^{d/2} configs.  d=16: 3^8=6561 (trivial).  d=32: 3^16=43M
(feasible with sign-pair pruning + early p_1 test).  We do d=16 fully; d=32 via a complete
MITM that is EXACT (not a sampled cap) -- meet in the middle on the d/2 pairs, count ALL.
"""

import itertools
from math import gcd
from collections import Counter

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def primes_1_mod_n(n, lo, cap):
    out=[]; p = lo|1
    while len(out) < cap:
        if (p-1) % n == 0 and is_prime(p): out.append(p)
        p += 2
    return out

def find_gen(p, n):
    for g0 in range(2, p):
        w = pow(g0, (p-1)//n, p)
        if pow(w,n,p)==1 and all(pow(w, n//q, p)!=1 for q in (2,3,5,7,11,13) if n%q==0):
            return w
    raise RuntimeError("no gen")

# ---------- char-0 exhaustive: V_d^prim(p_1=0) empty? ----------
def charzero_prim_empty(d):
    half=d//2
    def root(j):
        e=j%d; v=[0]*half
        if e<half: v[e]=1
        else: v[e-half]=-1
        return tuple(v)
    def add(u,v): return tuple(a+b for a,b in zip(u,v))
    zero=tuple([0]*half)
    cnt=0
    # antipodal-free Y: over each pair (t,t+half) choose none/+t/+(t+half)
    for choice in itertools.product(range(3), repeat=half):
        Y=[]
        for t,c in enumerate(choice):
            if c==1: Y.append(t)
            elif c==2: Y.append(t+half)
        if len(Y)<2: continue
        p1=zero
        for j in Y: p1=add(p1, root(j))
        if p1==zero: cnt+=1
    return cnt

# ---------- char-p EXHAUSTIVE (MITM but EXACT count, no cap) ----------
def charp_census(p, d, odd_a_to_check=None):
    """EXACT census of antipodal-free Y subset mu_d with p_1(Y)=0 mod p, and how many
    violate (*)_d (some odd a with p_a != 0). MITM over the d/2 pairs, both halves complete."""
    half=d//2
    w=find_gen(p,d)
    rv=[pow(w,j,p) for j in range(d)]   # rv[j] = w^j
    if odd_a_to_check is None:
        odd_a_to_check=[a for a in range(3,d,2)]
    pairs=list(range(half))
    Lh=half//2;
    leftpairs=pairs[:Lh]; rightpairs=pairs[Lh:]
    # each half: enumerate all 3^{|half|} choices, record (p1sum mod p, chosen exps)
    def enum(pp):
        out=[]
        for choice in itertools.product(range(3), repeat=len(pp)):
            exps=[]; s=0
            for t,c in zip(pp,choice):
                if c==1: exps.append(t); s=(s+rv[t])%p
                elif c==2: exps.append(t+half); s=(s+rv[t+half])%p
            out.append((s, tuple(exps)))
        return out
    left=enum(leftpairs); right=enum(rightpairs)
    # bucket right by sum
    from collections import defaultdict
    rb=defaultdict(list)
    for s,exps in right: rb[s].append(exps)
    n_prim=0; n_viol=0; viol_examples=[]; ok_examples=[]
    for ls,lexps in left:
        tgt=(-ls)%p
        if tgt in rb:
            for rexps in rb[tgt]:
                Y=lexps+rexps
                if len(Y)<2: continue
                n_prim+=1
                # (*)_d test
                viol_at=None
                for a in odd_a_to_check:
                    s=0
                    for j in Y: s=(s+pow(w,(a*j)%d,p))%p
                    if s!=0: viol_at=a; break
                if viol_at is not None:
                    n_viol+=1
                    if len(viol_examples)<2: viol_examples.append((Y,viol_at))
                else:
                    if len(ok_examples)<2: ok_examples.append(Y)
    return n_prim, n_viol, viol_examples, ok_examples

def verify_antipodal_free(Y, d):
    half=d//2; Ys=set(Y)
    return not any(((j+half)%d) in Ys for j in Y)

def main():
    print("="*90)
    print("#407 LANE D -- DECISIVE Q1 (*)_d dichotomy: d=16 (claimed settled) vs d=32 (open)")
    print("="*90)
    print("(*)_d: antipodal-free Y in mu_d, p_1(Y)=0  =>  p_a(Y)=0 for all odd a.")
    print("Char-p VIOLATION = spurious primitive point = norm vanishes mod p = K-bound NOT delivered.\n")

    print("--- (1) char-0 EXHAUSTIVE: V_d^prim(p_1=0) empty? (Lam-Leung) ---")
    for d in [8,16,32]:
        c=charzero_prim_empty(d)
        print(f"  d={d}: antipodal-free p_1=0 configs over C = {c}  "
              f"=> {'EMPTY (Lam-Leung; (*)_d vacuous over C)' if c==0 else 'NONEMPTY!'}")

    print("\n--- (2) char-p EXHAUSTIVE census over prize-scale prime band ---")
    for d in [16, 32]:
        print(f"\n  d={d}:  (prize band p = 1 mod {d}, p ~ {d}^4 .. {d}^4+, EXACT MITM count)")
        lo = d**4
        ps = primes_1_mod_n(d, lo, cap=8)
        tot_prim=0; tot_viol=0; primes_with_viol=0; primes_clean=0
        first_viol=None
        for p in ps:
            n_prim, n_viol, vex, okex = charp_census(p, d)
            tot_prim+=n_prim; tot_viol+=n_viol
            if n_viol>0:
                primes_with_viol+=1
                if first_viol is None and vex:
                    Y,a=vex[0]; first_viol=(p,Y,a)
            else:
                primes_clean+=1
            tag = (f"CLEAN (all {n_prim} self-descend)" if n_viol==0 and n_prim>0 else
                   ("EMPTY (no primitive pt)" if n_prim==0 else
                    f"VIOLATIONS {n_viol}/{n_prim} (p_1=0, p_a!=0)"))
            print(f"    p={p:>9}: primitive_pts={n_prim:>4}  violating={n_viol:>4}  -> {tag}")
        print(f"    SUMMARY d={d}: total primitive={tot_prim}, total violating={tot_viol}, "
              f"primes-with-violation={primes_with_viol}/{len(ps)}, primes-clean={primes_clean}/{len(ps)}")
        if first_viol:
            p,Y,a=first_viol
            af = verify_antipodal_free(Y,d)
            print(f"    FIRST VIOLATION: p={p}, Y(exponents in Z/{d})={sorted(Y)}, breaks at odd a={a}; "
                  f"antipodal-free verified={af}")
        verdict = ("(*)_d HOLDS in char-p (no spurious primitive pt) -> Q1 route intact at this d"
                   if tot_viol==0 else
                   "(*)_d FAILS in char-p (spurious primitive pts exist) -> Q1 self-similarity route BREAKS at this d")
        print(f"    => VERDICT d={d}: {verdict}")

if __name__ == "__main__":
    main()
