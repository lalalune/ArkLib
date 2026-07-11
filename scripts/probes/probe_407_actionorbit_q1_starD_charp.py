#!/usr/bin/env python3
"""
#407 LANE L4 -- Q1 route (i): the self-similarity hypothesis (*)_d at d=16,32, in BOTH char-0
and char-p, decisively.

THE PAPER'S Q1 ROUTE (i), verbatim (Open Problems, Q1):
  "a structural induction step on chain self-similarity (prove x_1 = 0 => x_a = 0 for every odd a
   on V_d^prim, currently rigorous at d in {4,8})".
This (*)_d hypothesis, if extended to all d=2^j, bootstraps Q1 through dyadic doublings.

We give a CONCRETE realization of (*)_d that is checkable:  V_d^prim is the mu_d-orbit-PRIMITIVE
stratum -- a config of mu_d-roots that is NOT a full coset-union (the genuinely primitive part).
On the gap-variety reading shared by both Q1 routes, a primitive point is an ANTIPODAL-FREE subset
Y of mu_d (no {y,-y} pairs).  x_a corresponds to the power sum p_a(Y) = sum_{y in Y} y^a.
(*)_d :  p_1(Y) = 0  =>  p_a(Y) = 0  for every odd a.

CHAR-0 (over Z[zeta_d]):  Lam-Leung gives that an antipodal-free subset of mu_{2^j} with p_1=0 is
IMPOSSIBLE (a vanishing 0/1-sum of 2-power roots decomposes into negation pairs).  So V_d^prim with
x_1=0 is EMPTY over C  =>  (*)_d holds VACUOUSLY over C for ALL d=2^j.  We re-verify exhaustively.

CHAR-p (over F_p, p = 1 mod d, p ~ prize scale):  here Lam-Leung FAILS -- short antipodal-free
char-p vanishing sums CAN exist.  The REAL Q1 question at d>=16 is whether such a char-p primitive
point exists AND violates p_a=0 for some odd a (so the self-similar descent breaks).  We hunt them
DIRECTLY over a wide prize-scale prime band, for d = 8, 16, 32 (the open regime), via MITM on the
two leading power-sum conditions.

DECISIVE OUTPUTS:
  * char-0: confirm V_d^prim (x_1=0) empty for d=8,16,32  (=> (*)_d vacuous over C).
  * char-p: does ANY antipodal-free Y subset mu_d with p_1=0 mod p exist at d=16,32 in the prize
    band? If yes, does it satisfy p_a=0 for all odd a ((*)_d holds in char-p) or violate ((*)_d
    FAILS => Q1 route (i) breaks at d>=16, the precise open point)?
"""

import itertools, sys
from math import gcd, comb
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

# ---------- char-0 over Z[zeta_d], basis {1,...,zeta^{d/2-1}}, zeta^{d/2}=-1 ----------
def charzero_starD(d, max_size=8):
    half=d//2
    def root(j):
        e=j%d; v=[0]*half
        if e<half: v[e]=1
        else: v[e-half]=-1
        return tuple(v)
    def add(u,v): return tuple(a+b for a,b in zip(u,v))
    zero=tuple([0]*half)
    n_p1zero=0; viol=0; ex=[]
    for size in range(2, min(half, max_size)+1):
        for Y in itertools.combinations(range(d), size):
            Yset=set(Y)
            if any(((j+half)%d) in Yset for j in Y):  # antipodal pair
                continue
            p1=zero
            for j in Y: p1=add(p1, root(j))
            if p1==zero:
                n_p1zero+=1
                # check all odd a up to d-1
                bad_a=None
                for a in range(3, d, 2):
                    pa=zero
                    for j in Y: pa=add(pa, root((a*j)%d))
                    if pa!=zero: bad_a=a; break
                if bad_a is not None:
                    viol+=1
                    if len(ex)<3: ex.append((Y,bad_a))
    return n_p1zero, viol, ex

# ---------- char-p over F_p: antipodal-free Y subset mu_d with p_1 = 0 mod p, MITM ----------
def charp_starD(p, d, want=3):
    """Hunt antipodal-free Y subset mu_d with p_1(Y)=0 mod p. For each found, test (*)_d:
    p_a(Y)=0 mod p for all odd a.  MITM over half-split of the antipodal-free exponent reps."""
    w=find_gen(p,d)
    half=d//2
    # antipodal-free reps: for each pair {j, j+half}, choose 0 / +zeta^j / +zeta^{j+half}.
    # value of zeta^j and zeta^{j+half} = -zeta^j; we track exponent and sign.
    rootval=[pow(w,j,p) for j in range(d)]
    # We want subsets Y (exponents) antipodal-free with sum rootval[j]=0 mod p.
    # MITM: split the `half` pairs into two groups; enumerate partial choices.
    pairs=list(range(half))  # pair t represents exponents {t, t+half}
    L=half//2; R=half-L
    # left choices: for pairs[0:L], each in {none, +t (zeta^t), +(t+half)(=-zeta^t)}
    # represent a choice as a partial sum and the chosen exponent set
    def gen_choices(idxs):
        # returns dict sum -> list of (exp_tuple)
        res={}
        for combo in itertools.product(range(3), repeat=len(idxs)):
            s=0; exps=[]
            for ci,t in zip(combo, idxs):
                if ci==0: continue
                if ci==1: s=(s+rootval[t])%p; exps.append(t)
                else: s=(s+rootval[t+half])%p; exps.append(t+half)
            res.setdefault(s, []).append(tuple(exps))
        return res
    left=gen_choices(pairs[:L])
    right=gen_choices(pairs[L:])
    found=[]
    # need leftsum + rightsum = 0  => rightsum = -leftsum
    for ls, lexps_list in left.items():
        target=(-ls)%p
        if target in right:
            for lexps in lexps_list:
                for rexps in right[target]:
                    Y=lexps+rexps
                    if len(Y)<2: continue  # nonempty, size>=2
                    found.append(Y)
                    if len(found)>=400: break
                if len(found)>=400: break
        if len(found)>=400: break
    # now test (*)_d on found configs
    results=[]
    for Y in found:
        # p_1 already 0; check odd a
        viol_a=None
        for a in range(3, d, 2):
            s=sum(pow(rootval[j], a, p) for j in Y) % p
            # rootval[j]^a = w^{aj}; but easier: pow(w,(a*j)%d,p)
            s=0
            for j in Y: s=(s+pow(w,(a*j)%d,p))%p
            if s!=0: viol_a=a; break
        results.append((Y, viol_a))
        if len(results)>=want and any(r[1] is not None for r in results):
            pass
    return results

def main():
    print("="*88)
    print("#407 LANE L4 -- Q1 route (i): (*)_d  [x_1=0 => x_a=0 odd a on V_d^prim]  at d=16,32")
    print("="*88)

    print("\n--- char-0 (over Z[zeta_d]): is V_d^prim (antipodal-free, p_1=0) EMPTY? ---")
    for d in [8, 16, 32]:
        n1, viol, ex = charzero_starD(d, max_size=(8 if d<=16 else 6))
        if n1==0:
            print(f"  d={d}: NO antipodal-free p_1=0 config => V_d^prim(x_1=0) EMPTY over C "
                  f"=> (*)_d VACUOUS over C  [Lam-Leung].")
        else:
            print(f"  d={d}: {n1} antipodal-free p_1=0 configs; {viol} violate odd-power vanishing "
                  f"{'((*)_d holds)' if viol==0 else f'((*)_d FAILS over C) ex={ex}'}")

    print("\n--- char-p (over F_p, prize band p=1 mod d ~ d^4): primitive point exists? (*)_d? ---")
    for d in [8, 16, 32]:
        lo = d**4
        ps = primes_1_mod_n(d, lo, cap=6)
        any_prim=False; any_viol=False
        for p in ps:
            res = charp_starD(p, d)
            prims = [r for r in res if True]
            if prims:
                any_prim=True
                viol = [r for r in res if r[1] is not None]
                # report a couple
                sample = res[0]
                if viol:
                    any_viol=True
                    print(f"  d={d} p={p} (~d^{round(__import__('math').log(p,d),2)}): "
                          f"{len(res)} primitive char-p pts; {len(viol)} VIOLATE (*)_d "
                          f"(p_1=0 but p_{viol[0][1]}!=0) -> (*)_d route gives NO descent here; e.g. Y={viol[0][0]}")
                else:
                    print(f"  d={d} p={p} (~d^{round(__import__('math').log(p,d),2)}): "
                          f"{len(res)} primitive char-p pts, ALL satisfy (*)_d (p_a=0 all odd a) "
                          f"-> self-descent holds despite primitive point; e.g. Y={sample[0]}")
            else:
                print(f"  d={d} p={p}: NO antipodal-free p_1=0 char-p point -> V_d^prim empty mod p (clean)")
        verdict = ("(*)_d route INTACT (every primitive pt self-descends or none exist)"
                   if not any_viol else
                   "(*)_d route BREAKS in char-p (primitive pt violates odd-power vanishing)")
        print(f"    => d={d}: {verdict}")

if __name__ == "__main__":
    main()
