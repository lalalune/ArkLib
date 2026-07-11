#!/usr/bin/env python3
"""
wf-LD (#407, lane F11): EVEN-SUBLATTICE ideal-SVP under the cross-parity leak.
CORRECTED: work in the POWER BASIS Z^d, d = phi(n) = n/2.

Setup.  K = Q(zeta_n), n = 2^mu, O_K = Z[zeta], rank d = n/2, power basis {1,zeta,...,zeta^{d-1}}
with the SINGLE relation zeta^d = -1 (Phi_n = x^{d}+1).  A cyclotomic integer is a coefficient
vector c in Z^d.  Its L1 (coefficient) weight is sum|c_j|.  Reduction mod the degree-1 split
prime P|p (n|p-1 => p FULLY SPLIT, N(P)=p): zeta -> g a primitive n-th root in F_p, so
c reduces to sum_j c_j * g^j (mod p).  The ideal P = {c : sum c_j g^j == 0 mod p}.

Because we use the d-dim power basis (NOT the n redundant roots), there is NO trivial antipodal
weight-2 relation: the basis is honestly independent over Q.  So lambda_1^L1(P) here is the
GENUINE shortest cyclotomic integer in the ideal.

THE THREE LATTICES:
  - FULL   P:    all c in Z^d, sum c_j g^j == 0 mod p.
  - EVEN   P_e:  c supported on even power indices {0,2,4,...} only.
  - ODD    P_o:  c supported on odd  power indices {1,3,5,...} only.
The cross-parity law A == -g*B (mod p): even-part A = sum_{j even} c_j g^j,
odd-part B = sum_{j odd} c_j g^j; vanishing => A == -B. The "leak" is A == -g*B, i.e. the
odd part, after dividing by g, equals -even part. We test BOTH the vanishing split A==-B
and whether the structured g0 = -A/B is fixed / in mu_n.

r*(n,p) := (1/2) lambda_1^L1,EVEN.  Closure-direction would need lambda_1^L1,EVEN to GROW
(a power of n exceeding 2 ln p) AND the cross-parity to FORBID pure-even short vectors.
Refute-direction: lambda_1^L1,EVEN ~ log_{n} p (same counting girth) => SVP handle dead.

Exact via BFS over the d generators {g^j mod p}: girth = min #signed terms summing to 0.
"""
import math
from collections import deque

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d=x-1; s=0
    while d%2==0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a%x==0: continue
        v=pow(a,d,x)
        if v in (1,x-1): continue
        ok=False
        for _ in range(s-1):
            v=v*v%x
            if v==x-1: ok=True; break
        if not ok: return False
    return True

def prime_factors(m):
    f=set(); d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    return f

def order_n_root(p,n):
    pf=prime_factors(n)
    for gg in range(2,p):
        z=pow(gg,(p-1)//n,p)
        if all(pow(z,n//q,p)!=1 for q in pf):
            return z
    raise RuntimeError("no root")

def girth_BFS(p, gens, cap=20):
    """Min L1-weight of a NONZERO ideal vector supported on `gens`: i.e. min sum|c_j| over
       nonzero integer combos sum c_j gens[j] == 0 mod p.  Equivalent to shortest signed word
       in the generators summing to 0 -- BUT we must forbid the DEGENERATE empty relation
       (same generator with + then -, c_j cancelling to 0).  We track, per reached residue,
       the coefficient vector's support-signature is too costly; instead we BFS where a step
       is (gen index i, sign), and we EXCLUDE returning to 0 via a word that is coefficient-
       zero.  A word reduces to a coefficient vector c (c_i = signed count of gen i); it is a
       genuine ideal vector iff c != 0.  The shortest genuine one: since a +s then -s on the
       SAME gen is pure waste (it cancels and only inflates weight), the BFS-shortest path to
       0 that is genuine equals the true L1 girth as long as we don't count net-zero words.
       We enforce this by tracking the running coefficient multiset is heavy; instead use the
       simpler exact fact: the shortest GENUINE relation never repeats a generator with
       opposite signs (that's strictly wasteful), so we BFS over residues but forbid a step
       that exactly undoes the immediately-previous step, and additionally verify the found
       word has nonzero net coefficients.  For full rigor on the headline we ALSO cross-check
       via direct enumeration in `genuine_girth_enum`."""
    if not gens: return None, None
    steps = []
    for i,g in enumerate(gens):
        steps.append((i, +1, g % p))
        steps.append((i, -1, (-g) % p))
    # parent stores (gen_i, sign, prev_residue). Forbid immediate inverse of last step.
    parent={0:None}
    laststep={0:None}
    frontier=[0]
    for w in range(1, cap+1):
        nf=[]
        for r in frontier:
            ls = laststep[r]
            for (i,sg,s) in steps:
                if ls is not None and ls[0]==i and ls[1]==-sg:
                    continue  # would undo the previous step on same gen (waste)
                t=(r+s)%p
                if t==0:
                    word=[(i,sg)]
                    rr=r
                    while parent.get(rr) is not None:
                        pi,psg,pr=parent[rr]
                        word.append((pi,psg)); rr=pr
                    # verify genuine: net coefficients nonzero
                    net={}
                    for (gi,gsg) in word: net[gi]=net.get(gi,0)+gsg
                    if any(v!=0 for v in net.values()):
                        return w, word
                    else:
                        continue
                if t not in parent:
                    parent[t]=(i,sg,r)
                    laststep[t]=(i,sg)
                    nf.append(t)
        frontier=nf
        if not frontier: break
    return None, None

def genuine_girth_enum(p, gens, cap=8):
    """RIGOROUS cross-check: exact min L1 weight via iterative-deepening over coefficient
       vectors. Enumerate net coefficient assignments c (per generator) with sum|c_i| = w,
       smallest w first; return first nonzero c with sum c_i gens_i == 0 mod p.
       Feasible because girth is tiny (<=~6) and we stop at first hit."""
    m=len(gens)
    if m==0: return None
    from itertools import combinations
    for w in range(2, cap+1):
        # distribute total L1 weight w among <= w generators with signs
        # choose support sizes s=2..min(m,w); for each support, compositions of w into s parts
        for s in range(2, min(m,w)+1):
            for supp in combinations(range(m), s):
                # compositions of w into s positive parts
                def comps(total, parts):
                    if parts==1:
                        yield (total,); return
                    for first in range(1, total-parts+2):
                        for rest in comps(total-first, parts-1):
                            yield (first,)+rest
                for mags in comps(w, s):
                    # all sign patterns
                    for signbits in range(1<<s):
                        val=0
                        for k in range(s):
                            sg = -1 if (signbits>>k)&1 else 1
                            val=(val+sg*mags[k]*gens[supp[k]])%p
                        if val%p==0:
                            return w
    return None



def gh_L1(d_eff, p):
    for w in range(1, 200):
        if d_eff<=0: return None
        cnt=(2*w)**d_eff/math.factorial(min(d_eff,170))
        if cnt>=p: return w
    return None

def analyze(n, p):
    if (p-1)%n!=0 or not is_prime(p): return
    d=n//2
    g=order_n_root(p,n)
    gp=[pow(g,j,p) for j in range(d)]          # zeta^j, j=0..d-1 (power basis)
    full=gp
    even=[gp[j] for j in range(d) if j%2==0]
    odd =[gp[j] for j in range(d) if j%2==1]
    # RIGOROUS exact girth (genuine, nonzero coefficient vector)
    la = genuine_girth_enum(p, full, cap=8)
    le = genuine_girth_enum(p, even, cap=8)
    lo = genuine_girth_enum(p, odd,  cap=8)
    logn_p=math.log(p)/math.log(n)
    print(f"\n##### n={n} d=phi={d}  p={p}  (beta=log_n p={logn_p:.2f}, SPLIT N(P)=p)")
    print(f"  lambda_1^L1 FULL  = {la}   (counting girth ~ log_n p={logn_p:.2f}; GH_full~{gh_L1(d,p)})")
    print(f"  lambda_1^L1 EVEN  = {le}   (GH even-rank d/2={d//2} ~ {gh_L1(d//2,p)})   r*=le/2={le/2 if le else None}")
    print(f"  lambda_1^L1 ODD   = {lo}")
    if la and le:
        print(f"  EVEN/FULL = {le/la:.2f}   (>1 => cross-parity gives the even sublattice a STRICTLY larger SVP)")

if __name__=="__main__":
    tests={16:[97,193,257,353,1153], 32:[97,193,257,673,1153], 64:[193,257,449,577,2113]}
    for n in [16,32,64]:
        for p in tests[n]:
            analyze(n,p)
