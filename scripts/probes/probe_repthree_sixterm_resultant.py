#!/usr/bin/env python3
"""
PROBE: r=3 RepThree char-p transfer via the SIX-TERM cyclotomic resultant lift.

The r=2 (Sidon) char-p transfer (SidonResultantImproved) works like this:
  - A 4-term zero-sum w^i + w^j - w^k - w^l = 0 in F_p (w a primitive n-th root)
    lifts to Res(Phi_n, fourTerm) ≡ 0 (mod p).
  - Parseval sum_{zeta in mu_n} |f(zeta)|^2 = 4n + AM-GM over phi(n)=n/2 prim roots
    => |Res| <= 8^{phi(n)/2} = 2^{3n/4}.
  - So for p > 2^{3n/4}: Res != 0 (char-0) => Res !≡ 0 mod p => NO nontrivial 4-term
    relation => repCount <= 2 (Sidon-mod-neg).

r=3 ANALOG (this probe). A "genuine" (non-antipodally-paired) zero-sum SIX-tuple
  c_1+...+c_6 = 0, c_i in mu_n, would violate RepThree. Sign-normalize to a six-term
  sixTerm(X) = X^{a}+X^{b}+X^{c}-X^{d}-X^{e}-X^{f} (3 plus, 3 minus after pairing
  the antipodal structure -- but a GENUINE relation is one NOT reducible to antipodal
  pairs). The resultant Res(Phi_n, sixTerm) over Z vanishes mod p iff the relation
  holds in F_p.

We measure:
  (1) Parseval: sum_{zeta in mu_n} |sixTerm(zeta)|^2  -- predict 6n for distinct expts.
  (2) max |Res(Phi_n, sixTerm)| over GENUINE (non-antipodal) distinct-exponent six-terms
      => the AM-GM prediction |Res| <= (6n/phi(n))^{phi(n)/2} = 12^{n/4}.
  (3) char-p check: for the prize-regime threshold p > 12^{n/4}, is RepThree FORCED?
      i.e. does every char-p genuine six-term relation require p <= |Res| <= 12^{n/4}?
  (4) DIRECT char-p RepThree: brute over F_p with n-th roots, count genuine (non-antipodal)
      zero-sum sextuples; verify = 0 once p > 12^{n/4}.

PROPER subgroup mu_n = <g^{(p-1)/n}> only. n = 2^a. NEVER n = q-1.
"""
import numpy as np
from itertools import product
from sympy import primerange, isprime, totient, resultant, symbols, Poly, cyclotomic_poly
import sys

X = symbols('X')

def parseval_sixterm(n):
    """sum_{zeta in mu_n} |zeta^{e1}+...+zeta^{e6} signed|^2 for distinct exponents.
       By orthogonality over the full n-th roots: = n * (#distinct exponents) when
       all 6 exponents distinct (cross terms vanish). Returns the predicted value 6n
       and an empirical check."""
    # use complex n-th roots
    zetas = np.exp(2j*np.pi*np.arange(n)/n)
    # pick 6 distinct exponents, signs (+,+,+,-,-,-)
    e = [0,1,2,3,4,5]  # distinct
    signs = np.array([1,1,1,-1,-1,-1])
    vals = sum(s*zetas**ex for s,ex in zip(signs,e))
    s = np.sum(np.abs(vals)**2)
    return 6*n, s.real

def sixterm_poly(exps, signs):
    """integer polynomial sum signs[i] X^{exps[i]}."""
    p = Poly(0, X, domain='ZZ')
    for ex,sg in zip(exps,signs):
        p = p + Poly(sg, X, domain='ZZ')*Poly(X**ex, X, domain='ZZ')
    return p

def is_antipodal_paired(exps, signs, n):
    """A six-tuple (c_i = w^{exps_i} with sign) is antipodally paired if it splits into
       3 pairs {z,-z}. -z = w^{e + n/2}. With signs absorbed: a +w^a and a -w^a cancel
       (that's c + (-c) = 0 where the two terms are w^a and -w^a = w^{a+n/2}... careful).
       We treat the multiset of SIGNED roots {sign_i * w^{exps_i}}. Antipodal pairing:
       can partition the 6 signed values into 3 pairs each summing to 0.
       A pair (u,v) sums to 0 iff v = -u. We just check perfect matching by value."""
    w = np.exp(2j*np.pi/n)
    vals = [sg*(w**ex) for sg,ex in zip(signs,exps)]
    # try to match into 3 antipodal pairs
    used=[False]*6
    def match(k):
        if k==6: return True
        if used[k]:
            return match(k+1)
        used[k]=True
        for j in range(k+1,6):
            if not used[j] and abs(vals[k]+vals[j])<1e-9:
                used[j]=True
                if match(k+1): return True
                used[j]=False
        used[k]=False
        return False
    return match(0)

def max_genuine_resultant(n, cap=200):
    """max |Res(Phi_n, sixTerm)| over GENUINE (non-antipodal) distinct-exponent
       zero-in-char-0? No: we want six-terms whose resultant we bound. The relevant
       set = signed six-tuples of n-th roots that are NOT antipodally paired (genuine),
       with the sixTerm poly built from them. We sample to find the max |Res|."""
    Phi = Poly(cyclotomic_poly(n, X), X, domain='ZZ')
    maxres = 0
    cnt = 0
    rng = np.random.default_rng(0)
    seen = 0
    # enumerate small distinct-exponent signed six-tuples
    for exps in product(range(n), repeat=6):
        if len(set(exps))!=6:  # require distinct exponents (else degenerate)
            continue
        # canonical sign pattern (+,+,+,-,-,-)
        signs=[1,1,1,-1,-1,-1]
        if is_antipodal_paired(exps,signs,n):
            continue
        seen+=1
        if seen>cap:
            break
        poly = sixterm_poly(exps,signs)
        R = resultant(Phi.as_expr(), poly.as_expr(), X)
        R=abs(int(R))
        if R>maxres:
            maxres=R
    return maxres, seen

def amgm_bound(n):
    phi = int(totient(n))
    # sum over phi(n) prim roots of |f|^2 <= 6n (subset of full sum 6n; actually prim
    # roots are a subset, sum_prim <= sum_full = 6n). AM-GM: prod <= (6n/phi)^{phi}.
    # |Res|^2 = prod_prim |f(zeta)|^2 <= (6n/phi)^{phi}. |Res| <= (6n/phi)^{phi/2}.
    val = (6*n/phi)**(phi/2)
    return val, phi

def charp_repthree_direct(n, p, g):
    """Brute char-p: w = primitive n-th root in F_p. Count GENUINE (non-antipodal)
       zero-sum signed six-tuples of mu_n. Return count (should be 0 if p > threshold)."""
    w = pow(g, (p-1)//n, p)  # primitive n-th root
    roots = [pow(w, k, p) for k in range(n)]
    half = n//2
    genuine = 0
    # signed values: +roots[k] and -roots[k] mod p. A genuine relation: 6 signed roots
    # summing to 0 mod p, distinct positions, NOT antipodally pairable.
    # We sample distinct-exponent (+,+,+,-,-,-) six-tuples.
    from itertools import combinations
    # choose 3 plus-exponents and 3 minus-exponents, all distinct exponents
    cnt_checked=0
    for plus in combinations(range(n),3):
        for minus in combinations(range(n),3):
            if set(plus)&set(minus): continue
            cnt_checked+=1
            s = (roots[plus[0]]+roots[plus[1]]+roots[plus[2]]
                 -roots[minus[0]]-roots[minus[1]]-roots[minus[2]])%p
            if s==0:
                exps=list(plus)+list(minus); signs=[1,1,1,-1,-1,-1]
                if not is_antipodal_paired(exps,signs,n):
                    genuine+=1
            if cnt_checked>200000: 
                return genuine, cnt_checked, True
    return genuine, cnt_checked, False

def primitive_root(p):
    if p==2: return 1
    factors=set()
    phi=p-1; m=phi; d=2
    while d*d<=m:
        if m%d==0:
            factors.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: factors.add(m)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in factors):
            return g
    return None

print("=== (1) PARSEVAL CHECK: sum |sixTerm|^2 over mu_n (distinct expts) ===")
for n in [4,8,16,32]:
    pred,emp = parseval_sixterm(n)
    print(f"  n={n}: predicted 6n={pred}, empirical={emp:.4f}, match={abs(pred-emp)<1e-6}")

print("\n=== (2) AM-GM RESULTANT BOUND |Res| <= (6n/phi)^{phi/2} = 12^{n/4} ===")
for n in [4,8,16]:
    val,phi=amgm_bound(n)
    print(f"  n={n}: phi={phi}, AM-GM bound (6n/phi)^(phi/2)={val:.3e}, "
          f"12^(n/4)={12**(n/4):.3e}, log2(bound)={np.log2(val):.3f} (vs n={n})")

print("\n=== (3) MAX GENUINE RESULTANT (empirical, small n; verifies <= AM-GM) ===")
for n in [4,8]:
    mr,seen=max_genuine_resultant(n, cap=120)
    val,phi=amgm_bound(n)
    print(f"  n={n}: max|Res|={mr} over {seen} genuine six-terms, AM-GM bound={val:.3e}, "
          f"OK={mr<=val+1}")

print("\n=== (4) DIRECT char-p RepThree: genuine zero-sum sextuples in mu_n over F_p ===")
print("    Prediction: 0 genuine relations once p > 12^{n/4} (the resultant threshold).")
for n in [8,16]:
    thr = 12**(n/4)
    # pick primes p ≡ 1 mod n, one BELOW-ish and several ABOVE threshold
    cands=[]
    for p in primerange(max(n+1,int(thr*0.3)), int(thr*8)+2000):
        if p%n==1:
            cands.append(p)
        if len(cands)>=4: break
    print(f"  n={n}: threshold 12^(n/4)={thr:.3e} (log2={np.log2(thr):.2f})")
    for p in cands:
        g=primitive_root(p)
        genuine,checked,capped = charp_repthree_direct(n,p,g)
        rel = "ABOVE" if p>thr else "below"
        print(f"    p={p} ({rel} thr, p%n={p%n}): genuine non-antipodal zero-sextuples={genuine}"
              f"  (checked {checked}{' CAPPED' if capped else ''})")
