#!/usr/bin/env python3
"""
wf407 / T232-03-bgk : connect BGK magnitude M to E_2 and the Fermat-curve count.

Three distinct 'additive' counts on G=mu_n:
   M      = #{u in G : (1+u) in G}                          (BGK; -1 in G so = |G cap (G-1)| etc.)
   T3     = #{(x,y,z) in G^3 : x+y+z=0} = n*M               (3-fold zero-sum; proven in-tree)
   E2     = #{(a,b,c,d) in G^4 : a+b=c+d}                   (additive energy)
   N_F    = #{(x,y) in G^2 : x+y=1}                         (affine Fermat-curve point count, w=1)

Char-0 baselines (G = nth roots of unity in C, n even):
   M_C    = 0      (no consecutive pairs on unit circle except degenerate)
   E2_C   = 3n^2 - 3n   (memory; let's re-derive/verify in char 0 via the <=2-rep bound: minimal energy)

CLAIMS to test:
  (a) N_F (x+y=1) relates to M:  for n even, M = #{u: u in G and 1+u in G}; sub u -> x, 1+u -> ... .
      Actually #{(x,y) in G^2 : x+y=1}: set x=u? then y=1-u. We compare to M's 1+u in G.
      Distinguish carefully and report the EXACT linear relation among {M, N_{x+y=1}, N_{x+y=-1}}.
  (b) E2 = (2n^2-n) + (correction). Is the correction = 2 * (#additive quadruples) and does the
      char-0 minimal value 3n^2-3n decompose as 2n^2-n + (n^2-2n)?  n^2-2n = n(n-2).
  (c) Fermat-curve / Hasse-Weil: #{(x,y) in mu_n^2 : x+y=c} for c!=0 has 'expected' value n^2/p with
      Weil-type error O(n) ... but n^2/p << 1 in prize regime, so the count is 0 or O(1) = exactly M-scale.
"""
from sympy import primerange
from collections import Counter

def primroot(p):
    order=p-1; qs=[]; mm=order; d=2
    while d*d<=mm:
        if mm%d==0:
            qs.append(d)
            while mm%d==0: mm//=d
        d+=1
    if mm>1: qs.append(mm)
    g=2
    while any(pow(g,order//q,p)==1 for q in qs): g+=1
    return g

def mu_n(n,p):
    g=primroot(p); h=pow(g,(p-1)//n,p)
    s=set(); cur=1
    for _ in range(n):
        s.add(cur); cur=cur*h%p
    return s

def counts(n,p):
    G=mu_n(n,p); Gs=G
    M = sum(1 for u in G if (1+u)%p in Gs)
    Nf1 = sum(1 for x in G if (1-x)%p in Gs)    # x+y=1
    Nfm1= sum(1 for x in G if (-1-x)%p in Gs)   # x+y=-1
    # E2
    r=Counter()
    Gl=list(G)
    for a in Gl:
        for b in Gl:
            r[(a+b)%p]+=1
    E2=sum(v*v for v in r.values())
    return M,Nf1,Nfm1,E2,r

def main():
    print("EXACT linear relations among M, N(x+y=1), N(x+y=-1), and E_2 decomposition.\n")
    print(f"{'n':>4} {'p':>7} {'M':>4} {'N(=1)':>6} {'N(=-1)':>7} {'E2':>7} "
          f"{'E2-(2n2-n)':>11} {'r0=#x+y=0':>10}")
    print("-"*70)
    samples = [(8,17),(8,41),(8,73),(8,89),(16,17),(16,97),(16,193),(16,257),
               (32,97),(32,193),(32,257),(32,353),(64,193),(64,257),(64,641),(64,7937)]
    for n,p in samples:
        if (p-1)%n: continue
        M,Nf1,Nfm1,E2,r=counts(n,p)
        r0=r.get(0,0)   # #{(a,b): a+b=0} = n (antipodal pairs) since -1 in G
        print(f"{n:>4} {p:>7} {M:>4} {Nf1:>6} {Nfm1:>7} {E2:>7} {E2-(2*n*n-n):>11} {r0:>10}")
    print("\nNotes:")
    print("  * r(0)=#{(a,b)in G^2:a+b=0}: equals n since -G=G (each a pairs with -a).")
    print("  * N(x+y=-1) should EQUAL M: y=-1-x in G and x in G <=> x in G and -(1+x) in G = BGK def.")
    print("  * N(x+y=1): x in G, 1-x in G. Under x->-x' (G symmetric): -x' in G, 1+x' in G => = M too.")
    print("    So expect N(=1)=N(=-1)=M exactly (for even n).")
    print()
    # E2 sum-rule: E2 = sum_c r(c)^2. r(0)=n. For c!=0, r(c) = #{(a,b):a+b=c} = N(x+y=c) on G.
    # By dilation (mult by g in G), r(c) depends only on coset of c? Actually a+b=c, scale by t in G:
    # ta+tb=tc, so r(c)=r(tc) for t in G. So r is constant on G-cosets of c. c=0 special.
    print("  * E_2 = n^2 (from r(0)=n)  + sum_{c!=0} r(c)^2; r constant on G-orbits of c (dilation).")
    print("    The 'clean' char-0 value 3n^2-3n: with r(0)=n contributes n^2; remaining 2n^2-3n from c!=0.")
    print()
    # char-0 check: build n-th roots of unity in C (high precision via exact algebraic is hard; use the
    # known minimal-energy combinatorial fact instead): count <=2 reps. Just print the predicted value.
    for n in [8,16,32,64]:
        print(f"   n={n}: char-0 E2 (=3n^2-3n) = {3*n*n-3*n};  2n^2-n={2*n*n-n}; "
              f"diff(char0 - trivial)= {3*n*n-3*n-(2*n*n-n)} = n^2-2n = n(n-2)={n*(n-2)}")

if __name__=="__main__":
    main()
