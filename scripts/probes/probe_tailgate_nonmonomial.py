#!/usr/bin/env python3
"""#389/#400 tail-gate falsification: does max_v L_v(delta) cross at delta_ent,
and is the worst far direction v the power-word monomial or a non-monomial?

Tail-Gate Conjecture (deltastar-tail-gate-conjecture-2026-06-13.md):
  for delta < delta_ent(rho,B),  max_{v not in C} L_v(delta) <= B,
where L_v(delta)=max_u #{c in C+<v> : agree(c,u) >= (1-delta)n}, C=RS[F_q,mu_n,k].

We compute, on a smooth domain (mu_n, n|q-1, q a large prime so mu_n is a PROPER
subgroup -- avoiding the #400 full-group degeneracy), the actual max list size of
the dim-(k+1) supercode C+<v> at agreement a=(1-delta)n, over several far v:
 monomial x^{k}, x^{k+1}, and non-monomial v = sum of two/three higher monomials.
We report, per a, the realized max list and compare crossing-a to a_ent.

L_v(a) lower bound via: pick u to BE a codeword of C+<v> (the natural rich center),
count codewords of C+<v> agreeing with it on >= a coords. We sweep many centers
(all degree<=k+1 words built from random coeffs + the structured power words) and
take the max -- a certified LOWER bound on the true worst-case list (sound for
refuting an upper-bound gate: if this >B below a_ent, the gate is FALSE).
"""
import math, random
from itertools import combinations

def primitive_root(p):
    fac=[]; phi=p-1; m=phi; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in fac): return g
    return None

def subgroup(p,n):
    assert (p-1)%n==0
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    D=[]; x=1
    for _ in range(n): D.append(x); x=x*h%p
    return D

def evalpoly(coeffs,x,p):
    r=0
    for c in reversed(coeffs): r=(r*x+c)%p
    return r

def H2(r):
    if r<=0 or r>=1: return 0.0
    return -r*math.log2(r)-(1-r)*math.log2(1-r)

def list_at_center(center_w, basis_words, p, a, trials, seed):
    """count distinct supercode words agreeing with center on >= a coords,
    by random search over coeff combos of basis (dim small). returns best count
    found of a single rich list (greedy: we instead count over a structured
    enumeration when basis small)."""
    n=len(center_w)
    # enumerate codewords of the supercode that agree with center on >=a coords:
    # a supercode word is sum_j cj*basis_j. Agreement with center on coord i:
    # sum_j cj*basis_j[i] == center_w[i]. We can't enumerate all q^{dim}. Instead
    # random-sample coeff vectors and a structured family (scalar multiples of
    # differences). Return max agreement-list size discovered around center.
    found=set(); rnd=random.Random(seed)
    dim=len(basis_words)
    for _ in range(trials):
        c=[rnd.randrange(p) for _ in range(dim)]
        w=tuple((sum(c[j]*basis_words[j][i] for j in range(dim)))%p for i in range(n))
        ag=sum(1 for i in range(n) if w[i]==center_w[i])
        if ag>=a: found.add(w)
    return len(found)

def main():
    # prize-shaped small instance: n=16, proper subgroup => need p with 16|p-1,
    # p large enough that mu_16 != F_p^*  (p-1 != 16 => p != 17). use p=97 (16|96).
    for (p,n,k) in [(97,16,2),(193,16,2),(257,16,2)]:
        D=subgroup(p,n)
        # basis of supercode C+<v>: {1,x,...,x^{k-1}} (RS[k]) plus far v.
        mon=lambda e: [pow(x,e,p) for x in D]
        rsbasis=[mon(e) for e in range(k)]   # deg < k  (dim k)
        fars={
          'x^k': mon(k),
          'x^{k+1}': mon(k+1),
          'x^k+x^{k+2}': [(mon(k)[i]+mon(k+2)[i])%p for i in range(n)],
          'x^k+3x^{k+3}': [(mon(k)[i]+3*mon(k+3)[i])%p for i in range(n)],
        }
        rho=k/n; B=n  # prize budget ~ n
        a_ent=(1-(1 - rho - H2(rho)/math.log2(max(B,2))))*n  # agreement at delta_ent
        print(f"\n=== p={p} n={n} k={k} rho={rho:.3f} B={B} a_ent={a_ent:.1f} ===")
        for name,v in fars.items():
            basis=rsbasis+[v]
            # centers: structured power words (these realize Sylvester-type lists)
            best={}
            for a in range(n, k, -1):
                # build many centers: random supercode words + the far word itself
                rnd=random.Random(hash((p,name,a))& 0xffffff)
                mx=0
                for t in range(40):
                    c=[rnd.randrange(p) for _ in range(len(basis))]
                    cen=tuple(sum(c[j]*basis[j][i] for j in range(len(basis)))%p for i in range(n))
                    L=list_at_center(cen,basis,p,a,4000,seed=t)
                    if L>mx: mx=L
                best[a]=mx
            # find crossing: largest a where list>B  (delta where gate would break)
            cross=[a for a in best if best[a]>B]
            ca=max(cross) if cross else None
            print(f"  v={name:14s} maxlist@a: " +
                  " ".join(f"{a}:{best[a]}" for a in sorted(best,reverse=True)[:8]) +
                  f"   cross_a(>B)={ca}")
main()
