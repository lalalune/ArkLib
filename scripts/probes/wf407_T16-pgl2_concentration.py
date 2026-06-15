#!/usr/bin/env python3
"""
WF407 T16-pgl2 (final): can the inversion x|->-x on Z/m give a NON-relation CONCENTRATION
input even though it is not a pointwise modulus relation?  Two last levers:

 (L1) SECOND-ORDER averaged: does pairing b with b^{-1} give a bound on max via the
      product |eta_b * eta_{b^-1}| or sum |eta_b|^2+|eta_{b^-1}|^2 that beats the trivial
      max? (i.e. is the worst coset 'balanced' against its inverse so neither can spike?)
      We test: is max_b |eta_b| <= max_b sqrt(|eta_b * eta_{b^-1}|)?   If the inverse
      pairing FORCED balance, the geometric-mean bound would equal the max; if inversion
      is independent, the GM is strictly below the max at the spike.

 (L2) Why the MCA twist (degree weight x^{k-1}) does NOT exist on the char-sum face:
      at k=1 the weight is x^0=1, so the 'twist' degenerates to plain inversion-permutation
      sigma:x|->-1/x of the domain, and  sum_{x in mu_n} e_p(b * (-1/x))  is just a
      RE-INDEXING of eta over the inv-permuted domain, == eta_{?}.  We compute the
      char-sum under the domain-inversion and confirm it equals eta_b (trivial reindex),
      i.e. the inversion symmetry on the DOMAIN gives NOTHING (it's eta_b again), while
      the inversion on the FREQUENCY (b|->b^{-1}) is the b-action which is NOT a relation.
      => the MCA-face DOF cut has NO char-sum-face counterpart.
"""
import cmath, math, sympy

def prim_root(p): return int(sympy.primitive_root(p))
def musub(n,p):
    g=prim_root(p); h=pow(g,(p-1)//n,p); return sorted({pow(h,j,p) for j in range(n)})

def run(p,n):
    w=2*math.pi/p; G=musub(n,p); m=(p-1)//n
    inv={b:pow(b,p-2,p) for b in range(1,p)}
    def eta(b): return sum(cmath.exp(1j*w*((b*y)%p)) for y in G)
    etas={b:eta(b) for b in range(1,p)}

    B = max(abs(etas[b]) for b in range(1,p))
    # L1: geometric-mean-with-inverse bound
    GM = max(math.sqrt(abs(etas[b])*abs(etas[inv[b]])) for b in range(1,p))
    # at the worst b, what is |eta_{b^-1}|?
    bmax = max(range(1,p), key=lambda b:abs(etas[b]))
    inv_at_max = abs(etas[inv[bmax]])

    # L2: domain-inversion char sum: sum_{x in mu_n} e_p(b * (-1/x)) over x in mu_n
    Ginv = [(p-pow(x,p-2,p))%p for x in G]   # {-1/x : x in mu_n} (set)
    def eta_dominv(b): return sum(cmath.exp(1j*w*((b*y)%p)) for y in Ginv)
    # domain-inversion equals eta_b (since {-1/x:x in mu_n} = mu_n as a SET, n even)
    dominv_eq = max(abs(eta_dominv(b)-etas[b]) for b in range(1,p))
    same_set = set(Ginv)==set(G)

    return dict(p=p,n=n,m=m,B=B,GM=GM,bmax_inv=inv_at_max,B_over_max=B,
                dominv_eq=dominv_eq,same_set=same_set)

if __name__=="__main__":
    cases=[(41,8),(73,8),(521,8),(113,16),(4129,16),(257,32)]
    hdr=f"{'p':>6}{'n':>4}{'m':>5} |  B/sqrt(n)  GM/sqrt(n)  |eta_{{1/bmax}}|/sqrt(n)  GM<B? | dominv==eta sameSet"
    print(hdr); print('-'*len(hdr))
    for (p,n) in cases:
        r=run(p,n); s=math.sqrt(n)
        print(f"{r['p']:>6}{r['n']:>4}{r['m']:>5} |  {r['B']/s:>8.3f}  {r['GM']/s:>9.3f}  "
              f"{r['bmax_inv']/s:>20.3f}  {str(r['GM']<r['B']-1e-9):>5} | "
              f"{r['dominv_eq']:>9.2e}  {str(r['same_set']):>5}")
    print()
    print("READ L1: GM (geometric mean with inverse coset) < B at the spike => inverse coset")
    print("         does NOT balance the worst coset; inversion gives NO concentration bound.")
    print("         |eta_{1/bmax}| is small at the spike (the inverse of the worst coset is NOT worst).")
    print("READ L2: domain-inversion char sum == eta_b exactly (sameSet=True): inversion on the")
    print("         DOMAIN is a trivial reindex (mu_n is inv-closed) -> gives eta_b back, NOTHING new.")
    print("         The MCA twist's degree weight x^{k-1} vanishes at k=1; no char-sum-face DOF cut.")
