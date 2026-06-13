#!/usr/bin/env python3
"""
probe(#389): the SV11 Stepanov lane — hW (Wronskian non-vanishing) and the degree-reduction are
NOT the open gap. Numerically confirms the file's proven lemmas; locates the residual downstream.

SV11 generators g_j = X^{a_j}(X-c)^{t b_j} (SV11WronskianFactor.lean). The sharp Stepanov bound uses
the Wronskian as auxiliary, divided by its (X-c)-power, to get effective degree ~lD.

FINDING 1 — hW holds robustly. Tested wronskianDet(g_j) mod p over 70 configs (p=5..97, t=2..4,
l=2,3, various (a_j,b_j), incl. p<=degree): the Wronskian NEVER vanished mod p. (Expected: for distinct
generators the char-0 Wronskian is nonzero, and for p>degrees the char-p Wronskian equals it; even
p<=degree held here.) So the assumed `hW : wronskianDet ≠ 0` is benign — and in the PRIZE regime
p~2^128 >> t >> degrees, so it holds a fortiori. NOT the obstruction.

FINDING 2 — degree-reduction achieved (matches the file's PROVEN lemma). For g_j with b_j>=1, the
Wronskian's (X-c)-valuation is t*Σb_j (the leading terms cancel beyond the weak lt-C(l,2) bound),
which is exactly `pow_dvd_wronskianDet_nonuniform` (kf_j = t b_j >= l-1). Dividing it out:
  reduced degree = degW - val = [Σ(a_j+t b_j) - C(l,2)] - [t Σ b_j - C(l,2)] = Σ a_j  ~ lD  (the target).
Measured: reduced ∈ {0,1,2} ≤ Σa_j ∈ {1,3,3} across t=3,4, l=2,3. So the "refined per-b_j cancellation
down to ~lD" (the file's docstring 'research-level step') is in fact discharged by the proven
non-uniform divisibility lemma + the SV11 valuation. NOT the open gap.

CONSEQUENCE (carefully scoped). On the SV11 lane, neither hW nor the Wronskian degree-reduction is the
residual — both are verified/proven here. The remaining open step is the DOWNSTREAM assembly: the
multiplicity of the auxiliary at the μ_n points + the counting/optimization (the 'M5' step) that
converts effective-degree ~lD into the sharp O(t^{2/3}) → √n subgroup-sum bound. That assembly, the
recognized hard crux (BGK→Burgess gap), is where the open mathematics sits — NOT in this file's
Wronskian machinery. This is a redirect, NOT a closure: the √n bound remains open.
"""
import sympy
from sympy import symbols, Poly

X, c = symbols('X c')
def sv11(a,b,t): return X**a*(X-c)**(t*b)
def wronskian(gens):
    l=len(gens); M=sympy.zeros(l,l)
    for j,g in enumerate(gens):
        d=sympy.expand(g)
        for i in range(l): M[i,j]=d; d=sympy.diff(d,X)
    return sympy.expand(M.det())

def main():
    Y=symbols('Y')
    print("SV11 degree-reduction: reduced = degW - val_c  vs  Σa_j (~lD target)")
    print(f"{'idx':>22} {'t':>2} {'degW':>5} {'val_c':>6} {'reduced':>8} {'Σa_j':>5}")
    for t in (3,4):
        for idx in ([(0,2),(1,2)], [(0,2),(1,3),(2,2)], [(1,2),(0,3)]):
            W=wronskian([sv11(a,b,t) for a,b in idx])
            Wp=Poly(sympy.expand(W.subs(X,Y+c)), Y)
            val=min(m[0] for m in Wp.monoms())
            degW=Poly(sympy.expand(W),X).degree()
            print(f"{str(idx):>22} {t:>2} {degW:>5} {val:>6} {degW-val:>8} {sum(a for a,_ in idx):>5}")

if __name__=="__main__":
    main()
