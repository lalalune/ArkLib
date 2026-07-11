import math
from sympy import isprime, primitive_root, n_order

# DECISIVE adversarial test: the geometric-cluster lower bound mechanism requires a
# multiplicative subgroup mu_n whose elements (as least-residues) form a geometric
# progression near 0. The cluster size is bounded by the number of subgroup elements x
# with x < p*tau (tau the coherence window ~1/n). 
#
# CLAIM (cluster cap, rigorous): for ANY prime p and ANY order-n subgroup mu_n=<h>,
#   #{x in mu_n : x mod p in (0, p*tau) U (p(1-tau), p)} <= 1 + 2*tau*n + ERROR,
# where the equidistribution error is O(M log p) by the standard subgroup-equidistribution
# (Polya-Vinogradov / the SAME M we're bounding -- circular for a CLEAN proof, but the
# point for N2 is the LOWER-bound DIRECTION:) the coherent head that can be GUARANTEED
# unconditionally is only the LITERAL geometric integers {h^j as integers < p}, which
# number floor(log_h p)+1 = O(log p). Beyond that, the residues are h^j mod p and NO
# unconditional statement forces them coherent (would need to DISPROVE equidistribution,
# i.e. prove M large -- which is exactly what we cannot do unconditionally).
#
# So the UNCONDITIONAL lower bound from geometry is M >= |head| - |tail| where 
# |head| <= log_h p and tail is bounded below by -(n - |head|) [trivial]. 
# This gives M >= (coherent head) - (n - head)  <-- USELESS (negative for n large).
# A USEFUL lower bound needs the tail to NOT cancel the head, i.e. needs control of the
# tail phases -- unavailable unconditionally. 
#
# Hence: the BEST unconditional lower bound is the L^2 (Parseval) one:
#   sum_{b!=0} |eta_b|^2 = q*(n - n^2/q)... wait. sum_{all b} |eta_b|^2 = q*n (Parseval over indicator).
#   Actually sum_b |eta_b|^2 = q * |mu_n| = q*n? No: sum_b |sum_x e_p(bx)|^2 = q * #{(x,y): x=y} = q*n.
#   Excluding b=0 (eta_0=n): sum_{b!=0}|eta_b|^2 = qn - n^2. avg over q-1 values = (qn-n^2)/(q-1) ~ n.
#   => max_b |eta_b|^2 >= n  => M >= sqrt(n). This is the ONLY unconditional lower bound. EXACTLY Johnson.
print("UNCONDITIONAL LOWER BOUND (Parseval, exact):")
print("  sum_{b!=0} |eta_b|^2 = q*n - n^2  =>  M^2 >= (qn-n^2)/(q-1) ~ n  =>  M >= sqrt(n)*(1-o(1))")
print("  This is the ONLY method-independent lower bound. It gives M >= sqrt(n), NOT sqrt(n)*omega.")
print()
# verify Parseval exactly at a prize prime
for n,p in [(16,65537),(8,4153)]:
    if not isprime(p) or (p-1)%n: continue
    g=primitive_root(p); h=pow(g,(p-1)//n,p); mun=[pow(h,j,p) for j in range(n)]
    w=2*math.pi/p
    s=0.0; mx=0.0
    for b in range(1,p):
        re=sum(math.cos(w*((b*x)%p)) for x in mun); im=sum(math.sin(w*((b*x)%p)) for x in mun)
        v=re*re+im*im; s+=v; mx=max(mx,v)
    print(f"  n={n} p={p}: sum_{{b!=0}}|eta|^2={s:.1f} (exact qn-n^2={p*n-n*n}); avg={s/(p-1):.3f}; M^2={mx:.2f}; M/sqrt(n)={math.sqrt(mx/n):.3f}")
print()
print("CONCLUSION: Parseval forces M >= sqrt(n)(1-o(1)) ALWAYS (the floor's lower side,")
print("matching Johnson 1-sqrt(rho)). It does NOT force M >= sqrt(n)*omega. A divergent")
print("lower bound would require lower-bounding a SPECIFIC |eta_b|, which needs DISPROVING")
print("equidistribution of mu_n -- unavailable unconditionally and FALSE for generic primes.")
