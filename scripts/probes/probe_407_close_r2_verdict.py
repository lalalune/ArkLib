"""
R2 VERDICT SUMMARY — what Kambire's paper actually proves about parameter optimization.

Reading arXiv:2604.09724 line-by-line:
  - "Setting parameters" (L63-96): picks rho=u/2^v, K (power of 2 in [L,2L]), s=2^alpha,
    r=rho*s+2, m=2^{2^alpha/K-alpha}, n=sm, k=(r-2)m.  These are CONSISTENCY/SUFFICIENCY choices
    (make r,m,k integers; make K log2 n = s; make count >= n^C), NOT a maximization.
  - "Constructing the Counterexample" (L100-153): FIXES f=X^{rm}, g=X^{(r-1)m} (ONE specific line);
    proves Delta(X^{rm}+lam X^{(r-1)m}, C) <= delta for each lam in H^{(+r)}.  No optimization over (a,b).
  - "Counting" (L154-295): lower-bounds the count |H^{(+r)}| >= C(s/2,r) >= (s/2r)^r, shows >= n^C.
    Pure LOWER bound to clear the threshold; no claim of maximality.

So in Kambire's paper R2 is:
  (R2a) [s,r selection]: SUFFICIENCY, not maximization.  But verified here: the count is MONOTONE
        INCREASING in s at fixed radius, and growing s makes delta closer to capacity, so his
        'largest s' choice IS the count-maximizing AND capacity-approaching direction. The two align.
        => R2a worst-case IS Kambire's (s=K log2 n, r=rho s+2) -- VERIFIED, but NOT proven-as-max
           by him (he only needs the lower bound). The maximality is OUR addition (numerics).
  (R2b) [exponent (a,b) selection]: ABSENT from the paper.  Kambire uses ONE monomial line.  The
        in-tree R1 refutation (2026-06-14) shows the monomial is NOT the max -- the general cofactor
        X^{b}(X^{a-b}+...+gamma) with even gcd(a,b) gives 2x MORE bad scalars (antipodal-doubling).
        => the FLOOR's worst-case is the GENERAL cofactor pencil, NOT Kambire's monomial.  This is
           strictly MORE than Kambire handles.

So R2 is NOT 'fully proven by Kambire' as an optimization:
  - Kambire proves the count is >= n^C (LOWER bound, sufficiency) for his ONE line. CEILING side.
  - The FLOOR needs the UPPER bound: NO line (over all (a,b), all s|n) beats |H^{(+r)}| at radius
    delta. Kambire does NOT prove this. R2a-max is verified numerically (monotone in s); R2b-max is
    REFUTED for monomials (general cofactor doubles it) => the floor must bound the general pencil.
"""
print(__doc__)
print("Worst-case (m,r,s) the FLOOR must handle (= count-maximizing at the delta* edge):")
print("  s = K*log2(n) = 2^alpha   (K ~ 16, the largest subgroup the closeness requires)")
print("  r = rho*s + 2             (couples to s via the rate)")
print("  m = n/s                   (cofactor period; gcd(a,b)=m EVEN since m=2^j, n=2^mu)")
print("  delta* = 1 - rho - 2/s    (= 1 - rho - 2*rho*log2(1/2rho)/log2(eps*q) in self-consistent log2 form)")
print()
print("  At mu=30, rho=1/4: s=480, r=122, m=2^30/480~2.24e6, delta*=0.7458 (Regime A, q=n^33).")
print("  (The KB note's 's~44,r~11' is Regime B with smaller q; both are 'small s, r=rho s+2'.)")
