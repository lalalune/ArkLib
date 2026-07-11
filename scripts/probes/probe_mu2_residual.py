# Probe: is mu_2={1,-1} the genuine residual rung (carries list info where mu_1 doesn't)?
# Dichotomy: saving on mu_{2^mu} <=> rootCount(Q, mu_2) < natDegree(Q) at s=mu-1.
# mu_2 has 2 elements => rootCount(Q,mu_2) in {0,1,2}.
# The condition is NON-degree-forced (genuine list info) iff there EXIST Q with
#   rootCount(Q,mu_2) = natDegree(Q) (saturation, no saving) for natDegree >= 1,
# i.e. the bound is TIGHT and not implied by deg alone.
#
# Q ranges over BASE polynomials of the off-BGK descent: the antipodal route descends
# the agreement polynomial. At mu_2 the relevant Q are deg-<= base agreement polys.
# We check: for deg d=1,2, can rootCount(Q,mu_2) reach d (tight, no saving)?
#   d=1: Q=X-1 -> roots in {1,-1}: {1}. count=1=d. TIGHT (saturates, deg-forced floor).
#   d=2: Q=(X-1)(X+1)=X^2-1 -> both 1,-1 roots. count=2=d. TIGHT.
#   d=2: Q=X^2-c, c not a square-of-mu2 -> 0 roots < 2. saving.
# So at mu_2 the bound rootCount<=2 CAN be saturated (tight) AND CAN have saving.
# => UNLIKE mu_1 (where count<=1 forced saving for deg>=2), mu_2 is a GENUINE
#    decision point: the saving condition is NOT degree-implied; it depends on Q.

print("=== mu_2 = {1,-1} residual probe (exact, symbolic) ===")
mu2 = [1, -1]
def rootcount(coeffs, pts):
    # coeffs low..high
    cnt=0
    for x in pts:
        v=sum(c*(x**i) for i,c in enumerate(coeffs))
        if v==0: cnt+=1
    return cnt
tests = {
  "X-1 (d=1)": [-1,1],
  "X+1 (d=1)": [1,1],
  "X^2-1 (d=2)": [-1,0,1],
  "X^2-4 (d=2, no mu2 root)": [-4,0,1],
  "X^2+1 (d=2)": [1,0,1],
  "X^3-X (d=3)": [0,-1,0,1],
}
for name,c in tests.items():
    d=len(c)-1
    rc=rootcount(c,mu2)
    verdict = "SATURATES (no saving, NOT deg-forced)" if rc==d else ("SAVING" if rc<d else "?")
    print(f"  {name:30s} rootCount(mu2)={rc}  deg={d}  {verdict}")
print()
print("CONCLUSION: at mu_2 the saving condition rootCount(Q,mu_2) < deg Q is GENUINE:")
print("  - X^2-1 saturates (count=2=deg, NO saving) => the bound is achievable/tight")
print("  - X^2+1, X^2-4 give saving (count<deg)")
print("So mu_2 is the FIRST rung where the off-BGK saving condition carries real list")
print("information (Q-dependent, not degree-forced). It is the TRUE residual floor,")
print("confirming the baserung brick's 'smallest rung with >=2 eval points' prediction.")
print("The residual list object = the deg-<=k agreement polynomials' root pattern on")
print("the fixed 2-element cyclotomic group {1,-1} = a FINITE, p-independent decision.")
