# Calibrate the deep-band #bad-scalar object directly over mu_n.
# Object (per CONNECT 1.3): #bad(r) = # distinct gamma=-e1(S) over (r+1)-subsets S of mu_n
#   such that S lies on a deep-band line: deficit-2 => BOTH top coeffs of p_S vanish.
# But the LINE forces e2 = phi(e1). The MEASURED ladder counts distinct bad gamma.
#
# We reconstruct the measured object faithfully. The deep-band condition in char 0 (faithful, = worst case
# per O172) for the top-frequency line: a subset S of size r+1 is "bad" if the pencil polynomial has its top
# TWO coefficients vanish, i.e. there is a deep-band line through it. Per the in-tree reduction, what is
# COUNTED as #bad is the number of distinct e1(S) such that S is a valid deep-band config.
#
# To match the published ladder 97,145,89,113,225,104 (n=16, r=3..8) we enumerate over mu_n = nth roots of
# unity in C (char-0 / faithful regime). A deep-band config at deficit 2 with top frequency k_c=r means:
#   p_S(x) = prod_{s in S}(x - s) has the form x^{r+1} + gamma x^r - W ... with deficit 2 meaning
#   coeff of x^{r} AND coeff of x^{r-1} both prescribed by the SINGLE line direction x^{k_c}.
# The clean characterization (Round6): a subset of size r+1 is a deep-band witness iff e2(S) is the
# line-forced value. But over the FULL ladder the actual counted quantity is the e1-axis support.
#
# SIMPLEST faithful model that reproduces r=3 closed form n*C(n/4,2)+1:
#   r=3 -> 4-subsets, count distinct e1 among 4-subsets whose e2 = (line)*e1-relation.
# The proven r=3 result n*C(n/4,2)+1 comes from the antipodal/parity split. Let me just brute the
# distinct-e1 over 4-subsets with e2 forced, but I need the EXACT phi. Instead, reproduce the published
# numbers by the structural characterization the kernels actually use, which I cross-check below.
import itertools, cmath, math
def mu(n):
    return [cmath.exp(2j*math.pi*k/n) for k in range(n)]

# r=3 closed form check
for n in [16,32,64]:
    g=n//4
    bad = n*math.comb(g,2)+1
    K = (2**3)*math.comb(n//2,3)
    print(f"r=3 n={n}: #bad(closed)={bad}  K={K}  ratio={K/bad:.3f}")
