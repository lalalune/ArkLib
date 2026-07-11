# Reproduce the deep-band #bad-scalar ladder for n=16, r=3..8 (published: 97,145,89,113,225,104).
# Deep band = deficit 2: for an (r+1)-subset S of mu_n on the TOP-FREQ line Q0 + gamma x^{k_c}, k_c=r,
# the deficit-2 condition forces the top TWO power-sum/elementary-symmetric coeffs. Per CONNECT/Round6
# the bad gamma = -e1(S), and the deep-band condition is that the config sits on a single line: the
# pencil polynomial p_S = prod(x-s) must, after subtracting the line word, drop degree by 2.
#
# Operationally (matching probe_o150 / KKH26): a deep-band witness at top frequency is an (r+1)-subset
# whose pencil has the property that BOTH leading line-coefficients are determined. The MEASURED #bad
# the task quotes is the count of DISTINCT bad gamma. We reconstruct it as the e1-axis support of the
# set of (r+1)-subsets that are deep-band-valid.
#
# The cleanest faithful reconstruction that matches r=3 closed form and the o150 fiber structure:
# A subset S (size r+1) on mu_n is a deep-band config iff its complement-within-the-line vanishing
# pattern holds. Empirically the deep-band #bad equals the number of distinct e1 over (r+1)-subsets S
# such that S supports a vanishing sum making both top coeffs collapse onto ONE line direction.
#
# To be RIGOROUS and reuse the proven object, I compute the e1-axis SUPPORT of the FULL (e1,e2) joint
# level set's relevant slice. But the published numbers are the actual counted #bad. Let me just
# brute the standard model used across the probes: deep band at deficit 2 = subsets where the pencil,
# evaluated against the best degree-(r-1) interpolant, agrees on >= r+2 points (= a0 = r+1+1?), i.e.
# the #bad scalars gamma for which a line word has a low-degree agreement of size a0=r+1.
#
# Given the complexity, reproduce via the SUBSET-SUM SPECTRUM bracket the kernels prove:
#   #bad lies in [ 2^r C(n/2,r) , |spectrum| ] where spectrum = {sum_{x in S} x : |S|=r}  (size r, NOT r+1!)
# Wait: witness_badscalar_card_le_spectrum uses powersetCard (k+1). With k=k_c. Let me just compute the
# spectrum cardinality |{ sum_{x in S} x : S in C(mu_n, m) }| for various m and compare to the ladder.
import itertools, cmath, math
def mu(n): return [cmath.exp(2j*math.pi*j/n) for j in range(n)]
def spectrum_card(n, m, tol=1e-7):
    M = mu(n); seen=[]
    for S in itertools.combinations(range(n), m):
        s = sum(M[i] for i in S)
        # dedup by rounding
        key=(round(s.real/tol), round(s.imag/tol))
        seen.append(key)
    return len(set(seen))
# spectrum sizes for n=16
print("n=16 subset-sum spectrum |{sum S : |S|=m}| for m=1..8:")
for m in range(1,9):
    print(f"  m={m}: {spectrum_card(16,m)}")
