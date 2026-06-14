# Extract the EXACT deficit-2 line relation phi by reproducing the full n=16 ladder, then spot-check n=32.
# CONNECT 1.2: line forces e1(S)=c1=-g_{k+1}/c AND e2(S)=c2=g_k/c. The line Q0+gamma*x^{k_c} at TOP freq.
# k_c = r (CONNECT 1.1). The two FORCED top coeffs of the pencil after removing the line:
# p_S(x) = x^{r+1} - e1 x^r + e2 x^{r-1} - ... ; the line word contributes to coeffs of x^{k_c}=x^r and the
# CONSTANT/Q0 part. Deficit 2 = the x^r AND x^{r-1} coeffs are BOTH "absorbed" by the line+Q0 => they are
# the two free slots, and gamma=-e1 ties to the x^r slot. The REMAINING coeffs (x^{r-2}..x^0) must match a
# fixed low-degree (deg <= k_c-1 = r-1) interpolant => they're determined but FREE as e1 varies? No.
#
# The cleanest operational reproduction: in a FAITHFUL field, #bad = # distinct e1 over (r+1)-subsets whose
# pencil, viewed as a deficit-2 deep-band config on the top line, is admissible. Since p2=0 gave 97 at r=3
# but 0 at even r, and the ladder is nonzero at even r, the actual slice is e2 = AFFINE(e1), not p2=0.
# Let me find phi(e1) by: for each r, the line is determined by (gamma, and one more parameter). Two free
# params => the (e1,e2) achievable pairs that admit a deficit-2 deep line form a CURVE; #bad = its e1-support.
#
# Pragmatic: I'll reproduce the ladder by counting distinct e1 over (r+1)-subsets S such that there EXISTS
# a value w (the second line coeff) making the deg-(r-1) interpolant through the band consistent. This is
# equivalent to: NO further constraint beyond e1 free, e2 free => #bad = full e1 spectrum (wrong, too big).
# So there IS exactly ONE constraint linking e1,e2 (deficit 2 on a 1-param-after-gamma line). Search affine:
from itertools import combinations
p=2013265921
def gen_order(p,n):
    for g in range(2,500):
        cand=pow(g,(p-1)//n,p)
        if pow(cand,n,p)==1 and all(pow(cand,n//q,p)!=1 for q in (2,)):
            return cand
n=16
g=gen_order(p,n)
H=[pow(g,i,p) for i in range(n)]
expected={3:97,4:145,5:89,6:113,7:225,8:104}
def feats(S):
    s1=sum(H[i] for i in S)%p
    s2=sum(pow(H[i],2,p) for i in S)%p
    return s1,s2
data={a:[feats(S) for S in combinations(range(n),a)] for a in range(4,10)}
# Affine relation: A*p2 + B*e1^2 + C*e1 = 0 (homogeneous-ish in the cyclotomic). But e1 has a scale (gamma).
# Actually the natural deficit-2 invariant might be: e1 in a specific COSET / e2 ANY (i.e. constraint only on e1).
# Test: maybe #bad = # distinct e1 over ALL (r+1)-subsets, but counted with the RIGHT field (char 0) yields
# a number != spectrum because of REAL collisions. Recompute char-0 spectrum exactly:
import cmath, math
M=[cmath.exp(2j*math.pi*j/16) for j in range(16)]
for a in range(4,10):
    seen=set()
    for S in combinations(range(16),a):
        s=sum(M[i] for i in S)
        seen.add((round(s.real,6),round(s.imag,6)))
    print(f"a={a} r={a-1}: char-0 full e1-spectrum={len(seen)}  expected#bad={expected[a-1]}")
