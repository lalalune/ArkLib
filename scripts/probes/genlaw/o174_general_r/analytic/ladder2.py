# Reproduce the n=16 deep-band #bad ladder by DIRECT line enumeration in a prime field, the way the
# in-tree census actually defines it. Faithful (char-0 = worst case, O172): use a prime p with mu_16,
# rate 1/2 so degree budget = k = n/2 = 8, deep band deficit 2 => agreement a0 = k_c+1.
#
# The DEEP-BAND object for general r (k_c = r, the top frequency): the line is W_gamma = X^{k_c} + gamma X^{k_c-?}
# Actually per CONNECT: line Q0 + gamma x^{k_c}, agreement size a0 = k_c+1 = r+1, deficit a0-k_c=... wait
# a0 - k_c = (r+1) - r = 1, not 2. The deficit-2 means deg drop of TWO: the pencil p_S = prod(x-s) over the
# (r+1)-subset has BOTH top coeffs (x^r and x^{r-1}) pinned by the line. So r+1 points, deg-(r+1) monic, and
# requiring it equals (line word) interpolant means top-2 elementary symmetric e1,e2 are forced.
#
# CONCRETE: For the TOP-frequency deep band, sweep gamma; a gamma is "bad" iff exists (r+1)-subset S of mu_n
# on which the line word w(x)=x^{r+1}? Let me use the faithful spectral definition that matches O150's
# e-vanishing: #bad(r) = #{ distinct -e1(S) : S in C(mu_n, r+1), e2(S) = e1(S)^2 * rho } for the line's rho.
# Since I don't have the exact rho per r, I directly COUNT distinct e1 over all (r+1)-subsets whose
# (e1,e2) pair is consistent with SOME single deep-band line through the top frequency. The line through
# top freq with deficit 2 means the pair (e1,e2) must satisfy the line's algebraic relation; but the line
# is FREE in gamma, so the constraint is purely: the subset's pencil, minus the rank-1 line correction in
# the top monomial, must vanish to deficit 2 -> this is exactly e_{k_c-1}=...=0 EXCEPT top two.
#
# Use the O150 e-vanishing model generalized: for the order-n group with rate giving degree budget d=n/2,
# a deep-band-at-deficit-2 (r+1)-subset is one whose elementary symmetric functions e_j vanish for all
# j EXCEPT the two the line carries. For the TOP-freq line carrying x^{k_c} and the constant, deficit 2
# means e_j(S) = 0 for j NOT in {the two line slots}. Let me just enumerate and find which vanishing
# pattern reproduces the ladder.
from itertools import combinations
import sys
def subgroup_gen(p, n):
    for g in range(2, p):
        x, seen = 1, set()
        for _ in range(p-1):
            x = x*g % p; seen.add(x)
        if len(seen)==p-1:
            cand = pow(g,(p-1)//n,p)
            return cand
    return None
def esymms(elems, p):
    # full elementary symmetric e_1..e_m via Newton from power sums
    m=len(elems)
    pws=[sum(pow(x,j,p) for x in elems)%p for j in range(1,m+1)]
    e=[1]
    for j in range(1,m+1):
        s=0
        for i in range(1,j+1):
            s += (-1)**(i-1)*e[j-i]*pws[i-1]
        e.append(s*pow(j,p-2,p)%p)
    return e  # e[0]=1,e[1]..e[m]

p=97  # has 16 | 96
gen=subgroup_gen(p,16)
H=[pow(gen,i,p) for i in range(16)]
n=16
print(f"p={p} gen={gen} |H|={len(set(H))}")
# Try: deep band deficit-2 for an a-subset (a=r+1). The published ladder is r=3..8 -> a=4..9.
# Hypothesis A: #bad = #{distinct e1(S) : |S|=a, e_2(S)=...=e_{a-2}(S)=0 ?}  (top-2 free: e1,e2 free? no)
# Better hypothesis from CONNECT: bad gamma=-e1, with the line forcing e1 AND e2 jointly. The line is the
# top-freq direction; its deficit-2 fiber over mu_n is exactly the (sum,sumsq) joint level set sliced by
# the line. The COUNT of distinct gamma = distinct e1 achievable. Without the exact line rho, count distinct
# e1 over a-subsets, broken by which e2 they realize, and report the support sizes.
for a in range(4,10):
    e1set=set()
    pairs=set()
    for S in combinations(range(16),a):
        elems=[H[i] for i in S]
        e=esymms(elems,p)
        e1set.add(e[1])
        pairs.add((e[1],e[2]))
    print(f"a={a} (r={a-1}): distinct e1={len(e1set)}  distinct (e1,e2)pairs={len(pairs)}")
