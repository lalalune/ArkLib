"""
FAST exact depth grading by DISTINCT-VALUE COUNT, via inclusion-exclusion over support size,
computed with FFT convolutions over Z/p.

Let N_s = # ordered zero-sum 2r-tuples using EXACTLY s distinct mu_n-values.
Let T_S = # ordered zero-sum 2r-tuples whose values lie in a FIXED s-subset S of mu_n,
using all coords (each coord any element of S). By symmetry over which subset,
sum over s-subsets of T_S counts tuples with support CONTAINED in some s-set with multiplicity.
Standard: let f(s) = sum over all s-subsets S of (# zero-sum 2r-tuples with all coords in S)
                   = sum over s-subsets S of [x^0] (sum_{g in S} x^g)^{2r}   (coeff extraction in Z/p)
Then the number using support of size EXACTLY j is, with g(j)=N_j,
   f(s) = sum_{j<=s} C(n-j, s-j) g(j)   [choose the extra s-j values among remaining n-j]
Invert: g(s) = sum_{j<=s} (-1)^{s-j} C(n-j, s-j) f(j).
We compute f(s) for s=1..2r by: for each s-subset... that's C(n,s) subsets, too many for n=32.
INSTEAD compute h(s) := sum over s-subsets S of [x^0](sum_{g in S} x^g)^{2r} via a generating
function over subsets: define per-element variable. We need, for fixed total power 2r,
   F(z) = sum_S z^{|S|} (sum_{g in S} x^g)^{2r}  -- not multiplicative because power 2r couples elements.
So expand multinomially: (sum_{g in S} x^g)^{2r} = sum over ordered tuples in S^{2r} x^{sum}.
Thus h(s) = sum over ORDERED 2r-tuples t with zero-sum, weighted by C(n - |supp(t)|, s - |supp(t)|).
=> h(s) = sum_j g(j) C(n-j, s-j).  (same relation) -- circular.

DIRECT feasible route: compute g(j) = N_j via the per-element multiplicity DP BUT track the
partial sum as a numpy int64 histogram over Z/p (length p) and the distinct-count as a separate
axis. Memory = p * (2r+1) * (2r+1) int64. For p~1.15e6, 2r=12: 1.15e6*13*13*8 bytes ~ 1.5 GB. Heavy.
We reduce: distinct-count and coords-used are bounded by 2r<=12; we can collapse to track only
(coords_used, distinct_used) -> length-p int64 vector. That's (13*13) vectors * p * 8 = ok ~1.5GB.
Use FFT-based convolution per element is overkill; per element we add multiplicities 0..remaining.

We implement: state[c][d] = int64 array len p (counts of partial sums using c coords, d distinct vals).
For each group element g (residue rg), update: choosing multiplicity m>=1 for this NEW element
shifts the histogram by m*rg and multiplies the ordered weight... but ORDERED count needs multinomial
which the per-element 1/m! EGF handles only with rationals. To keep integers, we instead compute the
UNORDERED multiset count per (c,d, sum) then convert: ordered = sum over multisets of multinomial.
That needs the full multiplicity vector. SO we keep the EGF-rational DP but vectorize the sum axis.

We use float128? No. We use the EGF with a common denominator: multiply everything by (2r)! at the end;
intermediate weights are multiples of 1/(prod m_i!). Track as Python-int numerators over a FIXED
denominator lcm? Simpler and EXACT: track weight as fraction-free by storing ordered partial counts
using the identity: ordered count of placing the chosen multiplicities = multinomial. We can build
ordered counts incrementally: if we decide to add an element with multiplicity m into a tuple that
currently has c coords already placed (ordered), the number of ways to INTERLEAVE is C(c+m, m).
=> ordered_new = ordered_old * C(c+m, m). This is EXACT INTEGER and avoids factorials!
State: ordered[c][d] = int64 array len p. Transition for new element rg, choose m in 0..(2r-c):
   if m==0: copy. else ordered[c+m][d+1] += shift(ordered[c][d], m*rg) * C(c+m,m).
Final: g(d) = ordered[2r][d][0].  EXACT.
"""
import numpy as np
from math import comb

def mu_res(n,p,pr):
    h=pow(pr,(p-1)//n,p); out=[]; x=1
    for _ in range(n): out.append(x); x=(x*h)%p
    return out

def depth_profile_distinct_fast(n,p,pr,twor):
    res=mu_res(n,p,pr)
    # ordered[c][d] : np.int64 array length p (use python int via object? overflow risk)
    # counts can exceed int64 at r=6,n=32 (E_6 ~ 7e12 < 9.2e18 int64 max -> OK). Use int64.
    P=p
    # store as dict to save memory: ordered[(c,d)] = np.ndarray int64 length P, mostly we only need nonzero
    from collections import defaultdict
    ordered=defaultdict(lambda: None)
    z=np.zeros(P,dtype=np.int64); z[0]=1
    ordered[(0,0)]=z
    for rg in res:
        new=defaultdict(lambda: None)
        for (c,d),vec in ordered.items():
            if vec is None: continue
            # m=0 keep
            if new[(c,d)] is None: new[(c,d)]=vec.copy()
            else: new[(c,d)]+=vec
            # m>=1
            for m in range(1, twor-c+1):
                nc=c+m; nd=d+1
                fac=comb(nc,m)  # interleave ways
                shifted=np.roll(vec,(m*rg)%P)*fac
                if new[(nc,nd)] is None: new[(nc,nd)]=shifted.copy()
                else: new[(nc,nd)]+=shifted
        ordered=new
    prof={}
    for (c,d),vec in ordered.items():
        if c==twor and vec is not None and vec[0]!=0:
            prof[d]=int(vec[0])
    return prof

if __name__=="__main__":
    import sympy, time
    # validate against the slow DP at n=16 p=65537
    n=16;p=65537;pr=int(sympy.primitive_root(p))
    for twor in [8,10]:
        t=time.time(); prof=depth_profile_distinct_fast(n,p,pr,twor)
        print(f"FAST n={n} 2r={twor}: {dict(sorted(prof.items()))} tot={sum(prof.values())} t={time.time()-t:.1f}s", flush=True)
