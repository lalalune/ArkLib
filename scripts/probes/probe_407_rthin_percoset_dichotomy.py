import math, sympy
from itertools import combinations
# PER-COSET DEGREE-COUNTING ARGUMENT (the deliverable route).
# On a single mu_d-coset z*mu_d (d points {z*omega^j}), write the codeword's restriction.
# c(z omega^j) = sum_{l<k} c_l z^l omega^{lj} = sum_{r=0}^{d-1} omega^{rj} * (sum_{l<k, l=r mod d} c_l z^l)
#             = sum_{r=0}^{d-1} omega^{rj} * C_r(z)   where C_r(z) collects degree-=r-mod-d terms.
# The number of NONZERO frequencies r is at most the number of residues r in [0,d) that have a
# degree-<k representative = #{r : 0<=r<d, r < k or ...} = min(d, k) ... more precisely
# #{r in 0..d-1 : exists l, l<k, l=r mod d} = min(d,k) for k<=d, and = d for k>=d... 
# Actually = number of residues hit by {0,1,..,k-1} mod d = min(d,k).
# Call Kc = #frequencies of c on a coset <= min(d,k). Actually it equals
#   #distinct (l mod d) for l in 0..k-1 = min(d, k).
# The LINE on the coset is the SINGLE frequency r0 = a mod d (amplitude w_gamma(z)).
# Agreement of c with line on the coset <=> the function j |-> c(zomega^j) - w(z)omega^{r0 j}
# vanishes. This is a sum of at most Kc+1 frequencies (the line freq may coincide with a c-freq).
# A nonzero "d-periodic exponential polynomial" with m nonzero frequencies, as a polynomial in
# Y=omega^j of degree < d with m nonzero coeffs, restricted to Y in mu_d: number of zeros among
# the d points = number of mu_d roots of a poly with m nonzero terms.
# KEY LEMMA (over a field, char nmid n): a nonzero univariate poly P(Y) with EXACTLY m nonzero
# terms has at most m-1 ROOTS THAT ARE ROOTS OF UNITY in any single coset... NO.
# Correct tool: P(Y) = sum over m freqs c_r Y^r (0<=r<d). #roots of P on mu_d <= deg if no
# special structure, BUT we want: if c agrees with line on > (Kc+1-1)=Kc points of a coset and
# the difference is a sum of <= Kc+1 chars then... a sum of <=Kc+1 distinct chars vanishing at
# Kc+1 points of mu_d forces it identically zero ONLY IF the Kc+1 chars' Vandermonde is
# invertible -- which it is (distinct frequencies => Vandermonde in distinct omega^r nonsingular).
# THEREFORE: if c=line on >= Kc+1 points of a coset, the difference (<=Kc+1 freqs) vanishes on
# >= Kc+1 points => its <=Kc+1 frequency-coefficients all vanish => c=line on the WHOLE coset.
# CONCLUSION (per-coset dichotomy): on each mu_d-coset, EITHER c=line on the full coset, OR they
# agree on <= Kc = #{distinct (l mod d): l<k} = min(d,k) points... let me re-derive the count:
#   agree on >= (#nonzero freqs of difference) points => full coset.
#   #nonzero freqs of difference <= Kc+1 if line freq is NEW, else <= Kc.
# So PARTIAL agreement on a coset is <= Kc (if line freq among c-freqs) or <= Kc (since at the
# threshold Kc+1 it becomes full). Precisely: partial agreement <= (#freqs of difference) - 1.
# Let me just MEASURE #freqs and the per-coset partial cap empirically.

def find_w(p,n):
    g=sympy.primitive_root(p); return pow(g,(p-1)//n,p)
def Kc_count(k,d):
    return len(set(l % d for l in range(k)))   # = min(k,d)
# verify the per-coset dichotomy claim: take random deg<k codeword, a line, and for each coset
# count agreement; check partial agreement <= (#freqs of difference)-1 and that exceeding it = full.
import random
def test(n,k,p,a,b,trials=2000):
    w=find_w(p,n); d=math.gcd(a-b,n); nod=n//d
    Kc=Kc_count(k,d)
    r0=a % d
    # #freqs of difference: c has freqs = {l mod d : l<k}; difference adds r0 if not present
    cfreqs=set(l%d for l in range(k))
    diff_freqs = cfreqs | {r0}
    m = len(diff_freqs)
    max_partial=0
    random.seed(0)
    for _ in range(trials):
        coeffs=[random.randrange(p) for _ in range(k)]
        for gamma in [random.randrange(p) for _ in range(3)]:
            for cidx in range(nod):  # coset rep index
                z=pow(w,cidx,p)
                agree=0; tot=0
                for j in range(d):
                    x=(z*pow(w,j*nod,p))%p
                    cx=sum(coeffs[l]*pow(x,l,p) for l in range(k))%p
                    lx=(pow(x,a,p)+gamma*pow(x,b,p))%p
                    if cx==lx: agree+=1
                    tot+=1
                if agree<d:  # partial
                    max_partial=max(max_partial,agree)
    return d,Kc,r0,m,max_partial
print("Per-coset: claim partial-agreement <= m-1 where m = #distinct freqs of (c-line) on coset")
print("           m = |{l mod d: l<k} U {a mod d}|.  Full coset if agree=d.")
for (n,k) in [(16,4),(16,2),(16,6),(32,8),(24,6)]:
    p=17
    while (p-1)%n or not sympy.isprime(p): p+=1
    for d in [2,4,8]:
        if n%d: continue
        a=k+ (d if k+d<n else 0)
        # pick a,b with gcd(a-b,n)=d
        a = n-1 if (n-1) - d>=1 else k+1
        b = a-d
        if b<1: continue
        dd,Kc,r0,m,mp=test(n,k,p,a,b)
        ok = mp <= m-1
        print(f" n={n} k={k} p={p} (a,b)=({a},{b}) d={dd} Kc=min(k,d)={Kc} m={m}: max_partial_agree={mp}  (m-1={m-1}) {'OK' if ok else 'VIOLATION'}",flush=True)
print("ALLDONE",flush=True)
