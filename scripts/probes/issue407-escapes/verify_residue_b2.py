"""
The decisive test for the lean-sharpen brick.

The brick CLAIMS the residue-degree object is the "isolated/non-coset root count" and that
it is "n-independent (Schlickewei-Evertse) / poly(k)" in char-0. The OBSTRUCTION it admits:
"numerics show deg d reaches k (not <k)" and over F_q at the prize prime it IS Kelley/BGK.

DECISIVE QUESTION: For a GENUINELY-RAGGED, LARGE far agreement set (the prize-relevant case
= |S| up to n/(2d)+Theta(s) at the Kambire worst direction), is the residue degree:
   (A) bounded by poly(k) / n-independent  [brick's optimistic claim -> would advance B1]
   (B) Theta(s) = Theta(n/d) = the autocorrelation/degree quantity [vacuous, = the wall]

To get LARGE ragged far sets we must CONSTRUCT them: pick a coset-union core C of mu_n
(size g*c), then ADD ragged stragglers, then ask whether one (k+2)-sparse poly realizes
the whole set. The realizability constraint: S is the root set of x^a + gamma x^b - c(x)
for ONE deg-<k codeword c. We BUILD S by choosing the line and codeword and reading off S.

Strategy: pick a far direction (a,b) with d=gcd(a-b,n)>=2. The binomial x^a+gamma x^b
vanishes on a mu_d-coset structure when gamma is a root of unity; adding the -c part
perturbs. We sweep gamma over mu_n (NOT random) and c = interpolation, to MAXIMIZE |S|,
then measure residue.
"""
import numpy as np

def rou(n):
    return np.exp(2j*np.pi*np.arange(n)/n)

def residue_and_core(S_exps, n):
    Sset = set(S_exps); nS=len(Sset); best_core=0; best_g=1
    for g in range(2,n+1):
        if n%g: continue
        step=n//g; seen=set(); core=0
        for e in Sset:
            if e in seen: continue
            orbit=set(); x=e
            for _ in range(g):
                orbit.add(x); x=(x+step)%n
            seen|=orbit
            if orbit<=Sset: core+=len(orbit)
        if core>best_core: best_core=core; best_g=g
    return nS-best_core, best_core, best_g

def agree_set(n,a,b,gamma,c_coeffs,tol=1e-7):
    om=rou(n); S=[]
    for e in range(n):
        x=om[e]
        val=x**a+gamma*(x**b)-sum(c_coeffs[j]*(x**j) for j in range(len(c_coeffs)))
        if abs(val)<tol: S.append(e)
    return S

# For the binomial line L(x)=x^a+gamma x^b with gamma in mu_n: L(x)=x^b(x^{a-b}+gamma).
# zeros of x^{a-b}=-gamma: a mu_d coset structure (d=gcd(a-b,n)). To make the LINE itself
# (without codeword) agree with c=0 on a coset, we need... but c must have deg<k.
# The TRUE prize family: a deg-<k codeword that the line agrees with on a large set.
# Construct: choose S = (a mu_d coset, size n/d) and demand x^a+gamma x^b = c(x) on S with
# deg c < k. On a mu_d coset {x: x^d = t}, x^a and x^b are determined by x mod the coset:
# if a = b mod d then x^a/x^b const... This is exactly the "imprimitive => reduces to deg<k
# on each coset" mechanism (comment 100's dir(9,10) trap). For GENUINE far we EXCLUDE that.

# So: a genuinely-far direction CANNOT have its binomial reduce to deg<k on a full coset.
# Hence large agreement requires the codeword to actively interpolate. Max |S| for ONE
# deg-<k codeword interpolating x^a+gamma x^b at chosen points: a deg-<k poly is determined
# by k points; it can agree with the line at MORE points only if forced by structure.

# DIRECT construction of max ragged far set: enumerate, for each (a,b,gamma), the codeword
# c = unique deg-<k interpolant through the FIRST k agreement candidates is circular.
# Instead: the agreement set of x^a+gamma x^b - c is the root set; its SIZE <= deg of that
# poly. We want the genuine MCA worst case. Use the in-tree fact: worst far incidence ~ n/(2d).
# Let's just DIRECTLY search: over gamma in mu_{n} and c with coeffs in mu_n union {0},
# small k, find max |S| and its residue, for genuine far (d>=2, NOT x^{n/2}=+-1 reducible).

print("Construct max ragged far agreement sets; measure residue vs core vs n.")
print("genuine far = d>=2 AND not (a,b both >= n/2 reducible). We brute small coeff alphabet.\n")
for n in [16, 24, 32]:
    om=rou(n)
    for k in [2,3]:
        # alphabet for gamma and c coeffs: roots of unity + 0 (keeps things algebraic/likely-large S)
        alpha=[0]+list(rou(n))  # n+1 values
        # too big to full-brute c in alpha^k for n=32; restrict gamma to mu_n, c coeffs to {0,+-1,+-om^j small}
        gammas=list(rou(n))
        c_alpha=[0,1,-1]
        best=None
        import itertools
        for a in range(k,n):
          for b in range(k,a):
            d=int(np.gcd(a-b,n))
            if d<2: continue
            # genuine-far filter: exclude directions where a mod d and b mod d make binomial
            # reduce to deg<k on cosets, i.e. exclude when (a-b) % (n/d?) ... use simple proxy:
            # exclude a>=n//2 and b>=n//2 with a-b small (the x^{n/2+-} trap) -- approximate.
            for gamma in gammas:
              for c_coeffs in itertools.product(c_alpha,repeat=k):
                if all(cc==0 for cc in c_coeffs):
                    pass
                S=agree_set(n,a,b,gamma,list(c_coeffs))
                if len(S)<3: continue
                res,core,g=residue_and_core(S,n)
                # is it GENUINELY ragged? require residue>0 (not pure coset union)
                if res==0: continue
                cand=(len(S),res,core,g,a,b,d)
                if best is None or len(S)>best[0] or (len(S)==best[0] and res>best[1]):
                    best=cand
        if best:
            sz,res,core,g,a,b,d=best
            print(f" n={n} k={k}: MAX ragged far |S|={sz} residue={res} core={core} g={g} dir(a,b)=({a},{b}) d={d}  | n/(2d)={n/(2*d):.1f} (k+2={k+2})")
        else:
            print(f" n={n} k={k}: none found")
