# Char-0 (faithful = O172 worst case) reproduction of the deep-band #bad ladder for n=16.
# Work in the cyclotomic field Q(zeta_16) using sympy exact arithmetic so e1 values are NOT collapsed.
# mu_16 = {zeta^j}. For an a-subset S (a=r+1), gamma = -e1(S). Deep band deficit-2 = the (e1,e2) pair
# lies on the line's deficit-2 fiber. The DEEP-BAND condition that defines a "bad" config (a config with
# a genuine deficit-2 collision on a single top-frequency line) is the O150-style symmetric-vanishing:
# all elementary symmetric functions e_j(S) = 0 EXCEPT the top two carried by the line.
#
# For the TOP-FREQUENCY line at agreement a0=r+1 with deficit 2: the pencil prod_{s in S}(x-s) must,
# modulo the line word x^{k_c}+gamma..., have only its top two coeffs free. Equivalently the lower
# elementary symmetric e_3, e_4, ..., e_{a} must take the SPECIFIC values the line forces. The single
# clean characterization that the in-tree census uses (probe_o150) is: e_j = 0 for the "interior"
# indices. For a deficit-2 band on an a-subset the bad configs are those with e_3=e_4=...=e_a = 0
# leaving e_1,e_2 free (the two line slots). Let me test THAT, in char 0, counting distinct e1.
import itertools
import sympy as sp

def run(n):
    z = sp.exp(2*sp.pi*sp.I/n)
    M = [sp.nsimplify(sp.simplify(z**j), [sp.pi]) for j in range(n)]  # exact roots of unity
    # use exact algebraic numbers via sympy Rational+I won't be exact; instead use cyclotomic via expand
    M = [sp.cos(2*sp.pi*j/n) + sp.I*sp.sin(2*sp.pi*j/n) for j in range(n)]
    results={}
    for a in range(4, n//2+2):
        e1vals=set()
        for S in itertools.combinations(range(n), a):
            elems=[M[i] for i in S]
            # elementary symmetric e_j
            # build polynomial coeffs
            poly=sp.prod([sp.Symbol('x')-e for e in elems])
            # too slow; compute e_j directly
            pass
        results[a]=None
    return results

# sympy exact over 16 elements with C(16,9)=11440 subsets and full e_j is heavy. Use a LARGE PRIME instead,
# big enough that e1 doesn't wrap: need p >> n^? . e1 = sum of <=9 roots; in char 0 the spectrum has ~Theta(n^3)
# distinct values for the bad set. Use p ~ 10^9 with 16|p-1.
print("switching to large-prime faithful model below")
