import numpy as np
from itertools import product

# Test the agent's central claims for the B1 / R-thin / Hankel-rank route over PRIME fields F_p
# with mu_n = 2-power subgroup. We test:
#  (1) "ragged excess <= t-1" (t = sparsity = k+2). The in-tree _IsolatedCountKelley says this is FALSE (iso ~= k+2 = t).
#  (2) n-independence of the isolated/ragged-excess count.
#  (3) whether the binding far direction is LOW-exponent x^k (comment 125) -> would make it secretly BGK.

def find_primes_with_subgroup(n, count=6, start=3):
    # primes p with n | (p-1), so mu_n exists in F_p
    primes = []
    p = start
    while len(primes) < count:
        p += 1
        # primality
        if p < 2: continue
        is_p = all(p % d for d in range(2, int(p**0.5)+1))
        if is_p and (p-1) % n == 0:
            primes.append(p)
    return primes

def subgroup(p, n):
    # generator of mu_n
    # find primitive root g, then g^((p-1)/n)
    def is_primroot(g):
        seen=set(); x=1
        for _ in range(p-1):
            x=(x*g)%p; seen.add(x)
        return len(seen)==p-1
    g=2
    while not is_primroot(g): g+=1
    h=pow(g,(p-1)//n,p)
    S=[pow(h,j,p) for j in range(n)]
    assert len(set(S))==n
    return S

def agreement_count(p, n, a, b, gamma, k, mu):
    # codeword c = polynomial of degree < k. We search over ALL deg<k codewords? Too many.
    # Instead: for each direction (a,b,gamma), the agreement set S = {x in mu : x^a + gamma x^b = c(x)} for SOME deg<k c.
    # The max agreement = max over subsets T of mu with |T|>=? that are interpolable by deg<k poly equal to (x^a+gamma x^b) on T.
    # A set T is "explained" by a deg<k codeword iff the values v(x)=x^a+gamma x^b on T are interpolated by a deg<k poly.
    # Equivalent: the divided differences / the unique interpolating poly through ALL points of T has degree < k.
    # We want the LARGEST agreement set. Standard: agreement set of x^b-direction with a deg<k poly is the root set of
    # P = x^a + gamma x^b - c, |S| <= deg P. For monomial single direction it's cleaner. Let's just directly:
    # For a GIVEN c, S = {x in mu: x^a+gamma x^b == c(x)}. Max over c of |S| with the constraint that S is "ragged".
    # This is expensive. Instead measure the ISOLATED count directly via the literature object:
    pass

# Simpler & decisive: directly test claim (1)/(2) the way _IsolatedCountKelley measured it.
# The isolated count = # nonzero roots in mu_n of a (k+2)-sparse poly h = c - x^a - gamma x^b that lie on NO nontrivial coset.
# We'll randomly sample sparse polys h with support in {0..k-1} U {a,b}, coeffs in F_p, count roots in mu_n,
# subtract those forming full mu_d cosets, and track the max "ragged/isolated" remainder.

def roots_in_subgroup(p, coeffs_dict, S):
    # coeffs_dict: exponent -> coeff (mod p). S = subgroup elements.
    out=[]
    for x in S:
        val=0
        for e,co in coeffs_dict.items():
            val=(val+co*pow(x,e,p))%p
        if val==0: out.append(x)
    return out

def coset_structure(roots, p, n, S, divisors):
    # For each divisor d>1 of n, mu_d = {x: x^(n/d? )...}. mu_d as subgroup of order d: elements g^(j*n/d).
    # A root set contains a full mu_d-coset (x0 * mu_d) if for some x0 in roots, all x0*mu_d in roots.
    # We strip maximal coset unions; remainder = ragged/isolated.
    rset=set(roots)
    # build mu_d for each d|n, d>1
    # need generator h of mu_n
    # reconstruct: S is ordered as h^0..h^{n-1}
    idx={S[j]:j for j in range(n)}
    rem=set(rset)
    for d in sorted(divisors, reverse=True):
        if d<=1: continue
        # mu_d = {h^{j*(n/d)} : j} -> indices multiples of n/d
        step=n//d
        # a coset is x0*mu_d: indices {i0 + j*step mod n}
        for i0 in range(step):
            coset_idx=[(i0 + j*step)%n for j in range(d)]
            coset=set(S[i] for i in coset_idx)
            if coset<=rem:
                rem-=coset
    return rem

# run sweep
def divisors_of(n):
    return [d for d in range(1,n+1) if n%d==0]

results={}
import random
random.seed(1)
for n in [16,32,64]:
    divs=divisors_of(n)
    primes=find_primes_with_subgroup(n, count=4, start=max(200,2*n))
    for k in [4,6]:
        worst_iso=0; worst_info=None
        for p in primes:
            S=subgroup(p,n)
            # sample directions a,b and codeword coeffs to build h
            for trial in range(3000):
                a=random.randrange(k, n)  # high exponent
                b=random.randrange(0, n)
                if a==b: continue
                # h = (x^a + gamma x^b) - c, support {0..k-1, a, b}
                cd={}
                cd[a]=cd.get(a,0)+1
                gamma=random.randrange(1,p)
                cd[b]=cd.get(b,0)+gamma
                for e in range(k):
                    cd[e]=(cd.get(e,0) - random.randrange(0,p))%p
                cd={e:co%p for e,co in cd.items() if co%p!=0}
                if not cd: continue
                rts=roots_in_subgroup(p,cd,S)
                rem=coset_structure(rts,p,n,S,divs)
                if len(rem)>worst_iso:
                    worst_iso=len(rem); worst_info=(p,a,b,k,len(rts))
        t=k+2
        results[(n,k)]=(worst_iso, t, t-1, worst_info)
        print(f"n={n} k={k}: max ragged/isolated={worst_iso}  t=k+2={t}  claim(t-1)={t-1}  iso<=t-1? {worst_iso<=t-1}  info={worst_info}")

