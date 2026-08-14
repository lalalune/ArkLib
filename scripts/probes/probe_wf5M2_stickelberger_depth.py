#!/usr/bin/env python3
# wf-M2 PRE-SCREEN: the depth-controlled Stickelberger sufficient lemma.
#
# CONTEXT. M(n) <= C sqrt(n log(p/n)) follows from the char-p deep-moment bound
#   E_r(mu_n) <= (2r-1)!! n^r   at depth  r ~ ln(p/n) ~ beta ln n.
# Char-0 (Lam-Leung) is proven; the OPEN CRUX is the char-p TRANSFER: spurious mod-p
# vanishing configs at depth r that are NOT char-0 (antipodal) coincidences.
#
# The in-tree Stickelberger brick (_BadPrimeBoundCore) proves: an antipodal-free B with
# o_j(B)=0 for ALL odd j in {1,...,k-1}, k=n/4  =>  p <= |B|^2 <= n^2/4.
# That needs ~n/8 window equations. The deep-moment depth is only r ~ beta ln n << n/8.
#
# THE M2 SUFFICIENT LEMMA (depth-r form). Let B subset mu_n antipodal-free, |B|=w,
# beta = sum_{s} w_s zeta_n^s in Z[zeta_n] (w in {-1,0,1}^{n/2} signed pair-indicator).
# If B vanishes mod p at the FIRST R odd power sums o_{j_1},...,o_{j_R} (j_t odd, distinct),
# then beta lies in R distinct primes above p (p totally split since n|p-1), so
#       p^R | N(beta)          (Stickelberger / prime-splitting; NT1)
# Trace identity (NT2, 2-power):  sum_{i=1}^{n/2} |sigma_i(beta)|^2 = (n/2) w.
# AM-GM:  |N(beta)| = sqrt(prod |sigma_i|^2) <= sqrt( ((n/2)w / (n/2))^{n/2} ) = w^{n/4}.
#   => p^R <= w^{n/4}  => p <= w^{(n/4)/R} = w^{n/(4R)}.
#
# SO: a depth-R spurious config of size w forces  p <= w^{n/(4R)} <= (n/2)^{n/(4R)}.
# For this to beat the prize field p = n^beta we need  n^beta > (n/2)^{n/(4R)},
# i.e.  beta < n/(4R) roughly, i.e.  R < n/(4 beta).  Since deep-moment depth R ~ beta ln n,
# the condition  beta ln n < n/(4 beta)  i.e.  R << n  holds with HUGE slack at prize scale
# (n=2^30, beta~4: n/(4 beta)~6.7e7 vs R~beta ln n ~ 83).  *** This is the whole point. ***
#
# BUT THE WALL: the AM-GM step requires the trace identity over the FULL degree n/2, while we
# only have R vanishing equations placing beta in R primes. The norm bound p^R | N(beta) is
# correct, but |N(beta)| <= w^{n/4} is the AM-GM ceiling regardless of R — so the bound
# p <= w^{n/(4R)} is VALID but only NON-VACUOUS (p<=n^2/4-ish) when R ~ n/8. For small R the
# RHS w^{n/(4R)} is astronomically large => NO constraint on the prize prime. This is exactly
# the n^{Theta(log n)} largest-bad-prime growth the campaign measured.
#
# THIS PROBE measures, for the worst spurious config that vanishes at depth R, the ACTUAL
# largest p that admits it, vs the Stickelberger ceiling p <= w^{n/(4R)}, to see (a) the bound
# is correct (no p exceeds the ceiling) and (b) whether the ACTUAL largest bad prime is much
# smaller (=> a SHARPER lemma might close it) or tracks the ceiling (=> route is DEAD: the
# generic prize prime IS bad at the deep-moment depth, confirming the conservation law).

import itertools, math
from sympy import isprime, primitive_root

def musub(n, p):
    g = primitive_root(p); h = pow(g, (p-1)//n, p)
    return [pow(h, j, p) for j in range(n)]

def primes_1modn(n, lo, hi, count):
    out=[]; m=max(1,(lo)//n)
    while len(out)<count:
        p=n*m+1
        if p>lo and isprime(p): out.append(p)
        m+=1
        if p>hi: break
    return out

# For small n, enumerate antipodal-free B and find, for each R (number of leading odd-window
# equations satisfied), the largest prime p (n|p-1) admitting a NONEMPTY genuine (non-char-0)
# such B. "genuine" = not forced by char-0 antipodal structure: we detect by requiring the
# config to vanish mod p but the corresponding integer signed sum NOT vanish over Z.

def signed_vec_to_complex_sum(choice, n, j):
    # over Z[zeta_n]: o_j = sum_{s: c_s=1} zeta^{s j} + sum_{s:c_s=2} zeta^{(s+n/2) j}
    # we test char-0 vanishing numerically
    half=n//2; tot=0j
    for s,c in enumerate(choice):
        if c==1: a=s
        elif c==2: a=s+half
        else: continue
        tot += complex(math.cos(2*math.pi*a*j/n), math.sin(2*math.pi*a*j/n))
    return tot

def analyze(n, plist):
    half=n//2
    odd_js=[j for j in range(1,n) if j%2==1]
    results={}  # R -> (max_p, ceiling_at_that_w, example)
    for p in plist:
        roots=musub(n,p)
        for choice in itertools.product((0,1,2), repeat=half):
            if all(c==0 for c in choice): continue
            B=[]
            for s,c in enumerate(choice):
                if c==1: B.append(roots[s])
                elif c==2: B.append(roots[s+half])
            w=len(B)
            # count leading odd-window equations satisfied mod p
            R=0
            for j in odd_js:
                if sum(pow(b,j,p) for b in B)%p==0: R+=1
                else: break
            if R==0: continue
            # is it char-0 genuine? check o_1..o_R don't all vanish over Z
            genuine = any(abs(signed_vec_to_complex_sum(choice,n,odd_js[t]))>1e-6 for t in range(R))
            if not genuine: continue
            ceiling = w**(n/(4*R)) if R>0 else float('inf')
            key=R
            if key not in results or p>results[key][0]:
                results[key]=(p, ceiling, w)
    return results

print("wf-M2 depth-Stickelberger pre-screen: largest GENUINE (non-char-0) spurious prime by depth R")
print("ceiling = w^(n/(4R)) is the Stickelberger/AM-GM bound; valid iff observed max_p <= ceiling\n")
for n in [8,16]:
    plist=primes_1modn(n, n*n, n*n*200, 30)  # p > n^2 to clear the char-q pollution threshold
    print(f"n={n}, primes tested {plist[0]}..{plist[-1]} ({len(plist)} primes, all > n^2={n*n})")
    res=analyze(n,plist)
    for R in sorted(res):
        mp,ceil,w=res[R]
        ok = "OK(p<=ceil)" if mp<=ceil+1 else "VIOLATION!"
        print(f"   R={R:2d}: largest genuine bad p={mp:7d}  w={w}  ceiling w^(n/4R)={ceil:.3e}  {ok}")
    print()
