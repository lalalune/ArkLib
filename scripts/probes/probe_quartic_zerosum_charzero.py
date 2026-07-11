import itertools, cmath, math
# mu_n = n-th roots of unity in C, n = 2^k. Count ordered 4-tuples (a,b,c,d) with a+b+c+d=0.
# Hypothesis: over C with n=2^k, every vanishing 4-sum decomposes into two antipodal pairs.
# i.e. the multiset {a,b,c,d} = {x,-x,y,-y}. Count should match the "antipodal pairing" formula.

def roots(n):
    return [cmath.exp(2j*math.pi*t/n) for t in range(n)]

def zerosumcount4(n, tol=1e-9):
    R = roots(n)
    cnt = 0
    pairing_cnt = 0
    nonpair = []
    for idx in itertools.product(range(n), repeat=4):
        s = sum(R[i] for i in idx)
        if abs(s) < tol:
            cnt += 1
            # check antipodal-pairing: can we partition the 4 indices into 2 antipodal pairs?
            # antipode of index i is (i + n/2) mod n
            anti = lambda i: (i + n//2) % n
            a,b,c,d = idx
            # 3 ways to pair (a,b)(c,d), (a,c)(b,d), (a,d)(b,c)
            ok = False
            for (p,q),(r2,s2) in [((a,b),(c,d)),((a,c),(b,d)),((a,d),(b,c))]:
                if anti(p)==q and anti(r2)==s2:
                    ok=True;break
            if ok: pairing_cnt += 1
            else: nonpair.append(idx)
    return cnt, pairing_cnt, nonpair

# Closed form for antipodal-pairing ordered 4-tuple count over mu_n (n even):
# choose which positions form pairs. Number of ordered tuples that are union of 2 antipodal pairs.
# Each antipodal pair is {x,-x}; there are n ordered "first elements" but pair unordered = n choices of x give pair, but {x,-x}={-x,x}.
# Easier: count ordered 4-tuples (a,b,c,d) s.t. they pair antipodally.
# Let A = anti map. Conditions per pairing pattern. Use inclusion to verify only.
def closed_form_guess(n):
    # ordered 4-tuples that are exactly two antipodal pairs (with multiplicity via the 3 pairings, minus overcount)
    # Just brute count "is union of two antipodal pairs" = pairing_cnt above; we compare.
    return None

for k in range(1,7):
    n = 2**k
    cnt, pc, nonpair = zerosumcount4(n)
    print(f"n=2^{k}={n}: zeroSumCount4={cnt}, antipodal-paired={pc}, NON-paired={cnt-pc}, examples_nonpair={nonpair[:3]}")
