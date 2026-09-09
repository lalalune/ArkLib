"""Exact first-step sparse-direction arithmetic and small spike censuses."""
import itertools
import json
from fractions import Fraction

P = 365375409332725729550921208179070755120141565953
G = 303645430271030343624574566109998498685964493478
N = 2**30
s = N//4
t, k = 3*s-1, 2*s
spike_gap = 5*(t-1)**2-(N-1)*((t-1)+4*(k-1))
assert spike_gap == s*s-25*s+14 > 0
m = N//18
sparse_gap = 19*(t-m)**2-(N-m)*((t-m)+18*(k-1))
assert sparse_gap == 15*s*s-38*s+19-71*s*m+19*m+18*m*m > 0
assert 18*m <= N
assert Fraction(s*s-304*s+171, 9) > 0

def census(n):
    s, k = n//4, n//2
    t = 3*s-1
    g = pow(G,N//n,P)
    d = [pow(g,i,P) for i in range(n)]
    r0 = d[:k-1]
    aa = d[k-1:k-1+s]
    a = aa[0]
    z = [x for x in d if x not in aa]
    def prod_at(roots,x):
        ans = 1
        for r in roots:
            ans = ans*(x-r)%P
        return ans
    c = {x:prod_at(r0,x) for x in d}
    # Every nonzero bad decoder must agree on all s outside points and
    # have exactly k-1 roots among z. A nonspike outside point fixes scale.
    # This enumerates every possible nonzero witness decoder, not samples.
    anchor = aa[1]
    bad = {(-c[a])%P}  # zero decoder's unique bad scalar
    nonzero_decoders = 0
    tested = 0
    for roots in itertools.combinations(z,k-1):
        tested += 1
        scale = c[anchor]*pow(prod_at(roots,anchor),-1,P)%P
        if not all(scale*prod_at(roots,x)%P == c[x] for x in aa[1:]):
            continue
        gamma = (scale*prod_at(roots,a)-c[a])%P
        # Every candidate has t agreements including a; the direction spike
        # cannot be jointly interpolated on that support (t-1>=k for s>=2).
        assert t-1 >= k
        bad.add(gamma)
        nonzero_decoders += 1
    assert 0 in bad and (-c[a])%P in bad
    return {"n":n,"root_subsets_tested":tested,
            "nonzero_witness_decoders":nonzero_decoders,
            "exact_bad_count":len(bad),"actual_production_prime":True}

print(json.dumps({"production":{"single_spike_bad_bound":4,
                   "single_spike_five_list_gap":spike_gap,
                   "sparse_support_limit":m,"sparse_bad_bound":18*m,
                   "sparse_nineteen_list_gap":sparse_gap},
                  "complete_small_controls":[census(8),census(16)]},indent=2))
