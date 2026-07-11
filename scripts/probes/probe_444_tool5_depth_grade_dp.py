"""
DEPTH-GRADED moment counter for Tool 5 sparsity test.

E_r = #{ (z_1,...,z_{2r}) in mu_n^{2r} : z_1+...+z_{2r} = 0 }  (using -1 in mu_n, so the
balanced-sum moment = zero-sum moment over mu_n^{2r}).  [Equivalent to sum_b|eta_b|^{2r}/q.]

DEPTH GRADING (collision depth):
We group each zero-sum 2r-tuple by its VALUE-MULTIPLICITY PARTITION lambda |- 2r:
the multiset of how many of the 2r coordinates equal each distinct mu_n value used.
'depth' = number of NON-PAIR structural blocks engaged, i.e. how far the solution
is from a pure {x,-x} pairing.  Concretely we grade by:
   D_pairing = (2r) - 2*(# of canceling pairs you can greedily strip)   -- 'residual non-pair mass'
But the CLEANEST, most defensible grading independent of greedy choices:
   grade by  s = number of DISTINCT mu_n-values that appear in the tuple.
The Wick/pairing solutions concentrate at LOW distinct-value counts in a controlled way;
genuine additive coincidences (the char-p excess source) appear as zero-sums whose
multiset is NOT a union of antipodal pairs.

We compute, EXACTLY (integer), the number of ORDERED zero-sum 2r-tuples whose underlying
multiset has a given multiplicity-partition, then aggregate by 'distinct-value count s'
and by 'pairing defect'.  We do this by enumerating multiSETS of size 2r from mu_n that
sum to 0 (unordered), classify each, and multiply by the multinomial (ordered count).

To make it feasible we enumerate multisets via the value-multiplicity vector over the n
group elements with a meet-in-the-middle / DP on the partial sum in F_p.  Since values live
in F_p that's a length-p DP per added element; n elements, total degree 2r.  We use a DP over
(number_used, partial_sum) with per-element multiplicity, but to retain the PARTITION we instead
enumerate by composition.  For the n,r we need (n<=32, 2r<=12) we use a smarter route:

  E_r and its DEPTH PROFILE are obtained from the per-element generating function
     F(t,u; x) = prod_{g in mu_n} ( sum_{m>=0} t^{[m>0]} * (u^? ) * (x^g)^m / m! ...)
  This is complex; instead we use DIRECT enumeration of multisets by a DP that tracks
  (count, sum mod p) AND we recover the partition by enumerating the actual multiset.

PRACTICAL EXACT METHOD (used here): for 2r <= 12 and n <= 32, enumerate all SORTED
index-multisets (i_1<=...<=i_{2r}) of mu_n indices with multiplicity, check zero-sum in F_p,
and bucket by partition.  Count of sorted multisets of size 2r from n symbols = C(n+2r-1,2r).
  n=16,2r=12: C(27,12)=17,383,860  -> feasible
  n=32,2r=12: C(43,12)=~1.9e9      -> NOT feasible by naive enum.
So for n=32 we use a DP that buckets ordered tuples by partition-TYPE via a transfer over
the 'distinct-value count' and 'antipodal-pair count' simultaneously. Implemented below as
exact integer DP keyed on (sum mod p, #coords placed, #distinct values, #full-antipodal-pairs).
"""
import numpy as np
from math import comb
from collections import defaultdict
from functools import lru_cache

def mu_indices_sums(n, p, g, primroot):
    h=pow(primroot,(p-1)//n,p)
    vals=[]; x=1
    for _ in range(n):
        vals.append(x); x=(x*h)%p
    return vals  # list of residues, index i -> mu^i

# ---- Exact ordered zero-sum 2r-tuple count, graded by DISTINCT-VALUE count s ----
# We use DP over elements g_0..g_{n-1}: for each element choose multiplicity m_i>=0,
# total sum m_i = 2r, sum m_i*g_i == 0 mod p. Ordered count = (2r)!/(prod m_i!).
# Grade by s = #{i: m_i>0}.  This is EXACTLY a graded count of E_r by distinct-value depth.
# DP state: (elements_processed, coords_used, sum_mod_p) -> dict {distinct_count: ordered_weight_partial}
# ordered weight accumulates multinomial via 1/m_i! factors -> multiply by (2r)! at end.
# We keep rational via integer: track (2r)! * prod(1/m_i!) as exact integer by deferring.
# Simpler: track count weighted by multinomial directly using integer multinomials at the end
#   is hard in DP; instead track the EXPONENTIAL generating weight w = prod 1/m_i! as Fraction.

from fractions import Fraction

def depth_profile_distinct(n, p, primroot, twor):
    vals = mu_indices_sums(n, p, primroot, primroot)
    # DP: state key (coords_used, sum_mod_p, distinct_used) -> Fraction weight (prod 1/m_i!)
    # iterate elements one at a time
    cur = { (0,0,0): Fraction(1) }
    for gi in vals:
        nxt = defaultdict(Fraction)
        for (used, smod, dist), w in cur.items():
            # choose multiplicity m for this element
            m = 0
            fact = 1
            while used + m <= twor:
                if m == 0:
                    nxt[(used, smod, dist)] += w
                else:
                    fact *= m  # m! incremental
                    nused = used + m
                    nsmod = (smod + m*gi) % p
                    ndist = dist + 1
                    nxt[(nused, nsmod, ndist)] += w * Fraction(1, fact)
                m += 1
        cur = dict(nxt)
    # collect zero-sum, full-size tuples, by distinct count
    from math import factorial
    F = factorial(twor)
    prof = defaultdict(int)
    for (used, smod, dist), w in cur.items():
        if used == twor and smod == 0:
            ordered = w * F
            assert ordered.denominator == 1, (used,dist,ordered)
            prof[dist] += int(ordered)
    return dict(prof)  # {distinct_value_count: ordered_zero_sum_tuple_count}
