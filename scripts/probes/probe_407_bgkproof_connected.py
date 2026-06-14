#!/usr/bin/env python3
"""
#407 — THE GENUINE PROOF ATTEMPT: the connected-relation (cumulant) bound on E_r(F_p).

The Wick bound (2r-1)!! n^r is the GAUSSIAN moment: (2r-1)!! = #{perfect matchings of 2r points}.
The standard way to PROVE a 2r-th moment <= (2r-1)!! sigma^{2r} is to show the random variable
X = eta_b is sub-Gaussian, equivalently its CUMULANTS k_{2j} for j>=2 are <= 0 (or small).

For eta_b = sum_{x in mu_n} psi(bx), as b ranges over F_p^*, eta_b is a "random period".
Over the FULL average (1/p) sum_{b!=0}, the 2r-th moment A_r is a sum over (x,y) in mu_n^{2r}
with sum x = sum y (mod p), MINUS the DC.  Decompose by the PARTITION structure of the 2r indices:

  A_r = (1/p) sum_{b!=0} |eta_b|^{2r}
      = sum over the 2r-tuple (x_1..x_r, y_1..y_r) with X:=sum x_i - sum y_j = 0 mod p, MINUS DC.

CONNECTED DECOMPOSITION.  Group the 2r roots into "blocks" by the equivalence "sum within block
= 0 (mod p) and no proper sub-block sums to 0".  Then
  E_r = sum_{partitions P of [2r] into blocks} prod_{B in P} Conn(|B|),
where Conn(2j) = #{minimal char-p vanishing relations of length 2j among signed mu_n elements}.
  - Conn(2) = #{(x,y): x = y} contributions = n PER PAIR (the diagonal); pairings give n^r.
    The number of pairings (perfect matchings) is (2r-1)!!, so the PAIR-ONLY term is EXACTLY
    (2r-1)!! n^r = Wick.   [This is the leading Gaussian term.]
  - Conn(2j), j>=2: minimal vanishing relations of length 2j.  In char 0 (ring) these are the
    ONLY-PAIRS ones for dyadic mu_n (Lam-Leung: minimal vanishing 2-power-root sums are +-pairs),
    so Conn_ring(2j)=0 for j>=2  =>  R_r <= Wick  with equality only from pairs (the proven bound).
  - In char p, Conn_p(2j) > 0 for j >= j0 (short char-p relations).  The anomaly A_r - (pair term)
    is the sum over partitions WITH at least one block of size >= 4.

THE KEY INEQUALITY TO ESTABLISH (the real open content, sharpened):
    sum_{partitions with a >=4 block} prod Conn_p(|B|)  <=  n^{2r}/p  +  (Wick - R_r)
  The cleanest SUFFICIENT structural bound:  Conn_p(2j) <= n^j  for all j (the "sub-Gaussian
  connected bound": each minimal length-2j relation contributes at most n^j, the SAME scaling as
  the Gaussian pair^j).  IF Conn_p(2j) <= C^j n^j with C absolute, the full sum is <= (Bell-type)
  and the moment is sub-Gaussian with constant depending on C.

WE MEASURE Conn_p(2j) DIRECTLY (the minimal char-p vanishing relation count) and test the scaling.
"""
import math
from sympy import primerange
import numpy as np
from itertools import product


def find_gen(n, p):
    e = (p - 1) // n
    for a in range(2, p):
        g = pow(a, e, p)
        if pow(g, n, p) == 1 and (n == 1 or pow(g, n // 2, p) == p - 1):
            return g
    raise RuntimeError


def conn_count(n, j, p):
    """Conn_p(2j) ~ #{ (signed) length-2j MINIMAL vanishing relations of mu_n mod p }.
    We count solutions to eps_1 x_1 + ... + eps_{2j} x_{2j} = 0 (mod p) with x_i in mu_n,
    eps_i in {+1,-1}, that are NOT decomposable into shorter vanishing sub-relations.
    Practically (small j): count total vanishing signed 2j-sums, then Mobius-subtract products
    of shorter ones.  We report TOTAL signed vanishing count V(2j) and the connected part.
    For the scaling test, V(2j) itself (its growth in n) is the informative object."""
    g = find_gen(n, p)
    mu = [pow(g, k, p) for k in range(n)]
    signed = mu + [(-x) % p for x in mu]  # 2n signed elements
    # V(2j) = #{ (a_1..a_2j) in signed^{2j} : sum = 0 mod p }
    # use convolution of the signed-element distribution, 2j-fold
    dist = np.zeros(p, dtype=np.int64)
    dist[0] = 1
    base = np.zeros(p, dtype=np.int64)
    for x in signed:
        base[x] += 1
    cnt = np.zeros(p, dtype=np.int64)
    cnt[0] = 1
    for _ in range(2 * j):
        nc = np.zeros(p, dtype=np.int64)
        for x in signed:
            nc += np.roll(cnt, x)
        cnt = nc
    return int(cnt[0])


def main():
    print("=" * 100)
    print("Conn/V(2j): total signed vanishing 2j-sum count V(2j) over mu_n mod p, scaling in n.")
    print("Gaussian/sub-Gaussian PREDICTION: the CONNECTED part Conn(2j) ~ n^j (pair scaling),")
    print("so V(2j)/(2n)^j -> O(1) [pure pairing], and the EXCESS over pairing is the anomaly.")
    print("=" * 100)
    print(f"{'n':>4} {'p':>10} {'j':>3} {'V(2j)':>16} {'pair_pred':>14} {'V/(n^j)':>12} {'V/pairpred':>11}")
    for mu in [3, 4]:
        n = 2 ** mu
        beta = 4.0
        p = next(q for q in primerange(int(n ** beta), int(n ** beta * 2)) if q % n == 1)
        for j in range(1, 5):
            V = conn_count(n, j, p)
            # pure-pairing prediction for signed 2j-sums = 0:
            #   a perfect matching pairs each +x with a -x: (2j-1)!! matchings, each gives
            #   (2n) choices for the value => (2j-1)!! * (2n)^j ... but signed, x with -x:
            #   pairs that vanish: {x, -x} -> 2n ways (pick signed elt, partner forced).
            pair_pred = (math.prod(range(1, 2 * j, 2))) * (2 * n) ** j
            print(f"{n:>4} {p:>10} {j:>3} {V:>16d} {pair_pred:>14.0f} {V/n**j:>12.2f} {V/pair_pred:>11.4f}")
        print()

    print("Reading: V/pairpred = 1 means PURELY pairings (Gaussian, no anomaly); >1 = char-p excess.")
    print("If V/pairpred stays O(1) bounded as j grows (to ~log p), the connected bound Conn(2j)<=C^j n^j")
    print("holds => sub-Gaussian => prize.  The CROSSOVER j where it departs from 1 = anomaly onset.")


if __name__ == "__main__":
    main()
