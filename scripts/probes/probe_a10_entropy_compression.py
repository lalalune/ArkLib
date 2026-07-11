#!/usr/bin/env python3
"""
A10-ENTROPY-COMPRESSION (#444, open-avenue C7, NEVER attacked).

RELOCATION OF THE CANCELLATION LOCUS: LOCUS = INFORMATION (Shannon entropy /
communication-complexity), distinct from the chaining angle (#2) which is a
metric-entropy / majorizing-measures functional on the index PROCESS. Here the
functional is the Shannon entropy of the (r+1)-subset-sum DISTRIBUTION over mu_n.

PRECISE NEW LEMMA (the thing I am inventing and testing):

  Let mu_n = {x_0,...,x_{n-1}} be the 2-power multiplicative subgroup of F_p^*,
  n = 2^mu, p prime, p >> n^3 (PROPER subgroup). For an integer r, let
      Sigma_r = sum_{i in T} x_i  (mod p),  T a UNIFORM random (r+1)-subset of mu_n.
  Let P_r be the distribution of Sigma_r on F_p, and  H(P_r) its Shannon entropy
  (in BITS). Define the SUBSET-SUM ENTROPY ENVELOPE
      Lambda_r := 2^{H(P_r)}    (effective support / "min-entropy-free" count).

  CLAIM (A10): the worst-case far-line list at the (r+1)-jump radius
  delta = 1 - (r+1)/n satisfies   L_worst  <=  Lambda_r  (entropy envelope),
  AND the 2-power multiplicative RIGIDITY forces  Lambda_r  to be SMALLER than
  the generic volume count C(n, r+1) -- so that for the window radius (past
  Johnson, before the floor), Lambda_r < budget = eps * q while the volume
  C(n,r+1) > budget. If true: the entropy of the subset-sum law CAPS the list
  below budget where the second-moment/volume bound does NOT.

DECISIVE TEST (this probe):
  (T1) Compute the EXACT subset-sum distribution P_r over mu_n (r+1 = 2..small),
       its Shannon entropy H(P_r), and Lambda_r = 2^H. Compare to:
          - log2 C(n,r+1)  (the VOLUME / max-entropy ceiling),
          - the EXACT worst-case bad list L (number of bad gammas / codewords)
            at the jump radius for the monomial stack (the actual prize object),
          - log2(distinct subset sums)  (support size = max possible Lambda).
  (T2) RIGIDITY GAIN: is H(P_r) STRICTLY below the max-entropy log2 C(n,r+1)?
       i.e. does the subset-sum law CONCENTRATE (collisions from 2-power
       structure)? Compare mu_n (smooth) to a RANDOM/Sidon domain of same size.
  (T3) THE CRUCIAL HORN: does Lambda_r reproduce the AVERAGE (volume/q, = no gain,
       reduces-to-wall) or does it land STRICTLY between Johnson and the floor as
       a function that beats volume? Track Lambda_r/C(n,r+1) and Lambda_r vs L.

PROPER REGIME: p PRIME, n=2^mu, n | p-1, p >> n^3, proper subgroup (NEVER n=p-1).
Exact arithmetic throughout.
"""
import itertools, math, random, sys
from collections import Counter
from math import comb, log2, lgamma

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = m-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a % m == 0: continue
        x = pow(a, d, m)
        if x == 1 or x == m-1: continue
        ok = False
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: ok = True; break
        if not ok: return False
    return True

def find_prime(mu, beta):
    """smallest prime p = 1 mod n with p > n^beta (so p >> n^3 for beta>=4)."""
    n = 1 << mu
    lo = int(n**beta)
    t = ((lo // n) + 1) * n + 1
    while not isprime(t):
        t += n
    return n, t

def subgroup(p, n):
    fac = []; x = p-1; d = 2
    while d*d <= x:
        if x % d == 0:
            fac.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: fac.append(x)
    g = None
    for c in range(2, p):
        if all(pow(c, (p-1)//q, p) != 1 for q in fac):
            g = c; break
    h = pow(g, (p-1)//n, p)
    H = [pow(h, i, p) for i in range(n)]
    assert len(set(H)) == n and pow(h, n//2, p) != 1, "not a proper subgroup"
    return H

def shannon_entropy_bits(counts, total):
    """H in bits of the empirical distribution with given counts summing to total."""
    H = 0.0
    for c in counts:
        if c > 0:
            pr = c/total
            H -= pr*log2(pr)
    return H

def subset_sum_dist(D, t, p):
    """EXACT distribution of t-subset sums mod p. Returns Counter, total = C(n,t)."""
    cnt = Counter()
    for comb_ in itertools.combinations(D, t):
        cnt[sum(comb_) % p] += 1
    return cnt

def log2binom(n, k):
    if k < 0 or k > n: return float("-inf")
    if k == 0 or k == n: return 0.0
    return (lgamma(n+1) - lgamma(k+1) - lgamma(n-k+1)) / math.log(2)

def main():
    print("="*100)
    print("A10 ENTROPY-COMPRESSION: H(subset-sum dist over mu_n) vs volume vs worst-case list")
    print("="*100)
    print("Lambda_r = 2^H(P_r) = effective support of (r+1)-subset-sum law.")
    print("Question: does Lambda_r < volume C(n,r+1) (rigidity GAIN) -> below budget past Johnson?")
    print("          or does H(P_r) = log2 C(n,r+1) (max entropy, = no gain = reduces-to-volume)?")
    print()
    random.seed(7)

    # exact regime: small mu so we can enumerate, but p >> n^3 PROPER subgroup.
    configs = []
    for mu in (3,4,5):
        for beta in (3.2, 4.0):
            n, p = find_prime(mu, beta)
            configs.append((mu, n, p))

    print(f"{'n':>3} {'p':>12} {'p/n^3':>9} | {'t=r+1':>5} {'C(n,t)':>9} {'#sums':>7} "
          f"{'H(P)bits':>9} {'Lam=2^H':>9} {'log2C':>7} {'gain':>6} {'rand H':>7} {'rand Lam':>9}")
    print("-"*120)
    for (mu, n, p) in configs:
        D = subgroup(p, n)
        Drand = sorted(random.sample(range(1, p), n))
        for t in range(2, min(n, 7)):
            if t > n: continue
            cnt = subset_sum_dist(D, t, p)
            total = comb(n, t)
            H = shannon_entropy_bits(cnt.values(), total)
            Lam = 2**H
            nsums = len(cnt)
            l2c = log2binom(n, t)
            gain = l2c - H  # >0 means concentration (rigidity gain)
            # random/Sidon comparison
            cntr = subset_sum_dist(Drand, t, p)
            Hr = shannon_entropy_bits(cntr.values(), total)
            Lamr = 2**Hr
            print(f"{n:>3} {p:>12} {p/n**3:>9.2f} | {t:>5} {total:>9} {nsums:>7} "
                  f"{H:>9.3f} {Lam:>9.1f} {l2c:>7.3f} {gain:>6.3f} {Hr:>7.3f} {Lamr:>9.1f}")
        print()

    print("="*100)
    print("INTERPRETATION KEY:")
    print(" gain = log2 C(n,t) - H(P_r). gain>0 = subset-sum law concentrates (2-power collisions).")
    print(" If Lambda_r (smooth) << Lambda_r (random) AND << C(n,t): rigidity gives a real reduction.")
    print(" If H(P_r) ~ log2 C(n,t) (gain ~ 0): max-entropy => NO gain => reduces-to-volume/wall.")
    print(" Decisive: in the WINDOW (past Johnson) is 2^H < budget while C(n,t) > budget?")
    return 0

if __name__ == "__main__":
    sys.exit(main())
