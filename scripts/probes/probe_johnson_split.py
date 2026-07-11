#!/usr/bin/env python3
"""#389 route 1 probe: THE JOHNSON SPLIT of the sub-Johnson supply wall.

For censused small RS instances RS[F_p, dom, k], measure at every agreement
level a:
  * the actual max list size  L(a) = max_w #{codewords c : agree(c,w) >= a}
    (max over sampled words w: random words + engine-style lines Q + gamma*x^k
    with deg Q in (k, 2k+m+1]),
  * the Johnson bound  n^2 // (a^2 - n(k-1))   (valid iff a^2 > n(k-1)),
  * the packing bound  n^k // (a+1-k)^k        (PopularCodewords, valid a>=k),
and for each band m, the actual max explainable-(k+m+1)-core count of
agreement-capped words versus the two proven fiber bounds:
  * Johnson fiber  J * C(2k+m+1, k+m+1)  (JohnsonSplitSupply.lean, above line),
  * pair-count fiber  C(n,k)             (DeepBandFailureUnconditional.lean).

The split point: a* = floor(sqrt(n(k-1)))+1, i.e. m* = a* - (k+1).
EVIDENCE: sampled max underestimates the true max; the Lean theorems are the
proof, this locates the empirical split and validates nonvacuity.
"""
import itertools, math, random
import numpy as np

random.seed(20260612)


def codeword_matrix(p, D, k):
    """All q^k codewords as an (q^k, n) numpy array."""
    n = len(D)
    V = np.array([[pow(x, i, p) for i in range(k)] for x in D], dtype=np.int64)
    coeffs = np.array(list(itertools.product(range(p), repeat=k)), dtype=np.int64)
    return (coeffs @ V.T) % p


def eval_poly(c, x, p):
    return sum(ci * pow(x, i, p) for i, ci in enumerate(c)) % p


def johnson_bound(n, k, a):
    gap = a * a - n * (k - 1)
    return (n * n) // gap if gap > 0 else None


def packing_bound(n, k, a):
    if a + 1 - k <= 0:
        return None
    return (n ** k) // ((a + 1 - k) ** k)


def run_instance(p, D, k, n_rand_words=120, n_lines_per_m=40, max_m=None):
    n = len(D)
    n_codewords = p ** k
    CW = codeword_matrix(p, D, k)
    a_star = math.isqrt(n * (k - 1)) + 1  # least a with a^2 > n(k-1)
    m_star = max(a_star - (k + 1), 0)
    print(f"\n=== RS[F_{p}, n={n}, k={k}]  (q^k = {n_codewords} codewords) ===")
    print(f"Johnson agreement line: a* = floor(sqrt({n}*{k - 1}))+1 = {a_star}"
          f"  =>  band split m* = a* - (k+1) = {m_star}")

    if max_m is None:
        max_m = n - k - 1
    bands = [m for m in range(0, max_m + 1) if k + m + 1 <= n]

    # ---- word sample: random words + engine lines Q + gamma x^k ----
    words = []
    for _ in range(n_rand_words):
        words.append(tuple(random.randrange(p) for _ in range(n)))
    for m in bands:
        degcap = 2 * k + m + 1
        for _ in range(n_lines_per_m):
            # Q with a guaranteed nonzero coefficient above k (off-code at every shear)
            deg = random.randrange(k + 1, degcap + 1)
            Q = [random.randrange(p) for _ in range(deg + 1)]
            Q[deg] = random.randrange(1, p)
            gamma = random.randrange(p)
            w = tuple((eval_poly(Q, x, p) + gamma * pow(x, k, p)) % p for x in D)
            words.append(w)
    W = np.array(words, dtype=np.int64)

    # agreement of every word with every codeword: (n_words, q^k)
    # chunk over words to keep memory modest
    max_list = np.zeros(n + 1, dtype=np.int64)
    agree_per_word = []
    for i in range(0, len(W), 32):
        chunk = W[i:i + 32]
        ag = (CW[None, :, :] == chunk[:, None, :]).sum(axis=2)  # (chunk, q^k)
        agree_per_word.append(ag)
        for a in range(0, n + 1):
            counts = (ag >= a).sum(axis=1)
            max_list[a] = max(max_list[a], counts.max())
    agree_per_word = np.concatenate(agree_per_word, axis=0)

    print(f"{'a':>3} {'maxList':>8} {'johnson':>8} {'packing':>10} {'q^k':>8}  side")
    for a in range(max(k, 1), n + 1):
        jb = johnson_bound(n, k, a)
        pb = packing_bound(n, k, a)
        side = "ABOVE line" if a >= a_star else "below line"
        ok = ""
        if jb is not None and max_list[a] > jb:
            ok = "  *** JOHNSON VIOLATED ***"
        print(f"{a:>3} {max_list[a]:>8} {str(jb):>8} {str(pb):>10} {n_codewords:>8}  {side}{ok}")

    # ---- explainable-core counts per band, agreement-capped words only ----
    print(f"\n band   cores(max)  J*C(2k+m+1,k+m+1)   C(n,k)   side")
    for m in bands:
        t = k + m + 1
        cap = 2 * k + m + 1
        jb = johnson_bound(n, k, t)
        jfiber = jb * math.comb(cap, t) if jb is not None else None
        pfiber = math.comb(n, k)
        best_cores = 0
        if math.comb(n, t) <= 20000:
            for wi in range(len(W)):
                ag = agree_per_word[wi]
                if ag.max() > cap:
                    continue  # not agreement-capped; outside the residual's scope
                idxs = np.nonzero(ag >= t)[0]
                cores = set()
                for ci in idxs:
                    Sw = tuple(np.nonzero(CW[ci] == W[wi])[0])
                    for T in itertools.combinations(Sw, t):
                        cores.add(T)
                best_cores = max(best_cores, len(cores))
        side = "ABOVE" if m >= m_star else "below"
        viol = ""
        if jfiber is not None and best_cores > jfiber:
            viol = "  *** FIBER VIOLATED ***"
        print(f"  m={m:<3} {best_cores:>9} {str(jfiber):>18} {pfiber:>8}   {side}{viol}")
    return a_star, m_star


if __name__ == "__main__":
    # smooth-ish small instances (domain = full multiplicative line or subgroup-like)
    run_instance(17, list(range(1, 9)), 2)            # n=8,  k=2: line a*=3, m*=0
    run_instance(13, list(range(13)), 3, max_m=6)     # n=13, k=3: line a*=6, m*=2
    run_instance(31, list(range(1, 17)), 3, max_m=8)  # n=16, k=3: line a*=6, m*=2
    print("\nSplit-point law: a* = floor(sqrt(n(k-1)))+1, m* = a*-(k+1); "
          "bands m >= m* are closed by JohnsonSplitSupply.lean "
          "(deep_band_failure_above_johnson_of_sqrt); bands m < m* are the "
          "named SubJohnsonSupplyResidual.")
