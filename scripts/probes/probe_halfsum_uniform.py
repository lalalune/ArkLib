# probe_halfsum_uniform.py  (#407, Lane 3 COUNT lane — uniform-in-n Half-Sum Lemma)
#
# QUESTION: does the per-fixed-n Half-Sum Lemma (proven n=8,16,32,64 via candidate-prime
# enumeration) admit a UNIFORM-IN-n argument, or does it hit a wall at some n?
#
# SETUP. mu_n = <g> ⊂ F_p*, n=2^mu, p ≡ 1 mod n (the prize SPLIT regime). U ⊆ mu_n
# antipodal-free (U ∩ -U = ∅). The m=2 (second-moment) optimality residual reduces to:
#
#   HALF-SUM LEMMA.  If  s1 := Σ_{u∈U} u = 0  AND  s3 := Σ_{u∈U} u^3 = 0  in F_p,
#   then  e2 := -(1/2) Σ_{u∈U} u^2  lies in  Σ_k := { sums of k distinct mu_{n/2} elts },
#   where k = |U|/2 . (e2 ∈ Σ ⟹ this bad scalar is ALREADY counted by the char-0 ladder,
#   so #bad is NOT inflated by char-p coincidences ⟹ exact delta*.)
#
# Candidate UNIFORM MECHANISM (sharper, n-independent if true):
#   (M)  e2 = Σ over SOME k-subset W of the multiset {u^2 : u∈U}  (2k squares, in mu_{n/2}).
#
# This is q-independent COUNT combinatorics (off the BGK/analytic wall), decidable.
# We keep |U| SMALL (4,6) so we can sweep MANY n and find the FIRST n where uniformity breaks.

from itertools import combinations, product
import sympy as sp


def gen_split(n, p):
    e = (p - 1) // n
    for a in range(2, p):
        g = pow(a, e, p)
        if pow(g, n, p) == 1 and pow(g, n // 2, p) == p - 1:
            return g
    return None


def split_primes(n, count, start=None):
    out = []
    a = (start or (n + 1))
    while len(out) < count:
        if a % n == 1 and sp.isprime(a):
            out.append(a)
        a += 1
        if a > 5_000_000:
            break
    return out


def analyze_prime(n, p, sizes, cap=None):
    HALF = n // 2
    g = gen_split(n, p)
    if g is None:
        return None
    inv2 = pow(2, p - 2, p)
    mun = [pow(g, j, p) for j in range(n)]
    munhalf = [pow(g, 2 * j, p) for j in range(HALF)]
    res = {"nprim": 0, "mech_ok": 0, "mech_fail": 0, "sig_ok": 0, "sig_fail": 0,
           "fail": [], "sig_cache": {}}

    def sigma_k(k):
        if k not in res["sig_cache"]:
            if sp.binomial(HALF, k) > 3_000_000:
                res["sig_cache"][k] = None
            else:
                res["sig_cache"][k] = set(sum(W) % p for W in combinations(munhalf, k))
        return res["sig_cache"][k]

    for size in sizes:
        k = size // 2
        Sig = sigma_k(k)
        for Uidx in combinations(range(n), size):
            idxset = set(Uidx)
            if any(((j + HALF) % n) in idxset for j in Uidx):
                continue
            us = [mun[j] for j in Uidx]
            if sum(us) % p != 0 or sum(pow(u, 3, p) for u in us) % p != 0:
                continue
            res["nprim"] += 1
            e2 = (-inv2 * sum(pow(u, 2, p) for u in us)) % p
            sq = [(u * u) % p for u in us]
            mech = any(sum(W) % p == e2 for W in combinations(sq, k))
            if mech:
                res["mech_ok"] += 1
            else:
                res["mech_fail"] += 1
                if len(res["fail"]) < 8:
                    res["fail"].append(("MECH", p, size, tuple(Uidx)))
            if Sig is not None:
                if e2 in Sig:
                    res["sig_ok"] += 1
                else:
                    res["sig_fail"] += 1
                    if len(res["fail"]) < 8:
                        res["fail"].append(("SIG", p, size, tuple(Uidx)))
            if cap and res["nprim"] >= cap:
                return res
    return res


if __name__ == "__main__":
    print("=" * 74)
    print("PART A — uniform mechanism (M) + Σ-membership across many primes, small |U|")
    print("=" * 74)
    # size 4,6 only (building blocks); sweep many split primes per n
    for n in [8, 16, 32, 64, 128]:
        sizes = [4, 6] if n >= 8 else [4]
        if n >= 64:
            sizes = [4, 6]
        nprimes = {8: 12, 16: 10, 32: 8, 64: 6, 128: 4}[n]
        primes = split_primes(n, nprimes)
        tot_nprim = tot_mfail = tot_sfail = 0
        any_fail = []
        for p in primes:
            r = analyze_prime(n, p, sizes, cap=50000)
            if r is None:
                continue
            tot_nprim += r["nprim"]
            tot_mfail += r["mech_fail"]
            tot_sfail += r["sig_fail"]
            any_fail += r["fail"][:2]
        print(f"n={n}: primes={primes}")
        print(f"   #primitive U (s1=s3=0, antipodal-free, |U|∈{sizes}) over all primes = {tot_nprim}; "
              f"mechanism(M) fails {tot_mfail}; Σ-membership fails {tot_sfail}")
        if any_fail:
            print(f"   FAILURES: {any_fail[:5]}")
        else:
            print(f"   -> CLEAN: mechanism (M) AND Σ-membership hold for ALL tested configs.")
