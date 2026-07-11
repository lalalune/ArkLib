"""Confirm + mechanism: sum_{psi!=0} eta_psi^r = q*W_r - n^r is STRICTLY NEGATIVE for
ODD r on thin mu_n (#444 signed-period lane).

eta_psi = sum_{x in mu_n} psi(x) is the period sum at additive character psi.
For psi=0 (trivial), eta_0 = n. So sum_{ALL psi} eta^r = q*W_r (W_r=zeroSumCount), and
sum_{psi!=0} eta^r = q*W_r - n^r.

MECHANISM hypothesis for odd-r negativity:
  For psi != 0, eta_psi is a REAL number (mu_n negation-closed => the character sum is real:
  eta_psi = sum_x psi(x), and pairing x with -x gives psi(x)+psi(-x)=psi(x)+conj => real,
  actually 2*Re). The nontrivial period sums eta_psi (psi!=0) satisfy sum_{psi!=0} eta_psi
  = -n (since sum_ALL eta_psi = q*[1 in S? -> #{x in S: ... }]... ) and each |eta_psi| <= ...
  For ODD r the map t->t^r is odd, so negative eta_psi contribute negatively. The claim
  q*W_r - n^r < 0 says the bulk of nontrivial period sums are NEGATIVE-leaning at odd r.

This probe: (1) confirm the sign law q*W_r - n^r < 0 (r odd) / > 0 (r even) on MANY configs
incl large primes p>n^3 and Fermat 257; (2) tabulate the actual eta_psi values to expose the
mechanism (how many negative vs positive, and the dominant ones).
"""
import itertools
import cmath


def primes_one_mod_n(n, min_ratio=2, count=3, want_big=False):
    res = []
    k = 1
    while len(res) < count:
        p = k * n + 1
        k += 1
        if p <= 2:
            continue
        if not all(p % d for d in range(2, int(p ** 0.5) + 1)):
            continue
        if (p - 1) // n < min_ratio:
            continue
        if want_big and p <= n ** 3:
            continue
        res.append(p)
        if k > n ** 3 + 5000:
            break
    return res


def mun(n, p):
    for a in range(2, p):
        x = a % p
        kk = 1
        while x != 1 and kk <= p:
            x = (x * a) % p
            kk += 1
        if kk == n:
            S = []
            x = 1
            for _ in range(n):
                S.append(x)
                x = (x * a) % p
            return sorted(set(S))
    return None


def zerosumcount(S, p, r):
    cnt = 0
    for t in itertools.product(S, repeat=r):
        if sum(t) % p == 0:
            cnt += 1
    return cnt


def eta_values(S, p):
    """period sums eta_psi for all additive characters psi_b(x)=exp(2pi i b x/p)."""
    out = []
    for b in range(p):
        s = sum(cmath.exp(2j * cmath.pi * (b * x % p) / p) for x in S)
        out.append(s)
    return out


def main():
    print("PART 1: sign law (q*W_r - n^r) for r in 1..5, many configs")
    print(f"{'n':>3} {'p':>7} {'big?':>5} | " + " ".join(f"r{r}" for r in [1, 2, 3, 4, 5]))
    configs = []
    for n in [4, 8]:
        ps = primes_one_mod_n(n, min_ratio=2, count=3)
        ps_big = primes_one_mod_n(n, min_ratio=2, count=2, want_big=True)
        for p in ps + ps_big:
            configs.append((n, p, p > n ** 3))
    # add Fermat-ish: 257 for n=8 (257-1=256, n=8 -> ratio 32, proper)
    if all(c[1] != 257 for c in configs if c[0] == 8):
        configs.append((8, 257, 257 > 8 ** 3))
    for (n, p, big) in configs:
        S = mun(n, p)
        if S is None or len(S) != n:
            continue
        row = []
        for r in [1, 2, 3, 4, 5]:
            if n ** r > 6_000_000:
                row.append("  .")
                continue
            z = zerosumcount(S, p, r)
            v = p * z - n ** r
            row.append("neg" if v < 0 else ("ZER" if v == 0 else "pos"))
        print(f"{n:>3} {p:>7} {str(big):>5} | " + " ".join(f"{x:>3}" for x in row))

    print()
    print("PART 2: mechanism - eta_psi spectrum (n=8, p=17). Are nontrivial etas real & sign-mixed?")
    n, p = 8, 17
    S = mun(n, p)
    etas = eta_values(S, p)
    nontriv = etas[1:]
    reals = [e.real for e in nontriv]
    maxim = max(abs(e.imag) for e in nontriv)
    print(f"  max |Im(eta_psi)| over psi!=0 = {maxim:.2e} (should be ~0: eta real on neg-closed S)")
    print(f"  nontrivial eta real parts sorted: {[round(r,3) for r in sorted(reals)]}")
    npos = sum(1 for r in reals if r > 1e-9)
    nneg = sum(1 for r in reals if r < -1e-9)
    nzer = sum(1 for r in reals if abs(r) <= 1e-9)
    print(f"  #pos={npos} #neg={nneg} #zero={nzer}; sum eta_psi(psi!=0) = {sum(reals):.4f} (expect -n = -{n})")
    for r in [3, 5]:
        ssum = sum(rr ** r for rr in reals)
        print(f"  sum_(psi!=0) eta^{r} (direct, real) = {ssum:.3f}  -> sign {'neg' if ssum<0 else 'pos'}")


if __name__ == "__main__":
    main()
