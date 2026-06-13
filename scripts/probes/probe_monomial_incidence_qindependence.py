#!/usr/bin/env python3
"""Issue #389 — q-independence and coset structure of the worst-case monomial far-line
incidence, and localization of the open core.

Setup (prize-shape smooth RS): domain mu_n (n=2^mu), code RS[k], rho=k/n. The far-line
incidence is Z/n-dilation invariant, so extremal directions are monomials X^a; for
u0=X^b, u1=X^a the bad set B(delta)={gamma != 0 : X^b+gamma X^a is delta-close to RS[k]}.
Exact list-decode by k-subset interpolation (max agreement >= w := round((1-delta) n)).

KEY MEASURED FACTS (n=16, k=4, rho=1/4; q in {97,193,257,353}, all = 1 mod 16):
  * w=5 (delta=0.688): incidence = q-1 EXACTLY (full explosion, proportional to q).
  * w=6 (delta=0.625): incidence = 32,16,16,16 -> BOUNDED, q-INDEPENDENT, -> n.
  * w>=7 (delta<=0.562): incidence = 0.
So below the explosion the worst incidence is q-independent and bounded (-> ~n at the edge,
matching the prize threshold q*eps* = n for q = n*2^128), then jumps to the full q-1 explosion.
The bad set is a union of mu_{n'} cosets (n' = n/gcd(a,n)); for dir (5,6), gcd=1 so n'=16 and
#bad=16 means EXACTLY ONE coset is bad.

LOCALIZATION OF THE OPEN CORE: the provable per-witness bound is C(n,w)=C(16,6)=8008 (wall W1);
the true worst incidence is 16 = n. Closing C(n,w) -> O(n) (= bounding #bad cosets) is the
line-ball-incidence open core, here shown to be q-independent (so a purely combinatorial count
over mu_n, not a character-sum-over-F_q problem). This is honest empirical localization, NOT a
proof of the prize.
"""
import itertools

def inv_table(q):
    return [0] + [pow(a, q - 2, q) for a in range(1, q)]

def gen_mu_faithful(q, n):
    for x in range(2, q):
        if pow(x, n, q) == 1 and pow(x, n // 2, q) != 1:  # n = 2^mu => order exactly n
            dom = [pow(x, i, q) for i in range(n)]
            assert len(set(dom)) == n
            return dom
    raise RuntimeError("no faithful mu_n")

def close_ge(vals, dom, k, q, n, w, inv):
    """Does some deg<k polynomial agree with `vals` on >= w of the n points?"""
    for sub in itertools.combinations(range(n), k):
        xs = [dom[i] for i in sub]; ys = [vals[i] for i in sub]
        dent = []
        for t in range(k):
            den = 1
            for s in range(k):
                if s != t:
                    den = den * ((xs[t] - xs[s]) % q) % q
            dent.append(inv[den % q])
        agree = 0
        for j in range(n):
            xj = dom[j]; val = 0
            for t in range(k):
                num = ys[t] * dent[t] % q
                for s in range(k):
                    if s != t:
                        num = num * ((xj - xs[s]) % q) % q
                val = (val + num) % q
            if val == vals[j]:
                agree += 1
            elif agree + (n - 1 - j) < w:
                break
        if agree >= w:
            return True
    return False

def incidence(n, k, q, a, b, w):
    dom = gen_mu_faithful(q, n); inv = inv_table(q)
    return sum(1 for g in range(1, q)
               if close_ge([(pow(dom[i], b, q) + g * pow(dom[i], a, q)) % q for i in range(n)],
                           dom, k, q, n, w, inv))

if __name__ == "__main__":
    n, k = 16, 4
    print(f"n={n} k={k} rho={k/n}; window=(1-sqrt(rho),1-rho)=({1-(k/n)**.5:.3f},{1-k/n:.3f})")
    print("dir   w  delta  | incidence at q = 97, 193, 257, 353")
    for (a, b) in [(5, 6), (6, 7)]:
        for w in [5, 6, 7]:
            row = [incidence(n, k, q, a, b, w) for q in (97, 193, 257, 353)]
            print(f"({a},{b})  {w}  {1-w/n:.3f}  | {row}")
