#!/usr/bin/env python3
"""
δ* value-concentration probe (#389, 2026-06-13).

Tests the face-(iv) lever: do STRUCTURED far directions (power maps x^d, d|n, and the
inverse map) on a smooth RS code RS[F_p, H, k] (H = subgroup of 2-power order n) push the
max agreement of u0 + γ·u1 with a degree-<k codeword STRICTLY BETWEEN Johnson and capacity?

For each candidate direction u1 (entrywise x -> R(x) for a structured R) and a generic u0,
we sweep ALL γ ∈ F_p, and for each γ compute the exact distance of w = u0 + γ·u1 to the RS
code = n - maxagree, where maxagree = max over degree-<k polys f of #{x∈H : f(x)=w(x)}.
maxagree is computed exactly by brute force over k-subsets (Lagrange interpolation + count).

Outputs, per direction:
  conc = max value-multiplicity of R on H (pure concentration, no code constraint)
  best_agree = max over γ of agreement     -> δ*_emp = 1 - best_agree/n
compared to Johnson (1-sqrt(ρ)) and capacity (1-ρ).
"""
import itertools, math, json, sys

def is_prime(m):
    if m < 2: return False
    for i in range(2, int(m**0.5)+1):
        if m % i == 0: return False
    return True

def find_prime_with_subgroup(n, lo=2):
    # smallest prime p > lo with n | p-1
    p = max(lo, n+1)
    while True:
        if (p-1) % n == 0 and is_prime(p):
            return p
        p += 1

def subgroup(p, n):
    # generator of the order-n subgroup of F_p^*
    # find primitive root g0, then g0^((p-1)/n)
    for g0 in range(2, p):
        seen = set(); x = 1; ok = True
        # check order = p-1 cheaply by powers dividing
        # just trust small p: compute order
        order = 0; x = g0
        vals = set()
        xx = 1
        for _ in range(p-1):
            xx = (xx*g0) % p
            vals.add(xx)
        if len(vals) == p-1:
            g = pow(g0, (p-1)//n, p)
            H = [pow(g, i, p) for i in range(n)]
            return g, H
    raise RuntimeError("no primitive root?")

def interp_count(p, H, w, k, xs_idx):
    # interpolate degree-<k poly through the k points (H[i], w[i]) for i in xs_idx,
    # then count agreement over all of H. Returns agreement count, or None if singular.
    pts = [(H[i], w[i]) for i in xs_idx]
    # Lagrange evaluation of the interpolant at each H[j]
    agree = 0
    # Precompute coefficients via Lagrange: f(X) = sum_i y_i * prod_{l≠i}(X-x_l)/(x_i-x_l)
    xs = [pt[0] for pt in pts]; ys = [pt[1] for pt in pts]
    # check distinct
    if len(set(xs)) != len(xs): return None
    for j in range(len(H)):
        X = H[j]; fx = 0
        for i in range(k):
            num = ys[i]; den = 1
            for l in range(k):
                if l == i: continue
                num = (num * ((X - xs[l]) % p)) % p
                den = (den * ((xs[i] - xs[l]) % p)) % p
            fx = (fx + num * pow(den, p-2, p)) % p
        if fx == w[j]:
            agree += 1
    return agree

def max_agree(p, H, w, k):
    n = len(H)
    best = 0
    # brute over k-subsets; agreement >= k always for the chosen subset
    for sub in itertools.combinations(range(n), k):
        a = interp_count(p, H, w, k, sub)
        if a is not None and a > best:
            best = a
    return best

def concentration(p, H, Rvals):
    from collections import Counter
    c = Counter(Rvals)
    return max(c.values())

def run(n, k, max_p=4000):
    p = find_prime_with_subgroup(n, lo=2*n)
    if p > max_p:
        return None
    g, H = subgroup(p, n)
    rho = k / n
    johnson = 1 - math.sqrt(rho)
    capacity = 1 - rho
    # generic u0: a "random-ish" deterministic word (value x^2 say, far from low deg if k small)
    u0 = [pow(x, k+1, p) for x in H]   # degree k+1 > k-1 -> not a codeword
    results = {}
    # structured directions R = x^d for d | n (incl inverse map d=n-1)
    divisors = [d for d in range(1, n) if n % d == 0]
    dirs = [("x^%d"%d, [pow(x, d, p) for x in H]) for d in divisors]
    dirs.append(("inv(x^%d)"%(n-1), [pow(x, n-1, p) for x in H]))
    for name, u1 in dirs:
        conc = concentration(p, H, u1)
        best = 0; best_g = None
        for gamma in range(p):
            w = [(u0[i] + gamma*u1[i]) % p for i in range(n)]
            a = max_agree(p, H, w, k)
            if a > best:
                best = a; best_g = gamma
        dstar = 1 - best/n
        results[name] = dict(conc=conc, best_agree=best, dstar_emp=round(dstar,4),
                             best_gamma=best_g)
    return dict(n=n, k=k, p=p, rho=round(rho,4),
                johnson=round(johnson,4), capacity=round(capacity,4),
                directions=results)

if __name__ == "__main__":
    out = []
    for (n,k) in [(4,1),(4,2),(8,2),(8,4),(8,6),(16,4),(16,8)]:
        r = run(n,k)
        if r:
            out.append(r)
            d = r["directions"]
            print(f"n={n} k={k} p={r['p']} ρ={r['rho']} "
                  f"Johnson={r['johnson']} cap={r['capacity']}")
            for name, dd in d.items():
                tag = ""
                ds = dd["dstar_emp"]
                if ds < r["johnson"] - 1e-9: tag = "  <Johnson(bad-tight)"
                elif ds > r["capacity"] + 1e-9: tag = "  >capacity(?)"
                elif abs(ds - r["capacity"]) < 1e-9: tag = "  =capacity"
                elif abs(ds - r["johnson"]) < 1e-9: tag = "  =Johnson"
                else: tag = "  BETWEEN J & cap <<<"
                print(f"    {name:12s} conc={dd['conc']:3d} maxagree={dd['best_agree']:3d} "
                      f"δ*_emp={ds}{tag}")
    print("\nJSON:")
    print(json.dumps(out))
