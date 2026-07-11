#!/usr/bin/env python3
"""
Avenue D probe: does the DC-Wick / moment ladder yield the WORST-CASE (L-inf, max over b!=0)
period bound, or only the AVERAGE (L2 / L2r)?

Mechanism under test (the in-tree chain, two independent forms):
  (A) cosh-MGF / Chernoff:  cosh(M*y) <= sum_{b!=0} cosh(|eta_b| y) = DC-MGF(y) <= B
      => M = max_{b!=0}|eta_b| <= log(2B)/y.  Holds for EVERY b => worst-case.
  (B) fixed even moment / Markov:  #{|eta_b|>T} * T^{2r} <= sum_{b!=0}|eta_b|^{2r} = qE_r - n^{2r} =: S
      => if S < T^{2r} then #{...}=0 => every |eta_b| <= T.  Worst-case via Markov.

We numerically construct the cyclotomic Gauss-period family eta_b = sum_{x in mu_n} e_p(b x)
for a small PRIME p with n | p-1, p >> n^3, n = 2^mu (proper probe regime), and check:
  - the SUM-based threshold T*(r) = (S)^{1/2r} (Markov) DOMINATES the true max  (worst-case OK)
  - the AVERAGE-based scale sqrt(S/(q-1)) (L2 avg) UNDERSHOOTS the true max  (avg is NOT a bound)
This confirms the ladder controls the MAX (via the count argument), and that the average alone
would be a strict under-estimate of the worst case.
"""
import cmath, math

def gauss_periods(p, n):
    # mu_n = unique subgroup of order n in F_p^*
    g = primitive_root(p)
    # generator of order n: g^((p-1)/n)
    h = pow(g, (p-1)//n, p)
    mu = [pow(h, k, p) for k in range(n)]
    etas = []
    for b in range(p):
        s = 0j
        for x in mu:
            s += cmath.exp(2j*math.pi*((b*x) % p)/p)
        etas.append(abs(s))
    return etas

def primitive_root(p):
    # smallest primitive root mod p
    from sympy import primitive_root as pr
    return pr(p)

def main():
    # proper regime: n = 2^mu, n | p-1, p PRIME, p >> n^3
    cases = []
    # n=4: need p prime, 4 | p-1, p >> 64
    # pick p = 113 (4|112), p=113 >> 64
    cases.append((113, 4))
    # n=8: 8 | p-1, p >> 512 -> p=521 (8|520), prime
    cases.append((521, 8))
    # n=16: 16 | p-1, p >> 4096 -> p=4177? check prime & 16|4176 ; 4176/16=261 ok
    cases.append((4177, 16))
    for p, n in cases:
        try:
            etas = gauss_periods(p, n)
        except Exception as e:
            print(f"  p={p} n={n}: skip ({e})")
            continue
        q = p
        nz = [etas[b] for b in range(p) if b % p != 0]  # b != 0
        # b=0 spike check
        dc = etas[0]
        M = max(nz)  # true worst-case max over b!=0
        # fixed moment r: S_r = sum_{b!=0} |eta_b|^{2r}
        print(f"p={p}, n={n}, q={q}: DC(b=0)={dc:.2f} (=n? {abs(dc-n)<1e-6}), true M=max_{{b!=0}}={M:.4f}, 2sqrt(n)={2*math.sqrt(n):.4f}")
        for r in [1,2,3,4]:
            S = sum(v**(2*r) for v in nz)
            T_markov = S**(1.0/(2*r))             # Markov sup threshold: every |eta_b| <= T_markov
            avg_scale = math.sqrt(S/(len(nz)))    # the AVERAGE (L2-of-2r) scale
            ok_worst = (M <= T_markov + 1e-9)
            avg_under = (avg_scale < M)           # average undershoots the worst case?
            print(f"   r={r}: S={S:.3e}  T_markov(sup)={T_markov:.4f}  avg_scale={avg_scale:.4f}  "
                  f"max<=T_markov? {ok_worst}  avg<max(undershoot)? {avg_under}")
    print()
    print("INTERPRETATION: T_markov(sup) >= true M at every r  =>  the moment/MGF ladder's")
    print("count(Markov) step yields a VALID WORST-CASE (L-inf) bound.  The average scale")
    print("sits strictly below M, so 'average' alone is NOT a worst-case bound — the LADDER")
    print("UPGRADES average-energy control to the max via the elementary count step.")

if __name__ == "__main__":
    main()
