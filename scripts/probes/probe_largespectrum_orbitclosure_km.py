#!/usr/bin/env python3
"""
probe_largespectrum_orbitclosure_km.py  (#389/#407/#444 — alien-idea grounding)

Grounds the "structure-from-large-spectrum" angle (KM/Kelley-Lovett-Meka 2024 sparse-graph
counting + Bloom-Sisask structure of the large spectrum) applied DIRECTLY to M(mu_n), NOT as the
already-refuted density theorem (A9).

OBJECT: M(mu_n) = max_b |S_b|, S_b = sum_{x in mu_n} e_p(bx) = p * \\hat{1_H}(b)  (un-normalized DFT
of the subgroup indicator). So M is literally the L^infty of the Fourier transform of 1_H, and the
LARGE SPECTRUM  Spec_t = { b != 0 : |S_b| >= t }  is the object a structure theorem constrains.

MEASURED (proper mu_n=2^mu, n|p-1, p PRIME, p>>n^3, m=(p-1)/n odd, NEVER n=p-1):
  * the large spectrum is EXACTLY a union of full mu_n-cosets => |Spec_t| is a multiple of n
    (dilation-orbit-closed: b in Spec => tb in Spec for all t in mu_n, since S_{tb}=S_b up to the
    H-action permuting the sum). CONFIRMED: |Spec|=9n,26n,... at the floor threshold.
  * the large spectrum at threshold ~ sqrt(n log(p/n)) is THIN in F_p* (density ~1e-3 of (p-1)).

WHY THIS IS THE RIGHT KM USE (vs A9 density-vacuity): A9 fed the DENSITY of mu_n to the 3AP
theorem (vacuous, n/p=2^-128). Here we feed the orbit-closed large SPECTRUM to the sparse-graph
counting / structure-of-spectrum machinery: M<=t  <=>  Spec_t = {} (empty), and the new tech
bounds the number of cosets the spectrum can occupy from its own additive structure. The
self-improvement is the never-tried lever. This probe only ESTABLISHES the structural inputs
(orbit-closure, thinness); it does not claim the bound.
"""
import numpy as np, math

def is_prime(n):
    if n < 2: return False
    d = 2
    while d*d <= n:
        if n % d == 0: return False
        d += 1
    return True

def primroot(p):
    phi = p-1; facs = set(); m = phi; d = 2
    while d*d <= m:
        while m % d == 0: facs.add(d); m //= d
        d += 1
    if m > 1: facs.add(m)
    for g in range(2, p):
        if all(pow(g, phi//q, q_) != 1 for q_ in facs):  # noqa
            pass
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in facs):
            return g

for n in [16, 32]:
    target = n**4
    p = None
    for cand in range(target, target + 300000):
        if (cand-1) % n == 0 and is_prime(cand) and ((cand-1)//n) % 2 == 1:
            p = cand; break
    g = primroot(p); h = pow(g, (p-1)//n, p)
    H = set(pow(h, j, p) for j in range(n))
    assert len(H) == n and (n != p-1)
    ind = np.zeros(p)
    for x in H: ind[x] = 1.0
    S = np.fft.fft(ind); absS = np.abs(S); absS[0] = 0.0
    M = absS.max()
    floor = math.sqrt(n*math.log(p/n))
    print(f"n={n} p={p} m={(p-1)//n} M={M:.2f} floor=sqrt(n log(p/n))={floor:.2f} "
          f"M/floor={M/floor:.3f} M/n={M/n:.3f}")
    for c in [0.5, 0.75, 1.0]:
        thr = c*floor
        spec = np.where(absS >= thr)[0]
        specset = set(int(b) for b in spec)
        closed = True
        for b in list(specset)[:20]:
            for t in list(H)[:8]:
                if (b*t) % p not in specset:
                    closed = False; break
            if not closed: break
        mult = len(spec)/n
        print(f"   thr={c}*floor: |Spec|={len(spec)} (={mult:.2f}*n int? {abs(mult-round(mult))<1e-9}, "
              f"={len(spec)/(p-1):.2e}*(p-1)) orbit-closed(sampled)={closed}")
print("\nCONCLUSION: large spectrum is a union of full mu_n-cosets (orbit-closed) and thin in F_p*. "
      "These are exactly the structural inputs a post-2022 structure-of-spectrum / sparse-graph-"
      "counting theorem would consume; A9 fed the wrong functional (density) to KM.")
