import math
# The geometry-of-numbers threshold for char-p moment faithfulness.
# W_r=0 (char-p moments = char-0) is GUARANTEED by the norm bound when 2r < min-house(P) ~ p^{2/n}.
# Show WHERE this protects (small n) vs where it goes vacuous (prize n~p^{1/4}).
print("min-house(P) ~ p^{2/n} vs the moment depth 2r~2 log m: when does the norm bound PROVE W_r=0?",flush=True)
print(f"{'p':>10} {'n':>10} {'n=p^?':>7} {'2r~2logm':>9} {'p^(2/n)':>12} {'protects?':>10}",flush=True)
cases=[
  (10007, 8), (10007, 16), (1048609, 32), (16777259, 64),
  (2**24, 2**6), (2**32, 2**8), (2**48, 2**12),
  (2**64, 2**16), (2**128, 2**32),  # prize point: p=2^128, n=p^{1/4}=2^32
]
for p,n in cases:
    m=p/n
    twor=2*math.log(m)            # depth 2r ~ 2 log m
    minhouse=p**(2.0/n)           # Minkowski min-house of P (residue degree 1, N(P)=p)
    protects = "YES" if minhouse>twor else "no (vacuous)"
    logpn = math.log(p)/math.log(n) if n>1 else 0
    print(f"{p:>10.3g} {n:>10} {logpn:>7.2f} {twor:>9.2f} {minhouse:>12.4g} {protects:>12}",flush=True)
print("\nNorm bound proves W_r=0 only while p^{2/n} > 2 log m, i.e. n < 2 log p / log(2 log m) ~ 2 log p/loglog p (SMALL).",flush=True)
print("Prize n~p^{1/4}: p^{2/n} -> 1 (vacuous) => norm bound gives NOTHING; W_r governed by actual #short-vectors",flush=True)
print("of P expressible as root-of-unity sums = BCHKS Conj 1.12 = the open core. Volume heuristic says MANY, the",flush=True)
print("roots-of-unity (Lam-Leung/Mann) structure suppresses to ~0 (measured sub-Wick) -- proving that is the prize.",flush=True)
print("DONE")
