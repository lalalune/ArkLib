#!/usr/bin/env python3
"""
probe_i031_logtarget.py  (#444 - I031 log(p/n) target wiring)

ONE sweep, decisive. The I031 union bound is
    M(mu_n) = max_{b!=0} ||eta_b|| <= sqrt(2 * C0 * n * log m),  m = [F*:mu_n] = (q-1)/n
conditional on the per-period sub-Gaussian tail (the named-open BGK/Lamzouri wall).

This probe does NOT re-test the open tail (that is the wall). It validates the PURE-ALGEBRA
wiring that the new brick formalizes:
  (W1) m = (q-1)/n is >= 1 in the prize regime (proper subgroup) -> bridge hypothesis 1<=m holds.
  (W2) log((q-1)/n) <= log(q/n): the I031 collapse lands at the PRIZE target form log(q/n),
       not the trivial log(q). And the GAP log(q) - log(q/n) = log(n) is exactly the
       sqrt(n)-scale entropy the dilation-quotient collapse removes (the value of I031).
  (W3) the target sqrt(2 C0 n log(q/n)) is NON-VACUOUS (a finite positive real, < the trivial
       sqrt(2 C0 n log q)) at PROPER thin subgroups p >> n^3, NEVER n=q-1.
"""
import math

def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i*i <= x:
        if x % i == 0: return False
        i += 2
    return True

# prize-regime instances: n = 2^a (thin 2-power), q = p prime == 1 mod n, p >> n^3 (PROPER subgroup)
cases = []
for a in range(2, 8):           # n = 4 .. 128
    n = 2**a
    target = n**4               # q ~ n^4 (beta=4 prize regime)
    # find several primes p == 1 mod n near n^3..n^5, all PROPER (p-1 > n, never p-1=n)
    found = 0
    p = target | 1
    while found < 3 and p < target*64:
        if p % n == 1 and is_prime(p) and (p-1) > n:   # PROPER: (p-1)/n >= 2
            cases.append((n, p))
            found += 1
        p += 2

C0 = 1.25  # the empirically-stable wall constant (census 1.6); only used for non-vacuity scale
fails = 0
checked = 0
saturating = 0
print(f"{'n':>5} {'p':>14} {'m=(q-1)/n':>10} {'log(q/n)':>9} {'log(q)':>8} {'gap=log n':>9} {'W1':>3} {'W2':>3} {'W3':>3}")
for (n, p) in cases:
    q = p
    m = (q - 1) // n
    # W1: m >= 1 (proper subgroup)
    w1 = (m >= 1)
    # W2: log((q-1)/n) <= log(q/n)  AND  the removed entropy log(q)-log(q/n) == log(n)
    lhs = math.log((q - 1) / n)
    rhs = math.log(q / n)
    w2_mono = (lhs <= rhs + 1e-12)
    removed = math.log(q) - math.log(q / n)
    w2_gap = abs(removed - math.log(n)) < 1e-9        # the collapse removes EXACTLY log n
    w2 = w2_mono and w2_gap
    # W3: target finite positive, strictly below the trivial log(q) target
    tgt = math.sqrt(2 * C0 * n * math.log(q / n))
    triv = math.sqrt(2 * C0 * n * math.log(q))
    w3 = (0 < tgt < triv)
    checked += 1
    if not (w1 and w2 and w3):
        fails += 1
    if abs(lhs - rhs) < 1e-9:   # would only saturate if n=q-1 (excluded) -> never
        saturating += 1
    print(f"{n:>5} {p:>14} {m:>10} {rhs:>9.4f} {math.log(q):>8.4f} {removed:>9.4f} "
          f"{str(w1):>3} {str(w2):>3} {str(w3):>3}")

print()
print(f"VERDICT: {checked-fails}/{checked} pass  (fails={fails}, saturating={saturating})")
print("W1 m>=1 (proper subgroup), W2 log((q-1)/n)<=log(q/n) & removed-entropy==log(n),")
print("W3 target sqrt(2 C0 n log(q/n)) finite-positive and < trivial sqrt(2 C0 n log q).")
print("The brick formalizes W1+W2 (pure algebra); the per-period tail (W-open) is the WALL, untouched.")
