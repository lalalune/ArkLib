"""Probe: compare the two Wick-route hypotheses on PROPER thin mu_n in prize regime.
  step-ratio form (WickStepRatio.lean):  cross_r <= 2 r n * E_r     (E_{r+1} <= (2r+1) n E_r)
  cond-pin form  (CharPWickConditionalPin.lean): cross_r <= 2 r n * Wick_r  (Wick_r=(2r-1)!! n^r)
Question: on clean rungs where E_r <= Wick_r, is the pin form STRICTLY WEAKER (easier) than the
step-ratio form? If E_r <= Wick_r then 2rn*E_r <= 2rn*Wick_r so pin RHS >= step RHS: step is the
STRONGER requirement, pin is the weaker/dominated-by-larger-RHS one. Confirm cross <= both, and that
they can DIVERGE (cross sits between when E_r < Wick_r strictly)."""
from itertools import product

def doublefact(m):
    r = 1
    while m > 1:
        r *= m
        m -= 2
    return r

def energy_via_freq(G, p, r):
    if r == 0:
        return 1
    freq = {}
    for v in product(G, repeat=r):
        d = sum(v) % p
        freq[d] = freq.get(d, 0) + 1
    return sum(c * c for c in freq.values())

def is_primroot(a, p):
    seen = set(); x = 1
    for _ in range(p - 1):
        x = x * a % p; seen.add(x)
    return len(seen) == p - 1

def mu_n(p, n):
    g = 2
    while not is_primroot(g, p):
        g += 1
    h = pow(g, (p - 1) // n, p)
    S = set(); x = 1
    for _ in range(n):
        x = x * h % p; S.add(x)
    return sorted(S)

cases = []
for n in [4, 8, 16]:
    target = n ** 4
    p = target | 1
    cnt = 0
    while cnt < 2:
        if all(p % k for k in range(2, int(p ** 0.5) + 1)) and (p - 1) % n == 0 and p - 1 > n:
            cases.append((n, p)); cnt += 1
        p += 2

hdr = f"{'n':>3} {'p':>7} {'r':>2} {'E_r':>8} {'Wick_r':>11} {'cross_r':>9} {'2rnE_r':>10} {'2rnWick':>11} {'step?':>6} {'pin?':>5} {'Er<=W?':>6}"
print(hdr)
all_step = True
all_pin = True
diverge = False
for (n, p) in cases:
    G = mu_n(p, n)
    assert len(G) == n and (p - 1) != n
    Es = {r: energy_via_freq(G, p, r) for r in range(0, 6)}
    for r in range(1, 5):
        cross = Es[r + 1] - n * Es[r]
        wick = doublefact(2 * r - 1) * n ** r
        step_rhs = 2 * r * n * Es[r]
        pin_rhs = 2 * r * n * wick
        step_ok = cross <= step_rhs
        pin_ok = cross <= pin_rhs
        erw = Es[r] <= wick
        if not step_ok: all_step = False
        if not pin_ok: all_pin = False
        if step_rhs != pin_rhs: diverge = True
        print(f"{n:>3} {p:>7} {r:>2} {Es[r]:>8} {wick:>11} {cross:>9} {step_rhs:>10} {pin_rhs:>11} {str(step_ok):>6} {str(pin_ok):>5} {str(erw):>6}")

print()
print(f"ALL step-ratio (cross<=2rnE_r) hold: {all_step}")
print(f"ALL pin (cross<=2rnWick_r)  hold:    {all_pin}")
print(f"RHS diverge (E_r < Wick_r somewhere): {diverge}")
print("Strength: when E_r <= Wick_r, 2rnE_r <= 2rnWick_r so the STEP-RATIO bound is the STRONGER")
print("requirement (smaller RHS). pin hypothesis is weaker/easier => the better attack target.")
