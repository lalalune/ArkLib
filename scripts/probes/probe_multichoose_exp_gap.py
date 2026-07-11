#!/usr/bin/env python3
"""
probe_multichoose_exp_gap.py  (#444/#407, lane kambire-expgap)

KambireNotExtremal.lean PROVED choose s r < multichoose s r (=C(s+r-1,r)) strictly, but the
EXPONENT-level gap (multichoose/choose ~ 2^{0.26 s}, super-poly, NOT a constant) is only stated
NUMERICALLY in prose. That exponent gap is the actual content: it's why the complete-homogeneous
worst direction changes the LEADING ORDER of delta*, not just a constant.

This probe finds a CLEAN, PROVABLE exponential lower bound on multichoose s r / choose s r so it can
be formalized as a real brick.

Candidate clean bounds (want something with an elementary Lean proof):
  (a) at r = s:        multichoose s s = C(2s-1, s) >= 2^{s-1}, choose s s = 1 -> ratio >= 2^{s-1}.
  (b) general r:       multichoose s r / choose s r = prod_{i=0}^{r-1} (s-1+r-i)/(s-i)
                       = C(s+r-1,r)/C(s,r). Check >= 2^{c r} type bounds.
  (c) the prize depth r = s/2:  log2(ratio)/s -> 0.26... confirm the constant.

We want a bound that is (i) TRUE for all valid s,r in regime, (ii) has a clean elementary proof.
The cleanest: C(s+r-1, r) >= C(s+r-1, r) and a doubling chain. Probe several to pick.
"""
import sys
from math import comb, log2

def multichoose(s, r):
    return comb(s + r - 1, r) if (s + r - 1) >= 0 else 0

def main():
    print("=== (c) prize depth r = s/2: log2(multichoose/choose)/s -> 0.26 ? ===")
    for a in range(2, 9):
        s = 1 << a
        r = s // 2
        ch = comb(s, r)
        mc = multichoose(s, r)
        ratio = mc / ch
        print(f"  s={s:4d} r=s/2={r:3d}: choose={ch:.3e} multichoose={mc:.3e} "
              f"ratio={ratio:.4e} log2(ratio)/s={log2(ratio)/s:.4f}")

    print("\n=== (a) r=s clean bound: multichoose s s = C(2s-1,s) >= 2^{s-1} ? ===")
    allok = True
    for s in range(1, 25):
        mc = multichoose(s, s)            # = C(2s-1, s)
        lb = 2 ** (s - 1)
        ok = mc >= lb
        allok &= ok
        if s <= 12 or not ok:
            print(f"  s={s:3d}: C(2s-1,s)={mc} >= 2^(s-1)={lb}  {ok}")
    print(f"  ALL r=s: C(2s-1,s) >= 2^(s-1) : {allok}")

    print("\n=== (b) doubling-chain lower bound: multichoose s r >= 2^r * choose s r / something ? ===")
    # Try: ratio = prod_{i=0}^{r-1} (s+r-1-i)/(s-i). Each factor (s+r-1-i)/(s-i) >= 1 (already).
    # When r<=s, the LARGEST factor analysis. Check the clean claim:
    #   C(s+r-1,r) >= C(s+r-1, r) trivially; want >= 2^r when r <= s-? Let's test 2^r <= ratio.
    allok2 = True
    fails = []
    for s in range(2, 40):
        for r in range(1, s + 1):
            ratio = multichoose(s, r) / comb(s, r)
            if ratio < 2 ** (r * 0.0):    # placeholder
                pass
    # test specific clean claim: for r <= s, C(s+r-1, r) >= 2^(r-1) * C(s, r)?? probe
    print("  testing C(s+r-1,r) >= 2^? * C(s,r):")
    for s in [8, 16, 32]:
        for r in [2, s//4, s//2, s]:
            if r < 1 or r > s: continue
            ratio = multichoose(s, r) / comb(s, r)
            print(f"    s={s} r={r}: ratio={ratio:.4e} log2={log2(ratio):.3f} "
                  f"log2/r={log2(ratio)/r:.4f} log2/s={log2(ratio)/s:.4f}")

    print("\n=== CLEANEST PROVABLE: at r=s, C(2s-1,s) >= 2^{s-1} (Lean: central binom >= 2^n family) ===")
    print("    AND the strict exponent gap is exhibited; r=s is in-regime (deep band).")

    print("\n=== (d) DEEP-BAND extension: multichoose s r monotone in r (s>=1) + >= 2^{s-1} for r>=s ===")
    band_ok = True
    for s in [8, 16]:
        vals = [multichoose(s, r) for r in range(0, 2 * s + 1)]
        mono = all(vals[i] <= vals[i + 1] for i in range(len(vals) - 1))
        band = all(multichoose(s, r) >= 2 ** (s - 1) for r in range(s, 2 * s + 1))
        band_ok &= (mono and band)
        print(f"  s={s}: multichoose monotone-up over r=0..2s = {mono}; "
              f"multichoose s r >= 2^(s-1) for all r in [s,2s] = {band}")
    # show the s=0 degeneracy that forces the s>=1 hypothesis
    print(f"  (degeneracy check) multichoose 0 0 = {multichoose(0,0)} > multichoose 0 1 = "
          f"{multichoose(0,1)}  -> monotonicity needs s>=1, as formalized")
    print(f"  DEEP-BAND (s>=1): monotone + 2^(s-1) floor across [s,2s] : {band_ok}")
    sys.exit(0 if (allok and band_ok) else 1)

if __name__ == "__main__":
    main()
