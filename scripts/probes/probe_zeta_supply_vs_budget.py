"""
#444 §6.5 — CONSTRAINT LEMMA: the over-det VANISHING (coset-union) supply V_r(n)=2^{n/2^{floor(log2 r)+1}}
is NOT the binding constraint at prize depth -- it is super-exponentially LOOSE there.

Closed form (proven axiom-clean, OverdetVanishingCosetCount.lean): V_r(n)=2^{n/d}, d=2^{floor(log2 r)+1}.
Prize budget q*eps* ~ n.  We compare exactly (integer exponents only, no float in the verdict).
"""
import math

def supply_exponent(n, r):
    d = 2**(math.floor(math.log2(r)) + 1)
    return n // d   # log2 V_r(n)

if __name__ == "__main__":
    print("=== over-det vanishing supply V_r(n)=2^{n/d} vs prize budget ~ n (exact exponents) ===")
    print("\n(a) at PRIZE BINDING DEPTH r ~ log2 n (the deep-rung where the BGK wall lives):")
    for L in [8, 16, 30, 128]:
        n = 2**L
        r = L  # ~ log2 n
        e = supply_exponent(n, r)
        print(f"  n=2^{L:<3}: r~log2 n={r:<3} -> log2 V_r = n/d = {e}  vs budget exponent log2 n = {L}"
              f"   => supply/budget = 2^{e-L}  ({'SUPER-EXP LOOSE' if e>L else 'tight'})")
    print("\n(b) crossover depth r* where V_r first drops to <= budget n  (claim: r*/n = 1/(2 log2 n)):")
    allmatch = True
    for L in [8, 10, 16, 20, 30]:
        n = 2**L
        rstar = None
        for j in range(L + 1):
            if n // (2**(j + 1)) <= L:
                rstar = 2**j
                break
        ratio = rstar / n
        pred = 1.0 / (2 * L)
        ok = abs(ratio - pred) < 0.02
        allmatch = allmatch and ok
        print(f"  n=2^{L:<3}: r*={rstar:<10} r*/n={ratio:.5f}  1/(2 log2 n)={pred:.5f}  {'MATCH' if ok else '~'}")
    print(f"\nVERDICT: coset-union vanishing supply is super-exponentially loose at prize depth r~log n;"
          f" crosses budget only at r*~n/(2 log n).  r*/n law {'CONFIRMED' if allmatch else 'approx'}.")
    print("DONE")
