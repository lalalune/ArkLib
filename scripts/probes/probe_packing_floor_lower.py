# PROBE (seeded 20260617): the packing deflation floor C(n,k+1)/C(a,k+1) is bounded BELOW
# by a constant at the prize band a <= n/2 -- the rigorous "packing collapses to O(1),
# provably cannot reach sub-Johnson sqrt(n)" no-go, formalized as a constraint lemma.
#
# Claim to test (REAL ratio): for k+1 <= a <= n/2,  C(n,k+1)/C(a,k+1) >= 2^(k+1).
# Clean Nat-provable surrogate (what Lean will prove): C(n,k+1) >= 2^(k+1) * C(a,k+1) when 2a <= n.
# This is the rigorous lower bound matching PackingDeflationBandAntitone's probe-only
# "saturates at 2^(k+1)" assertion. It proves the under-det packing distinct-gamma floor
# is Omega(1), hence CANNOT deliver an o(sqrt(n)) cap => packing face collapses to Johnson.
from math import comb

def test():
    bad_real = 0
    bad_nat = 0
    total = 0
    # also test the sharper a-product engine: C(n,j) >= 2^j * C(a,j) for 2a <= n
    bad_engine = 0
    for k in range(1, 7):
        j = k + 1
        for n in range(2 * j, 700):
            for a in range(j, n // 2 + 1):  # prize band a <= n/2
                total += 1
                Cn = comb(n, j)
                Ca = comb(a, j)
                if Cn / Ca < 2 ** j - 1e-9:
                    bad_real += 1
                    if bad_real <= 5:
                        print(f"REAL FAIL n={n} k={k} a={a}: {Cn/Ca:.4f} < {2**j}")
                if Cn < (2 ** j) * Ca:
                    bad_nat += 1
                    if bad_nat <= 8:
                        print(f"NAT FAIL n={n} k={k} a={a}: C(n,j)={Cn} < {2**j}*C(a,j)={2**j*Ca}")
    # engine sweep: C(2a, j) >= 2^j * C(a, j) (the n=2a tight case) and monotone above
    for j in range(2, 8):
        for a in range(j, 400):
            if comb(2 * a, j) < (2 ** j) * comb(a, j):
                bad_engine += 1
                if bad_engine <= 5:
                    print(f"ENGINE FAIL a={a} j={j}: C(2a,j)={comb(2*a,j)} < {2**j}*C(a,j)={2**j*comb(a,j)}")
    print(f"\nREAL ratio >= 2^(k+1):                          {total - bad_real}/{total} pass")
    print(f"NAT product C(n,k+1) >= 2^(k+1)*C(a,k+1), 2a<=n: {total - bad_nat}/{total} pass")
    print(f"ENGINE C(2a,j) >= 2^j*C(a,j) (tight case):       {'ALL pass' if bad_engine==0 else str(bad_engine)+' FAIL'}")
    # show the tight case is EXACTLY 2^j at small j (saturation, matches PackingDeflationBandAntitone probe)
    print("\nTIGHTNESS at n=2a (the a=n/2 prize band), ratio C(2a,j)/C(a,j):")
    for j in [2, 3, 4]:
        vals = [round(comb(2 * a, j) / comb(a, j), 3) for a in [j, 2 * j, 8 * j, 64 * j]]
        print(f"  j={j} (k={j-1}): a in [j,2j,8j,64j] -> {vals}  (-> 2^j={2**j} from ABOVE)")

test()
