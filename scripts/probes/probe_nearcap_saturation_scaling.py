"""
Near-capacity saturation SCALING vs n  (#407, prong 2).

Background (n=32 finding, prior probe): the NEAR-CAPACITY in-window band incidence
I_pencil(w) GROWS with p (slow-clearing mod-p sumset pollution) but SATURATES at a
fixed value and the FRACTION I/p -> 0. The δ*-crossing band, by contrast, is
char-INVARIANT for p >> n^3. The open question for the BGK wall:

  Does the saturation p-THRESHOLD (the prime above which the near-capacity band
  stops growing = "pollution clears") GROW with n in a way that would let the
  char-dependent / slow-clearing region reach the δ*-crossing as n -> ∞?

This probe measures, for n = 16, 32, 64 (constant rate k=4, ρ = 4/n):
  - the near-capacity band incidence I(w_cap) as a function of p (sweep many primes)
  - the saturation VALUE (where I stops increasing)
  - the saturation p-THRESHOLD p*(n) = smallest prime where |I(p)-I_sat| is small
  - the distance-to-capacity of the measured band
Tabulate p*(n) / n^c for several c to read off the growth exponent.

Method: identical exact non-enumerative incidence (per (k+1)-subset solve for
(g,γ), true agreement). Reuses the n=64 batch solver. Near-capacity band = the
smallest w that is still INSIDE the window upper edge, i.e. just below w_cap = n-k
(capacity radius δ = ρ = k/n => w = n-k). We take a couple of bands near the top:
w in {n-k-2, n-k-1, n-k} (just inside capacity).
"""
import itertools, math, sys, time
import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from probe_charinv_constrate_n64 import isp, proot, batch_solve_mod, bandcounts  # noqa


def sweep(n, k, a, b, primes):
    """Return {p: bandcounts dict} for the given pencil over a prime sweep."""
    prof = {}
    for p in primes:
        t0 = time.time()
        bc = bandcounts(p, n, k, a, b, verbose=False)
        prof[p] = bc
        sys.stderr.write(f"  n={n} ({a},{b}) p={p} [{time.time()-t0:.0f}s]\n")
        sys.stderr.flush()
    return prof


def main():
    # constant rate k=4: rho = 4/n. capacity band w_cap = n-k.
    configs = [
        # n, k, pencils, prime sweep (thin -> p >> n^3), spaced to see growth+saturation
        (16, 4, [(5, 7), (6, 7)],
         [97, 193, 257, 1153, 4129, 8209, 12289, 40961, 65537, 274177, 557057]),
        (32, 4, [(5, 7), (9, 13)],
         [577, 1153, 12289, 40961, 65537, 274177, 557057, 786433, 1179649, 5767169]),
        (64, 4, [(5, 7), (9, 13)],
         [193, 449, 65537, 274177, 786433, 1179649, 5767169, 13631489]),
    ]
    table = []  # rows: (n, w, dist_to_cap, p_threshold, I_sat, fraction_at_max_p)
    for n, k, pencils, cand in configs:
        n3 = n ** 3
        primes = sorted(p for p in cand if isp(p) and (p - 1) % n == 0)
        # capacity radius delta_cap = 1 - rho => w_cap = rho*n = k. I(w) defined for w>=k+1.
        # NEAR-CAPACITY = high delta = LOWEST bands just above the floor: w in {k+1,k+2,k+3}
        # (matches the prior n=32 finding "w=6"=k+2, delta=0.8125 vs capacity 0.875).
        print(f"\n=== n={n} k={k} rho={k/n} n^3={n3} capacity delta=1-rho={1-k/n:.4f} ===", flush=True)
        print(f"primes={primes}", flush=True)
        for (a, b) in pencils:
            prof = sweep(n, k, a, b, primes)
            print(f"\npencil({a},{b}) gcd={math.gcd(b-a,n)}:", flush=True)
            # near-capacity bands w in {k+1, k+2, k+3} (high delta, just below capacity)
            for w in [k + 1, k + 2, k + 3]:
                if w > n:
                    continue
                series = [(p, prof[p][w]) for p in primes]
                d = 1 - w / n
                dcap = 1 - k / n
                vals = [v for _, v in series]
                print(f"  band w={w} (delta={d:.3f}, capacity delta=1-rho={dcap:.3f}, "
                      f"dist-to-cap={dcap-d:+.3f}):", flush=True)
                for p, v in series:
                    frac = v / p
                    print(f"      p={p:>8} (p/n^3={p/n3:6.2f}): I={v:>6}  I/p={frac:.2e}",
                          flush=True)
                # saturation: max value; threshold = smallest prime within 5% of max, restricting p>n^3
                bigser = [(p, prof[p][w]) for p in primes if p > n3]
                if not bigser:
                    continue
                imax = max(v for _, v in bigser)
                dist2cap = dcap - d  # >0; how far this band's delta is below capacity
                if imax == 0:
                    print(f"     -> band identically 0 for p>n^3 (cleared); no growth", flush=True)
                    table.append((n, w, dist2cap, None, 0, 0.0))
                    continue
                thr = None
                for p, v in bigser:
                    if v >= 0.95 * imax:
                        thr = p
                        break
                pmax = bigser[-1][0]
                fracmax = bigser[-1][1] / pmax
                print(f"     -> I_sat≈{imax}  p*(saturation,≥95%)={thr} (p*/n^3={thr/n3:.2f})"
                      f"  I/p at p_max={fracmax:.2e}", flush=True)
                table.append((n, w, dist2cap, thr, imax, fracmax))

    # final scaling table
    print("\n\n===== SATURATION-THRESHOLD SCALING TABLE =====", flush=True)
    print(f"{'n':>4} {'w':>4} {'dist2cap':>9} {'p*(sat)':>10} {'p*/n^3':>8} "
          f"{'p*/n^4':>8} {'I_sat':>7} {'I/p@max':>10}", flush=True)
    for n, w, dist, thr, isat, frac in table:
        if thr is None:
            print(f"{n:>4} {w:>4} {dist:>+9.3f} {'cleared':>10} {'--':>8} {'--':>8} "
                  f"{isat:>7} {frac:>10.2e}", flush=True)
        else:
            print(f"{n:>4} {w:>4} {dist:>+9.3f} {thr:>10} {thr/n**3:>8.2f} {thr/n**4:>8.4f} "
                  f"{isat:>7} {frac:>10.2e}", flush=True)
    print("\nInterpretation: if p*(sat)/n^3 GROWS with n, the slow-clearing near-capacity"
          "\nregion encroaches; if p*/n^c is FLAT for some fixed c, the pollution-clearing"
          "\nthreshold scales as n^c and the band stays a fixed distance from delta*.", flush=True)


if __name__ == "__main__":
    main()
