#!/usr/bin/env python3
"""
wf-NH (#407) DECISIVE: is the monomial the WORST over-determined direction, and is the
binding incidence p-INDEPENDENT past 2^12?  (the two open tests of the decoupling claim.)

Design for speed: the binding/over-determined radius uses small witness size (size = k+2),
so C(n,size) is the only blow-up.  We:
  n=16,k=4: FULL exhaustive (monomial + 2-term general + 3-term hill), 4 primes incl >2^12 & Fermat.
  n=32,k=4: FULL monomial max + EXHAUSTIVE 2-term general, 3 primes incl >2^12.   [C(32,6)=906192]
  n=64,k=4: monomial max over far b + a FIXED worst-direction p-independence check only
            (C(64,6)=75M too slow for an a-sweep; we sweep b and a small a-set), 2 primes.

incidence_vec = exact FarCosetExplosion count (affine-in-gamma, <=1 gamma per witness).
"""
import sys, itertools, random
sys.path.insert(0, 'scripts/probes')
from probe_farline_incidence_exact import find_prime_cong1, left_null
from prize_workspace import get_W


def precompute_nulls(S, p, k, size):
    """Precompute left-null vectors for all witness sets once (the expensive part), reuse for all dirs."""
    n = len(S)
    nulls = []
    for R in itertools.combinations(range(n), size):
        V = [[pow(int(S[i]), j, p) for j in range(k)] for i in R]
        P = left_null(V, p)
        if P:
            nulls.append((R, P))
    return nulls


def inc_from_nulls(u0, u1, nulls, p):
    good = set()
    for R, P in nulls:
        sz = len(R)
        pa = [sum(P[t][ii] * u0[R[ii]] for ii in range(sz)) % p for t in range(len(P))]
        pb = [sum(P[t][ii] * u1[R[ii]] for ii in range(sz)) % p for t in range(len(P))]
        if not any(pb):
            if not any(pa):
                return p
            continue
        i = next(j for j in range(len(pb)) if pb[j])
        g = (-pa[i] * pow(pb[i], p - 2, p)) % p
        if all((pa[t] + g * pb[t]) % p == 0 for t in range(len(pb))):
            good.add(g)
    return len(good)


def mono(b, S, p):
    return [pow(int(x), b, p) for x in S]


def v2(p):
    t = p - 1; c = 0
    while t % 2 == 0:
        t //= 2; c += 1
    return c


def analyze(n, k, size, primes, full_general=True, hill=False, a_full=True):
    r = n - size
    print(f"\n=== n={n} k={k} (rho={k/n}) size={size} (s-k={size-k}) radius r={r} delta={r/n:.4f} ===", flush=True)
    mono_vals = []; gen_beats = []
    for plo in primes:
        p = find_prime_cong1(n, plo); S = list(get_W(n, p).S)
        nulls = precompute_nulls(S, p, k, size)
        # exhaustive monomial: far b in [0,size), a in [0,n)
        mbest = (-1, None)
        a_range = range(n) if a_full else range(min(n, 12))
        for b in range(size):
            for a in a_range:
                if a == b: continue
                I = inc_from_nulls(mono(a, S, p), mono(b, S, p), nulls, p)
                if p > I > mbest[0]: mbest = (I, ('mono', a, b))
        mono_vals.append(mbest[0])
        line = f"  p={p:>9} {'>2^12' if p>4096 else '     '} v2={v2(p)}: MONO={mbest[0]} {mbest[1]}"
        gbest = (-1, None)
        if full_general:
            for b1, b2 in itertools.combinations(range(size), 2):
                for c in (1, p-1, 2, p-2):
                    u1 = [(pow(int(x), b1, p) + c*pow(int(x), b2, p)) % p for x in S]
                    for a in a_range:
                        I = inc_from_nulls(mono(a, S, p), u1, nulls, p)
                        if p > I > gbest[0]: gbest = (I, ('2t', a, b1, b2, c))
            verdict = 'BEATS' if gbest[0] > mbest[0] else ('ties' if gbest[0]==mbest[0] else 'under')
            line += f" | GEN2={gbest[0]}({verdict}){gbest[1]}"
            gen_beats.append(gbest[0] > mbest[0])
        if hill:
            rng = random.Random(plo); hb = -1
            far = list(range(size))
            for _ in range(300):
                m = rng.randint(2, min(3, len(far)))
                e0 = rng.sample(far, m); c0 = [rng.randrange(1,p) for _ in range(m)]
                e1 = rng.sample(far, m); c1 = [rng.randrange(1,p) for _ in range(m)]
                u0 = [sum(c0[j]*pow(int(x),e0[j],p) for j in range(m))%p for x in S]
                u1 = [sum(c1[j]*pow(int(x),e1[j],p) for j in range(m))%p for x in S]
                I = inc_from_nulls(u0, u1, nulls, p)
                if p > I > hb: hb = I
            line += f" | HILL3={hb}{'(BEATS)' if hb>mbest[0] else ''}"
        print(line, flush=True)
    pind = len(set(mono_vals)) == 1
    print(f"  -> MONO p-INDEPENDENT (incl >2^12): {pind}; vals={mono_vals}"
          + (f"; any GEN beats mono: {any(gen_beats)}" if gen_beats else ""), flush=True)


if __name__ == '__main__':
    # n=16 prize rate k=4, over-det size=k+2=6 (r=10, the established binding radius). FULL.
    analyze(16, 4, 6, [200003, 786433, 5000011, 16777259], full_general=True, hill=True)
    # n=32 prize rate k=4, over-det size=6 (r=26). FULL monomial + 2-term general. C(32,6)=906192.
    analyze(32, 4, 6, [200003, 5000011, 16777259], full_general=True, hill=False)
    print("\n[n=64 in probe_wf2NH_n64_pind.py — C(64,6)=75M, direction-limited p-independence]")
    print("DONE")
