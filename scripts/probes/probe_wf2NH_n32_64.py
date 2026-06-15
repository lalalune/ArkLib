#!/usr/bin/env python3
"""
wf-NH (#407): n=32 and n=64 over-determined binding-incidence p-independence + general-direction test.
Reuses precompute_nulls (one null-space pass per prime) from probe_wf2NH_decisive.
n=32: full monomial max + a FOCUSED 2-term general set (winner-perturbations + random structured).
n=64: monomial max + p-independence of the winning direction across 2 primes (C(64,6)=75M: 1 pass/prime).
"""
import sys, itertools, random
sys.path.insert(0, 'scripts/probes')
from probe_farline_incidence_exact import find_prime_cong1
from prize_workspace import get_W
from probe_wf2NH_decisive import precompute_nulls, inc_from_nulls, mono, v2


def run_n(n, k, size, primes, focused_general=True, n_rand=120):
    r = n - size
    print(f"\n=== n={n} k={k} size={size}(s-k={size-k}) r={r} delta={r/n:.4f} ===", flush=True)
    mono_vals = []; gen_beat = []
    for plo in primes:
        p = find_prime_cong1(n, plo); S = list(get_W(n, p).S)
        print(f"  [building nulls p={p} ...]", flush=True)
        nulls = precompute_nulls(S, p, k, size)
        print(f"  [{len(nulls)} non-trivial witness nulls]", flush=True)
        mbest = (-1, None)
        for b in range(size):
            for a in range(n):
                if a == b: continue
                I = inc_from_nulls(mono(a, S, p), mono(b, S, p), nulls, p)
                if p > I > mbest[0]: mbest = (I, (a, b))
        mono_vals.append(mbest[0])
        line = f"  p={p:>10} {'>2^12' if p>4096 else ''} v2={v2(p)}: MONO={mbest[0]} at{mbest[1]}"
        if focused_general:
            gbest = (-1, None)
            cands = []
            ab = mbest[1]
            # perturb winning direction b with a 2nd far term
            for b2 in range(size):
                if b2 == ab[1]: continue
                for c in (1, p-1, 2, p-2):
                    cands.append(('p', ab[0], ab[1], b2, c))
            rng = random.Random(plo)
            for _ in range(n_rand):
                b1, b2 = rng.sample(range(size), 2); c = rng.randrange(1, p)
                a = rng.randrange(n)
                cands.append(('p', a, b1, b2, c))
            for cd in cands:
                _, a, b1, b2, c = cd
                u1 = [(pow(int(x), b1, p) + c*pow(int(x), b2, p)) % p for x in S]
                I = inc_from_nulls(mono(a, S, p), u1, nulls, p)
                if p > I > gbest[0]: gbest = (I, cd)
            verdict = 'BEATS' if gbest[0] > mbest[0] else ('ties' if gbest[0]==mbest[0] else 'under')
            line += f" | GEN2={gbest[0]}({verdict})"
            gen_beat.append(gbest[0] > mbest[0])
        print(line, flush=True)
    print(f"  -> MONO p-INDEPENDENT (incl >2^12): {len(set(mono_vals))==1}; vals={mono_vals}"
          + (f"; GEN beats: {any(gen_beat)}" if gen_beat else ""), flush=True)


if __name__ == '__main__':
    import os
    which = os.environ.get('NH_WHICH', '32')
    if which == '32':
        run_n(32, 4, 6, [200003, 5000011, 16777259], focused_general=True, n_rand=100)
    elif which == '64':
        run_n(64, 4, 6, [200003, 16777259], focused_general=True, n_rand=40)
    print("DONE")
