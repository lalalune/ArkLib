"""Pick a stratified sample of (O,sigma) classes at n=64 and compare the engine's
predicted C(v,k) count against the RAW C brute force (no forced/free rule).
Sample: one feasible class per (h,v,k) stratum + both mega z*-types + dead classes
(engine-infeasible pure-parity, mixed-parity, odd-axis-fail) which must give 0."""
import json, subprocess, random
from itertools import combinations
from math import comb

cl = json.load(open("/tmp/genlaw/n64_class_records.json"))
feas = {(tuple(c['O']), tuple(c['sig'])): c for c in cl}
random.seed(64232)

picks = []   # (O, sig, expected, label)
seen_strata = set()
for c in sorted(cl, key=lambda c: (c['h'], c['O'], c['sig'])):
    key = (c['h'], c['v'], c['k'])
    if key not in seen_strata:
        seen_strata.add(key)
        picks.append((c['O'], c['sig'], c['ways'], f"stratum {key}"))
# mega z*-axis classes (forced B on z*-axis): forced contains 8 or 24
for c in cl:
    if 8 in c['forced']:
        picks.append((c['O'], c['sig'], c['ways'], "mega LB|OP")); break
for c in cl:
    if 24 in c['forced']:
        picks.append((c['O'], c['sig'], c['ways'], "mega LO|PB")); break
# dead classes: 2 pure-parity infeasible, 2 mixed-parity, expect 0
SIGS = [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]
dead_pure, dead_mixed = [], []
allO = list(combinations(range(32), 3))
random.shuffle(allO)
for O in allO:
    pure = (O[0] % 2 == O[1] % 2 == O[2] % 2)
    for sig in SIGS:
        if (tuple(O), sig) in feas:
            continue
        if pure and len(dead_pure) < 2:
            dead_pure.append((O, sig))
        elif not pure and len(dead_mixed) < 2:
            dead_mixed.append((O, sig))
    if len(dead_pure) >= 2 and len(dead_mixed) >= 2:
        break
for O, sig in dead_pure:
    picks.append((list(O), list(sig), 0, "dead pure-parity"))
for O, sig in dead_mixed:
    picks.append((list(O), list(sig), 0, "dead mixed-parity"))

print(f"running RAW brute force on {len(picks)} classes "
      f"(each = C(29,15) = {comb(29,15):,} subsets)...")
fails = 0
for O, sig, exp, label in picks:
    out = subprocess.run(["/tmp/genlaw/raw_brute", str(O[0]), str(O[1]), str(O[2]),
                          str(sig[0]), str(sig[1])],
                         capture_output=True, text=True).stdout.strip()
    got = int(out.split("raw solutions = ")[1].split()[0])
    status = "OK" if got == exp else "MISMATCH"
    if got != exp:
        fails += 1
    print(f"  [{label:>18}] {out}   engine expects {exp}  -> {status}")
print(f"\nRAW-vs-ENGINE: {len(picks) - fails}/{len(picks)} classes agree exactly"
      + ("" if fails == 0 else f"  ({fails} MISMATCHES!)"))
