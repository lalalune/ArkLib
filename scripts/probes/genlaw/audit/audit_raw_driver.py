"""AUDITOR raw-vs-DP cross-validation at s=32.
Samples feasible (O,mask) classes from MY sweeper records (r=3 and r=5),
stratified by (h,v,w), runs the assumption-free raw B brute force, and
compares counts. Also runs dead controls (classes absent from the records),
both parity-pure and mixed, which must give 0.
"""
import random, re, subprocess
from itertools import combinations

random.seed(424242)

def load(fn, r):
    recs = []
    for line in open(fn):
        if not line.startswith("REC"):
            continue
        head, m, hpart, vpart, wpart = line.split("|")
        O = tuple(int(x) for x in head.split()[1:1 + r])
        m = int(m)
        h = int(hpart.split()[1])
        v = int(vpart.split()[1])
        w = int(wpart.split()[1])
        recs.append((O, m, h, v, w))
    return recs

r3 = load("/tmp/genlaw/audit/recs_s32_r3.txt", 3)
r5 = load("/tmp/genlaw/audit/recs_s32_r5.txt", 5)
print(f"loaded {len(r3)} r=3 classes (waysum {sum(t[4] for t in r3)}), "
      f"{len(r5)} r=5 classes (waysum {sum(t[4] for t in r5)})")

def sample_strat(recs, per=1):
    by = {}
    for t in recs:
        by.setdefault((t[2], t[3]), []).append(t)
    out = []
    for k in sorted(by):
        out += random.sample(by[k], min(per, len(by[k])))
    return out, sorted(by)

s5, strata5 = sample_strat(r5, per=2)
print(f"r=5 (h,v) strata: {strata5}")
s3, strata3 = sample_strat(r3, per=1)
print(f"r=3 (h,v) strata: {strata3}")

# dead controls
feas5 = {(t[0], t[1]) for t in r5}
dead5 = []
while len(dead5) < 4:
    O = tuple(sorted(random.sample(range(32), 5)))
    m = random.randrange(16)
    if (O, m) in feas5:
        continue
    pure = len({o % 2 for o in O}) == 1
    if pure and sum(1 for t in dead5 if t[2] == "pure") < 2:
        dead5.append((O, m, "pure"))
    elif not pure and sum(1 for t in dead5 if t[2] == "mixed") < 2:
        dead5.append((O, m, "mixed"))

def run_raw(s, r, O, m):
    out = subprocess.run(["/tmp/genlaw/audit/audit_rawB", str(s), str(r)]
                         + [str(o) for o in O] + [str(m)],
                         capture_output=True, text=True).stdout
    return int(out.split("solutions = ")[1].split()[0])

fails = 0
print("\n--- r=5 feasible classes (raw over C(27,14) = 20,058,300 subsets each) ---")
for O, m, h, v, w in s5:
    got = run_raw(32, 5, O, m)
    ok = got == w
    fails += not ok
    print(f"  O={O} m={m} (h={h},v={v}) DP={w} RAW={got} {'OK' if ok else 'MISMATCH'}")

print("--- r=5 dead controls (expect 0) ---")
for O, m, lab in dead5:
    got = run_raw(32, 5, O, m)
    ok = got == 0
    fails += not ok
    print(f"  O={O} m={m} [{lab}] RAW={got} {'OK' if ok else 'MISMATCH'}")

print("--- r=3 feasible classes (raw over C(29,15) = 77,558,760 subsets each) ---")
for O, m, h, v, w in s3[:4]:
    got = run_raw(32, 3, O, m)
    ok = got == w
    fails += not ok
    print(f"  O={O} m={m} (h={h},v={v}) DP={w} RAW={got} {'OK' if ok else 'MISMATCH'}")

print(f"\nRAW-vs-DP: fails = {fails}")
assert fails == 0
print("ALL RAW CROSS-CHECKS PASS")
