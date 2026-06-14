"""Aggregate r=5 worker outputs per prime: sum SUMMARY fields, cross-check the
char-0 side (sum + per-class vs audit recs), classify spurious classes
(char-0-feasible vs infeasible), and emit a random sample of flagged classes
for the class-mode brute triple-check."""
import re, sys, random
from collections import defaultdict

prime_files = {
    "2013265921": ["r5_bb_w0.txt", "r5_bb_w1.txt", "r5_bb_w2.txt"],
    "3221225473": ["r5_p2_w0.txt", "r5_p2_w1.txt", "r5_p2_w2.txt"],
}

audit = {}
for line in open("audit_s32_r5.txt"):
    if not line.startswith("REC "):
        continue
    head, m, hpart, vpart, wpart = line.split("|")
    O = tuple(int(x) for x in head.split()[1:6])
    audit[(O, int(m))] = (int(hpart.split()[1]), int(vpart.split()[1]),
                          int(wpart.split()[1]))

random.seed(64)
for p, files in prime_files.items():
    tot = defaultdict(int)
    spur = []          # (O, m, char0, modp)
    mine = {}
    xih = []
    for fn in files:
        for line in open(fn):
            if line.startswith("SUMMARY"):
                for k, v in re.findall(r"(\w+)=(\d+)", line):
                    tot[k] += int(v)
            elif line.startswith("SPUR "):
                mm = re.match(r"SPUR O=([\d,]+) m=(\d+) char0=(\d+) modp=(\d+)", line)
                O = tuple(int(t) for t in mm.group(1).split(","))
                spur.append((O, int(mm.group(2)), int(mm.group(3)), int(mm.group(4))))
            elif line.startswith("C0REC"):
                head, m, hpart, vpart, wpart = line.split("|")
                O = tuple(int(x) for x in head.split()[1:6])
                mine[(O, int(m))] = (int(hpart.split()[1]), int(vpart.split()[1]),
                                     int(wpart.split()[1]))
            elif line.startswith("XI "):
                xih.append(line.strip())
    assert mine == audit, "per-class char-0 mismatch vs audit DP!"
    nfeas_spur = sum(1 for _, _, c0, _ in spur if c0 > 0)
    exc_feas = sum(mp - c0 for _, _, c0, mp in spur if c0 > 0)
    exc_infeas = sum(mp - c0 for _, _, c0, mp in spur if c0 == 0)
    print(f"== p = {p} ==")
    print(f"  classes={tot['classes']} feas={tot['feas']} "
          f"char0_sum={tot['char0_sum']} modp_sum={tot['modp_sum']}")
    print(f"  spur_classes={tot['spur_classes']} spur_excess={tot['spur_excess']}")
    print(f"  spur on char0-FEASIBLE classes: {nfeas_spur} classes, excess {exc_feas}")
    print(f"  spur on char0-INFEASIBLE classes: {len(spur)-nfeas_spur} classes, "
          f"excess {exc_infeas}")
    print(f"  per-class char-0 == audit DP: True ({len(mine)} feasible classes)")
    print(f"  xi-in-mu64 classes mod p: {tot['xiH']} (feasible: {tot['xiH_feas']})")
    for line in xih[:10]:
        print(f"    {line}")
    assert tot["classes"] == 3222016 and tot["char0_sum"] == 99512
    assert tot["modp_sum"] - tot["char0_sum"] == tot["spur_excess"]
    samp = random.sample(spur, min(25, len(spur)))
    with open(f"r5_sample_{p}.txt", "w") as f:
        for O, m, c0, mp in samp:
            f.write(f"{','.join(map(str,O))} {m} {c0} {mp}\n")
    print(f"  wrote {len(samp)}-class brute-verification sample -> r5_sample_{p}.txt")
    print()
