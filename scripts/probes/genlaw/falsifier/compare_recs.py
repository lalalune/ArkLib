"""Per-class cross-check: my placement-rule records (C0REC) vs the audit's
independent per-axis generating-polynomial DP sweeper (REC). Exact dict
equality on (O, m) -> (h, v, w)."""
import sys

def load(fn, tag, r):
    d = {}
    for line in open(fn):
        if not line.startswith(tag + " "):
            continue
        head, m, hpart, vpart, wpart = line.split("|")
        O = tuple(int(x) for x in head.split()[1:1 + r])
        m = int(m)
        h = int(hpart.split()[1])
        v = int(vpart.split()[1])
        w = int(wpart.split()[1])
        d[(O, m)] = (h, v, w)
    return d

mine_f, audit_f, r = sys.argv[1], sys.argv[2], int(sys.argv[3])
mine = load(mine_f, "C0REC", r)
audit = load(audit_f, "REC", r)
assert mine == audit, (
    f"MISMATCH: {len(mine)} vs {len(audit)}; "
    f"only-mine {list(set(mine) - set(audit))[:5]}; "
    f"only-audit {list(set(audit) - set(mine))[:5]}; "
    f"diff-vals {[k for k in mine if k in audit and mine[k]!=audit[k]][:5]}")
print(f"OK {mine_f} == {audit_f}: {len(mine)} feasible classes, "
      f"waysum {sum(w for _,_,w in mine.values())} -- per-class (h,v,w) identical")
