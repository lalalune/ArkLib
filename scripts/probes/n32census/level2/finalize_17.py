#!/usr/bin/env python3
"""finalize_17.py — combine the aggregator output (exact-17 gamma counts) with the
agree>=18 layer (stage18.json) into the exact a=17 census readouts.

Exactness arguments (both used as cross-foots):
  * 2*17 > 32  =>  a codeword agreeing >=17 with u0+g1*u1 and u0+g2*u1 forces u1=0 on
    T1 ∩ T2 != {} — impossible; so each codeword belongs to exactly one gamma and
    union size = total distinct (gamma,ev) pairs.
  * a pair with agreement exactly 17 has a unique 17-point agreement set = the unique
    subset that emitted it => binary emissions <-> exact-17 distinct pairs, bijectively;
    a pair with agreement A>=18 is emitted as a full record by each of its C(A,17) subsets.
  * coverage: subsets = sb0 + deg + floor_emissions + sum_pairs C(agree,17) = C(32,17).
"""
import json, math, sys
from collections import Counter

FAIL = []
def check(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" — {detail}" if detail else ""))
    if not ok: FAIL.append(name)

st = json.load(open("/tmp/level2/stage18.json"))
agg = {}
hist = Counter(); qcnt = {}
for line in open("/tmp/level2/agg_out.txt"):
    f = line.split()
    if f[0] == "hist": hist[int(f[1])] = int(f[2])
    elif f[0] == "q": qcnt[int(f[1])] = int(f[2])
    else: agg[f[0]] = int(f[1])

check("aggregator saturation = 0 (uint16 counts exact)", agg["sat"] == 0, f"sat={agg['sat']}")
check("aggregator total = sum of chunk floor counters", agg["total"] == st["floor_total_counter"],
      f"{agg['total']} vs {st['floor_total_counter']}")
check("aggregator histogram self-consistent (sum c*hist[c] = total, sum hist = distinct)",
      sum(c*n for c, n in hist.items()) == agg["total"] and sum(hist.values()) == agg["distinct"])

# coverage cross-foot
total_subsets = st["sb0"] + st["deg"] + agg["total"] + st["ge18_subset_emissions"]
check("COVERAGE: sb0 + deg + exact17-emissions + sum_pairs C(agree,17) = C(32,17)",
      total_subsets == math.comb(32, 17), f"{total_subsets} vs {math.comb(32,17)}")

ge18 = {int(k): v for k, v in st["ge18_per_gamma"].items()}
check("all agree>=18 gammas present in query dump", set(ge18) == set(qcnt))

# distinct gammas at a=17
new_g = sum(1 for g_, c in qcnt.items() if c == 0)
n_gamma_17 = agg["distinct"] + new_g
# per-gamma list-size histogram at a=17: size(g) = exact17_count(g) + ge18_distinct(g)
size_hist = Counter(hist)            # start: gammas with only exact-17 pairs
for g_, d in ge18.items():
    b = qcnt[g_]
    if b > 0:
        size_hist[b] -= 1
        if size_hist[b] == 0: del size_hist[b]
    size_hist[b + d] += 1
union_17 = agg["total"] + st["ge18_pairs"]
check("histogram mass = distinct gammas", sum(size_hist.values()) == n_gamma_17)
check("sum of per-gamma list sizes = union size (codeword-disjointness across gammas)",
      sum(s*n for s, n in size_hist.items()) == union_17)

print(f"\n== a=17 (sub-witness) exact census ==")
print(f"gammas with nonempty list: {n_gamma_17:,}")
print(f"  (= {agg['distinct']:,} from the exact-17 stream + {new_g} agree>=18 gammas with no exact-17 pair)")
print(f"union list size (= total distinct (gamma,ev) pairs): {union_17:,}")
print(f"per-gamma list-size histogram: {dict(sorted(size_hist.items()))}")
print(f"max per-gamma list size: {max(size_hist)}")
frac_g = n_gamma_17 / (15*(1<<27)+1)
print(f"fraction of F_p hit as a bad scalar at a=17: {frac_g:.4f}")
json.dump({"n_gamma_17": n_gamma_17, "union_17": union_17,
           "size_hist": {str(k): v for k, v in sorted(size_hist.items())},
           "exact17_pairs": agg["total"], "raw_gamma_emission_hist": {str(k): v for k, v in sorted(hist.items())}},
          open("/tmp/level2/stage17.json", "w"))
print(f"\nfailures: {FAIL or 'none'}")
sys.exit(1 if FAIL else 0)
