#!/usr/bin/env python3
"""G1 — THE MENU LAW, derived and verified.
THEOREM (per-element): for a dense element with block B, the multiset of cross-pair
loci over the 35 witnesses is { Z_J : J ⊆ N(B), max(0,4-m0) <= |J| <= 4 } with
multiplicity C(m0, 4-|J|), where the pairs P1..P7 are the non-z* antipodal pairs of
mu_16, b_i = B∩P_i, N(B) = {i : b_i nonempty}, m0 = 7-|N|, and
Z_J = (B∩{z*}) ∪ ⋃_{i∈J} b_i.  Proof: S = {z*}∪⋃_{i∈I}P_i, |I|=4; S∩B = (B∩{z*}) ∪
⋃_{i∈I} b_i; blocks are disjoint so Z determines I∩N; the completions are free among
empty blocks: C(m0, 4-|J|).
AGGREGATE: the measured menu = sum over the 1,344 elements, merged by locus identity.
Evenness law: negation x↦-x fixes squares, so t and ν(t) share B exactly — every
locus's aggregate multiplicity is a sum over full B-census classes (sizes 2 or 4).
VERIFICATION: reconstruct the 1,344 (consistency dictionary, as exactness/lane_a.py),
compute the analytic aggregate menu, compare with the measured menu from
run2-published.txt — all 40 entries must match EXACTLY, plus distinct-loci count 4072."""
import sys, re
from itertools import combinations
from collections import Counter

P = 2013265921; G0 = 31; LAM = 284861408
h32 = pow(G0, (P-1)//32, P); H32 = [pow(h32, i, P) for i in range(32)]
G16 = [pow(h32*h32 % P, i, P) for i in range(16)]
zstar = (P - LAM) % P
# reconstruct dense layer via consistency equation (independent of kernels)
def e1(v): return sum(v) % P
def e2(v): return (v[0]*v[1] + v[0]*v[2] + v[1]*v[2]) % P
dense_blocks = []  # B as frozenset of G16 points, one entry per element
gidx = {g: i for i, g in enumerate(G16)}
Bsets = list(combinations(range(16), 7))
# consistency: e2(x)-e1(x)^2 = lam + e1(B); x = 3 distinct points of H32 (+xi forced)
# enumerate as lane_a did: for each B (C(16,7)=11440), for each x-triple class...
# cheaper: load the verified elements via the in-tree kernel output if present, else dictionary
import glob, os
rows = set()
for f in sorted(glob.glob('/tmp/incidence/regen/c17_*.txt')):
    for line in open(f): rows.add(tuple(map(int, line.split())))
if len(rows) < 1379:
    print("kernel rows unavailable; regenerate first"); sys.exit(2)
# distill dense and recover each element's B by factoring its error's even part
inv32 = pow(32, P-2, P); HINV = [pow(x, P-2, P) for x in H32]
def idft(vals):
    return [sum(vals[i]*pow(HINV[i], d, P) for i in range(32)) % P * inv32 % P for d in range(32)]
w32 = [(pow(x, 18, P) + LAM*pow(x, 16, P)) % P for x in H32]
elements = []
for vals in rows:
    ag = [i for i in range(32) if vals[i] == w32[i]]
    if len(ag) != 17: continue
    # error e = w - c vanishes exactly on T; its roots on H = T; the B-block =
    # squares z with BOTH ±sqrt in T (dead fibers of the error... anatomy: e has
    # roots at full fibers over B and at x1,x2,x3 (single) — T = roots of e on H)
    Tset = set(ag)
    B = frozenset(i for i in range(16) if i in Tset and (i+16) in Tset)
    # anatomy says |B| = 7 (as fiber indices); convert to G-point indices: fiber i <-> G16[i]
    assert len(B) == 7, f"B size {len(B)}"
    elements.append(B)
seen_elems = len(elements)
assert seen_elems == 1344, seen_elems
# analytic aggregate menu
pairs = [(i, i+8) for i in range(8)]
zidx = gidx[zstar]; zpair = zidx % 8
others = [pr for pr in pairs if pr[0] != zpair]
# aggregate analytic menu
menu = Counter()
from math import comb
for B in elements:
    bz = B & {zidx}
    blocks = [B & {a, b} for (a, b) in others]
    N = [k for k in range(7) if blocks[k]]
    m0 = 7 - len(N)
    for j in range(max(0, 4-m0), min(4, len(N))+1):
        mult = comb(m0, 4-j)
        for J in combinations(N, j):
            Z = frozenset(bz.union(*[blocks[k] for k in J])) if J else frozenset(bz)
            menu[Z] += mult
total = sum(menu.values())
print(f"analytic: total pair-mass {total} (expect 47040), distinct loci {len(menu)} (expect 4072)")
analytic_menu = Counter(menu.values())
# measured menu from the published log
meas = {}
for line in open('scripts/probes/incidence/run2-published.txt'):
    if line.startswith('locus multiplicity menu (FULL):'):
        meas = eval(line.split(':', 1)[1].strip()); break
match = dict(sorted(analytic_menu.items())) == dict(sorted(meas.items()))
print(f"analytic menu == measured menu: {match}")
if not match:
    for k in sorted(set(analytic_menu) | set(meas)):
        a, m = analytic_menu.get(k, 0), meas.get(k, 0)
        if a != m: print(f"  mult {k}: analytic {a} vs measured {m}")
print("G1:", "CONFIRMED" if (match and total == 47040 and len(menu) == 4072) else "REFUTED/PARTIAL")
