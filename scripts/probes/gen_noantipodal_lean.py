#!/usr/bin/env python3
"""#357 converse increment 3: GENERATE the no-antipodal branch Lean file.

Walks the canonical-matching tree exactly as the Lean proof will (partner of the
smallest unmatched index, fin_cases over the 12 candidates), computes a kill
certificate or a survivor conclusion at every node from exact integer linear algebra
over (a1,b1,a2,b2,a3,b3,h), and emits the complete Lean proof of

  secondLayer_of_no_antipodal : generic balanced multiplicity-free Distinct6 triple
  with NO antipodal pair satisfies one of the eight second-layer seed systems.

The emitted file mirrors ChordConverseCore.lean's verified syntax patterns.
"""
import sys
from itertools import product

# ---- the stack model over Z^7: coords (a1,b1,a2,b2,a3,b3,h) ----
EXPVEC = [
    (0,0,1,0,1,1), (0,0,0,1,1,1),
    (1,1,1,0,0,0), (1,1,0,1,0,0),
    (1,0,0,0,1,1), (0,1,0,0,1,1),
    (0,0,1,1,1,0), (0,0,1,1,0,1),
    (1,0,1,1,0,0), (0,1,1,1,0,0),
    (1,1,0,0,1,0), (1,1,0,0,0,1),
]
SHIFT = [0,0,1,1,1,1,1,1,0,0,0,0]
def esv(i):
    return tuple(list(EXPVEC[i]) + [SHIFT[i]])
LNAME = ['A₁','B₁','A₂','B₂','A₃','B₃']
HYPD6 = {}  # (i,j) -> hypothesis name, oriented i<j as "X_i ≠ X_j"
D6N = [None]*6
PAIRS6 = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(0,4),(0,5),(1,4),(1,5),
          (2,4),(2,5),(3,4),(3,5),(4,5)]
def d6name(i,j):
    nm = {0:'A1',1:'B1',2:'A2',3:'B2',4:'A3',5:'B3'}
    return f"h{nm[i]}{nm[j]}"

def vsub(u,v): return tuple(x-y for x,y in zip(u,v))
def vadd(u,v): return tuple(x+y for x,y in zip(u,v))
def vneg(u): return tuple(-x for x in u)
def smul(c,u): return tuple(c*x for x in u)
ZERO7 = tuple([0]*7)
def unit7(i): return tuple(1 if k==i else 0 for k in range(7))
EH = unit7(6)

# hypothesis diff for path pair (x, v): hp : ES v = ES x + h  => diff = esv(v) - esv(x) - eh
def hypdiff(x, v):
    return vsub(vsub(esv(v), esv(x)), EH)

# ---- targets ----
# returns (golstring, killline-template kind, payload)
TARGETS = []
for (i,j) in PAIRS6:
    # goal X_i = X_j ; hyp name d6name(i,j) : X_i ≠ X_j
    TARGETS.append(('D6', (i,j), vsub(unit7(i), unit7(j))))
for (i,j) in [(0,1),(0,2),(1,2)]:
    # goal S_{i+1} = S_{j+1}: A_i+B_i = A_j+B_j
    sv_i = vadd(unit7(2*i), unit7(2*i+1)); sv_j = vadd(unit7(2*j), unit7(2*j+1))
    TARGETS.append(('GEN', (i,j), vsub(sv_i, sv_j)))
for i in range(3):
    # goal B_i = A_i + h
    TARGETS.append(('ANTIP', i, vsub(vsub(unit7(2*i+1), unit7(2*i)), EH)))
MULTT = []
for i in range(12):
    for j in range(12):
        if i != j:
            MULTT.append(('MULT', (i,j), vsub(esv(i), esv(j))))

def solve(rows, target, maxc=2):
    """find integer lambda over rows and integer c with sum l*row + c*(2eh) = target;
    returns (lams, c) or None."""
    k = len(rows)
    rng = range(-maxc, maxc+1)
    half = k//2
    first = {}
    for lam1 in product(rng, repeat=half):
        v = ZERO7
        for i,l in enumerate(lam1):
            if l: v = vadd(v, smul(l, rows[i]))
        first.setdefault(v, lam1)
    for lam2 in product(rng, repeat=k-half):
        v2 = ZERO7
        for i,l in enumerate(lam2):
            if l: v2 = vadd(v2, smul(l, rows[half+i]))
        need = vsub(target, v2)
        # c absorbs only the h-coordinate, in even steps
        body = need[:6]
        for v1, lam1 in first.items():
            if v1[:6] != body: continue
            dh = need[6] - v1[6]
            if dh % 2 == 0:
                return (lam1 + lam2, dh//2)
    return None

def lc_expr(names, lams, c):
    terms = []
    for nm, l in zip(names, lams):
        if l == 0: continue
        if l == 1: terms.append(f"+ {nm}")
        elif l == -1: terms.append(f"- {nm}")
        elif l > 0: terms.append(f"+ {l} * {nm}")
        else: terms.append(f"- {-l} * {nm}")
    if c:
        if c == 1: terms.append("+ hh2")
        elif c == -1: terms.append("- hh2")
        elif c > 0: terms.append(f"+ {c} * hh2")
        else: terms.append(f"- {-c} * hh2")
    s = ' '.join(terms)
    if s.startswith('+ '): s = s[2:]
    elif s.startswith('- '): s = '-' + s[2:]
    return s if s else "(0 : R) = 0"  # should not happen

def goal_str(kind, payload):
    if kind == 'D6':
        i,j = payload
        return f"{LNAME[i]} = {LNAME[j]}"
    if kind == 'GEN':
        i,j = payload
        return f"{LNAME[2*i]} + {LNAME[2*i+1]} = {LNAME[2*j]} + {LNAME[2*j+1]}"
    if kind == 'ANTIP':
        i = payload
        return f"{LNAME[2*i+1]} = {LNAME[2*i]} + h"
    raise ValueError

def hypname(kind, payload):
    if kind == 'D6':
        i,j = payload
        return d6name(i,j)
    if kind == 'GEN':
        i,j = payload
        return f"hg{i+1}{j+1}"
    if kind == 'ANTIP':
        return f"hna{payload+1}"
    raise ValueError

def find_kill(rows, names, mset, allow_branch=True):
    """returns emission lines (list of str, unindented) or None"""
    for kind, payload, tv in TARGETS:
        sol = solve(rows, tv)
        if sol:
            lams, c = sol
            g = goal_str(kind, payload)
            return [f"exact absurd (by linear_combination {lc_expr(names, lams, c)} : "
                    f"{g}) {hypname(kind, payload)}"]
        sol = solve(rows, vneg(tv))
        if sol and kind != 'ANTIP':
            lams, c = sol
            # negated: goal X_j = X_i etc; use .symm on the derived eq
            if kind == 'D6':
                i,j = payload
                g = f"{LNAME[j]} = {LNAME[i]}"
            else:
                i,j = payload
                g = f"{LNAME[2*j]} + {LNAME[2*j+1]} = {LNAME[2*i]} + {LNAME[2*i+1]}"
            return [f"exact absurd (by linear_combination {lc_expr(names, lams, c)} : "
                    f"{g}).symm {hypname(kind, payload)}"]
    for kind, (i,j), tv in MULTT:
        if frozenset((i,j)) in mset: continue
        sol = solve(rows, tv)
        if sol:
            lams, c = sol
            return [f"refine absurd (hinj (a₁ := {i}) (a₂ := {j}) ?_) (by decide)",
                    f"simp only [chordStack]; linear_combination {lc_expr(names, lams, c)}"]
    if allow_branch:
        for i in range(6):
            for j in range(i+1, 6):
                tv2 = smul(2, vsub(unit7(i), unit7(j)))
                sol = solve(rows, tv2)
                if sol is None: continue
                lams, c = sol
                # arm 0: X_i = X_j → D6 kill; arm h: extra row X_i − X_j − h
                extra = vsub(vsub(unit7(i), unit7(j)), EH)
                sub = find_kill(rows + [extra], names + ['hh'], mset,
                                allow_branch=False)
                if sub is None: continue
                X, Y = LNAME[i], LNAME[j]
                lines = [f"have hd : ({X} - {Y}) + ({X} - {Y}) = 0 := by "
                         f"linear_combination {lc_expr(names, lams, c)}",
                         "rcases hker _ hd with h0 | hh",
                         f"· exact absurd (by linear_combination h0 : {X} = {Y}) "
                         f"{d6name(i,j)}"]
                lines.append("· " + sub[0])
                for extra_line in sub[1:]:
                    lines.append("  " + extra_line)
                return lines
    return None

# the eight second-layer systems: per survivor matching, the 3 reduced congruences
# stated as goals "LHS = RHS + h" derived from path rows. We store them as target
# vectors with a printable form.
SYSTEMS = [
    # (label, [(goalstr, targetvec)*3])
    [("B₂ + B₃ = A₁ + B₁ + h", None), ("A₃ + B₃ = A₁ + B₂ + h", None),
     ("A₂ + B₂ = A₁ + B₃ + h", None)],
    [("B₂ + A₃ = A₁ + B₁ + h", None), ("A₃ + B₃ = A₁ + B₂ + h", None),
     ("A₂ + B₂ = A₁ + A₃ + h", None)],
    [("B₂ + B₃ = A₁ + B₁ + h", None), ("A₃ + B₃ = B₁ + B₂ + h", None),
     ("A₂ + B₂ = B₁ + B₃ + h", None)],
    [("B₂ + A₃ = A₁ + B₁ + h", None), ("A₃ + B₃ = B₁ + B₂ + h", None),
     ("A₂ + B₂ = B₁ + A₃ + h", None)],
    [("A₂ + B₃ = A₁ + B₁ + h", None), ("A₃ + B₃ = A₁ + A₂ + h", None),
     ("A₂ + B₂ = A₁ + B₃ + h", None)],
    [("A₂ + B₃ = A₁ + B₁ + h", None), ("A₃ + B₃ = B₁ + A₂ + h", None),
     ("A₂ + B₂ = B₁ + B₃ + h", None)],
    [("A₂ + A₃ = A₁ + B₁ + h", None), ("A₃ + B₃ = A₁ + A₂ + h", None),
     ("A₂ + B₂ = A₁ + A₃ + h", None)],
    [("A₂ + A₃ = A₁ + B₁ + h", None), ("A₃ + B₃ = B₁ + A₂ + h", None),
     ("A₂ + B₂ = B₁ + A₃ + h", None)],
]
NM2IDX = {'A₁':0,'B₁':1,'A₂':2,'B₂':3,'A₃':4,'B₃':5}
def parse_goal(g):
    lhs, rhs = g.split(' = ')
    v = ZERO7
    for t in lhs.split(' + '):
        v = vadd(v, unit7(NM2IDX[t]))
    for t in rhs.split(' + '):
        if t == 'h': v = vsub(v, EH)
        else: v = vsub(v, unit7(NM2IDX[t]))
    return v
for sysrows in SYSTEMS:
    for k in range(3):
        g, _ = sysrows[k]
        sysrows[k] = (g, parse_goal(g))

def try_conclude(rows, names):
    for sidx, sysrows in enumerate(SYSTEMS):
        sols = []
        for g, tv in sysrows:
            sol = solve(rows, tv)
            if sol is None: break
            sols.append((g, sol))
        if len(sols) == 3:
            lines = []
            for k, (g, (lams, c)) in enumerate(sols):
                lines.append(f"have s{k+1} : {g} := by "
                             f"linear_combination {lc_expr(names, lams, c)}")
            core = "⟨s1, s2, s3⟩" if sidx == 7 else "Or.inl ⟨s1, s2, s3⟩"
            expr = core
            for _ in range(sidx):
                expr = f"Or.inr ({expr})"
            lines.append(f"exact {expr}")
            return lines
    return None

stats = {'kills':0, 'concl':0, 'nodes':0}

def emit_node(path, matched, depth, indent):
    """path: list of (x, v, hypname); matched: set of indices; returns lines."""
    stats['nodes'] += 1
    x = min(set(range(12)) - matched)
    d = depth
    pad = ' ' * indent
    lines = [f"{pad}obtain ⟨y{d}, hp{d}⟩ := hclosed {x}",
             f"{pad}fin_cases y{d} <;> simp only [chordStack] at hp{d}"]
    rows = [hypdiff(px, pv) for (px, pv, _) in path]
    names = [nm for (_, _, nm) in path]
    for v in range(12):
        if v == x:
            # ES x = ES x + h → h = 0
            sol = solve(rows + [hypdiff(x, v)], EH)
            assert sol is not None
            lams, c = sol
            lines.append(f"{pad}· exact absurd (by linear_combination "
                         f"{lc_expr(names + [f'hp{d}'], lams, c)} : h = (0 : R)) hh0")
            continue
        rows2 = rows + [hypdiff(x, v)]
        names2 = names + [f"hp{d}"]
        mset = {frozenset((px, pv)) for (px, pv, _) in path} | {frozenset((x, v))}
        kill = find_kill(rows2, names2, mset)
        if kill is not None:
            stats['kills'] += 1
            lines.append(f"{pad}· " + kill[0])
            for el in kill[1:]:
                lines.append(f"{pad}  " + el)
            continue
        concl = try_conclude(rows2, names2)
        if concl is not None:
            stats['concl'] += 1
            lines.append(f"{pad}· " + concl[0])
            for el in concl[1:]:
                lines.append(f"{pad}  " + el)
            continue
        # recurse
        sub = emit_node(path + [(x, v, f"hp{d}")], matched | {x, v}, depth + 1,
                        indent + 2)
        lines.append(f"{pad}· -- continue: partner of {x} is {v}")
        lines.extend(sub)
    return lines

HEADER = '''/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ChordConverseCore

/-!
# The second-layer converse: the no-antipodal branch of the wide-circuit classification

Campaign #357, exactness-converse lane, increment 3. Companion to
`ChordConverseCore.lean`: in the generic branch with **no** antipodal pair, the
canonical matching of a balanced multiplicity-free `Distinct6` stack is forced into one
of the **eight second-layer seed systems** — the supply systems of
`SecondLayerSeedFamily.lean` (shapes I/II and their orientation images).

The proof is the canonical-matching case tree, **machine-generated** from the exact
certificate data of `probe_noantipodal_branch_tree.py` (10395 pairings, 10387 killed,
8 survivors) by `gen_noantipodal_lean.py`, in the verified syntax patterns of
`ChordConverseCore.lean`. Every kill is one `linear_combination` onto a
`Distinct6`/genericity/no-antipodal/injectivity hypothesis (with doubling-kernel
branches), and each surviving branch concludes as soon as its three system congruences
are derivable.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option linter.style.longFile 1700

namespace ArkLib.ProximityGap.SecondLayerConverseCore

open ArkLib.ProximityGap.ChordConverseCore

variable {R : Type*} [CommRing R]

/-- **The no-antipodal-branch classification.** Over any commutative ring with a
half-period `h`: a `Distinct6` stack with no antipodal pair, pairwise-distinct
products, injective (multiplicity-free) and `+h`-closed (balanced) shifted 12-stack
satisfies one of the eight second-layer seed systems. -/
theorem secondLayer_of_no_antipodal {A₁ B₁ A₂ B₂ A₃ B₃ h : R}
    (hh2 : h + h = 0) (hh0 : h ≠ 0)
    (hker : ∀ u : R, u + u = 0 → u = 0 ∨ u = h)
    (hA1B1 : A₁ ≠ B₁) (hA2B2 : A₂ ≠ B₂) (hA3B3 : A₃ ≠ B₃)
    (hA1A2 : A₁ ≠ A₂) (hA1B2 : A₁ ≠ B₂) (hB1A2 : B₁ ≠ A₂) (hB1B2 : B₁ ≠ B₂)
    (hA1A3 : A₁ ≠ A₃) (hA1B3 : A₁ ≠ B₃) (hB1A3 : B₁ ≠ A₃) (hB1B3 : B₁ ≠ B₃)
    (hA2A3 : A₂ ≠ A₃) (hA2B3 : A₂ ≠ B₃) (hB2A3 : B₂ ≠ A₃) (hB2B3 : B₂ ≠ B₃)
    (hg12 : A₁ + B₁ ≠ A₂ + B₂) (hg13 : A₁ + B₁ ≠ A₃ + B₃)
    (hg23 : A₂ + B₂ ≠ A₃ + B₃)
    (hna1 : B₁ ≠ A₁ + h) (hna2 : B₂ ≠ A₂ + h) (hna3 : B₃ ≠ A₃ + h)
    (hinj : Function.Injective (chordStack A₁ B₁ A₂ B₂ A₃ B₃ h))
    (hclosed : ∀ x : Fin 12, ∃ y : Fin 12,
      chordStack A₁ B₁ A₂ B₂ A₃ B₃ h y = chordStack A₁ B₁ A₂ B₂ A₃ B₃ h x + h) :
    (B₂ + B₃ = A₁ + B₁ + h ∧ A₃ + B₃ = A₁ + B₂ + h ∧ A₂ + B₂ = A₁ + B₃ + h)
    ∨ (B₂ + A₃ = A₁ + B₁ + h ∧ A₃ + B₃ = A₁ + B₂ + h ∧ A₂ + B₂ = A₁ + A₃ + h)
    ∨ (B₂ + B₃ = A₁ + B₁ + h ∧ A₃ + B₃ = B₁ + B₂ + h ∧ A₂ + B₂ = B₁ + B₃ + h)
    ∨ (B₂ + A₃ = A₁ + B₁ + h ∧ A₃ + B₃ = B₁ + B₂ + h ∧ A₂ + B₂ = B₁ + A₃ + h)
    ∨ (A₂ + B₃ = A₁ + B₁ + h ∧ A₃ + B₃ = A₁ + A₂ + h ∧ A₂ + B₂ = A₁ + B₃ + h)
    ∨ (A₂ + B₃ = A₁ + B₁ + h ∧ A₃ + B₃ = B₁ + A₂ + h ∧ A₂ + B₂ = B₁ + B₃ + h)
    ∨ (A₂ + A₃ = A₁ + B₁ + h ∧ A₃ + B₃ = A₁ + A₂ + h ∧ A₂ + B₂ = A₁ + A₃ + h)
    ∨ (A₂ + A₃ = A₁ + B₁ + h ∧ A₃ + B₃ = B₁ + A₂ + h ∧ A₂ + B₂ = B₁ + A₃ + h) := by
'''

FOOTER = '''
/-! ## Source audit -/

#print axioms secondLayer_of_no_antipodal

end ArkLib.ProximityGap.SecondLayerConverseCore
'''

def d6name_fix(i, j):
    return d6name(i, j)

body = emit_node([], set(), 0, 2)
out = HEADER + '\n'.join(body) + '\n' + FOOTER
path_out = 'ArkLib/Data/CodingTheory/ProximityGap/SecondLayerConverseCore.lean'
with open(path_out, 'w', encoding='utf-8', newline='\n') as f:
    f.write(out)
print(f"wrote {path_out}: {len(out.splitlines())} lines; "
      f"nodes={stats['nodes']} kills={stats['kills']} conclusions={stats['concl']}")
