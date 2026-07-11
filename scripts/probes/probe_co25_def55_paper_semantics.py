#!/usr/bin/env python3
"""Falsify-first probe for issues #316/#314: CO25 Definition 5.5 dedup semantics.

Question: does the PAPER semantics of redundant entries (CO25 ePrint 2025/536,
Def. 5.5: a permutation entry is certified redundant by a prior *opposite-direction*
entry) make Lemma 5.16 (no out-of-order backtrack chains off E) and Lemma 5.14
(no forked backtrack families off E) hold on small traces, while the IN-TREE
deviated semantics (BadEvents.lean `redundantEntryDS`: *same-direction swapped*
certificates) has the known machine-checked countermodel (Lemma516TimePFalse.lean)?

Setup mirrors the Lean development with r = 1, c = 1 (SpongeSize N=2, R=1):
  state  = (rate, cap) pair of units; capacitySegment = cap = state[1].
  entry  = ('h', stmt, capUnit)        -- hash query stmt, answer capacity
         | ('p', s_in, s_out)          -- forward perm: query s_in, answer s_out
         | ('q', s_out, s_in)          -- inverse perm: query s_out, answer s_in

Backtrack chains (CO25 Def 5.3, Backtrack.lean BacktrackSequence): a chain ending
at state s is (stmt, [s_in,0..s_in,m], [s_out,0..s_out,m-1]) with
  (a) s_in,m = s
  (b) ('h', stmt, cap(s_in,0)) in tr
  (c) each step pair present in tr as ('p',in,out) or ('q',out,in)
  (d) cap(s_out,i) = cap(s_in,i+1)
  (e) cap(s_in,i) != cap(s_out,i).
J indices (Def 5.4 / BacktrackSequence.Index): j_h = first occurrence of the exact
hash entry; j_i = first occurrence of either orientation of step i's pair; the
terminal pair index is the sentinel len(tr).
E_time_h: j_h > j_0.  E_time_p: exists i with j_i > j_{i+1} (adjacent real steps;
the sentinel can never witness a decrease).  E_fork: exists an admissible family
(maximality: no member subsumed by another via stmt-eq + inputState/outputState
list-subset) with >= 2 chains, i.e. two distinct chains mutually non-subsumed.

E (combined bad event) is evaluated on the DEDUP'd base trace; the dedup keeps the
first occurrence of each certificate-equivalence class (the Lean
removeRedundantEntryDS erases redundant entries until none remain; since the
certificate relation is a symmetric/transitive class relation in both semantics,
the fixpoint is exactly the first-of-class subsequence).
"""

import argparse
import itertools
import sys
import time


def cap(s):
    return s[1]


# --------------------------------------------------------------------------
# Dedup semantics (Definition 5.5)
# --------------------------------------------------------------------------

def cert_intree(prev, e):
    """In-tree redundantEntryDS (BadEvents.lean lines 64-79).

    h:   prior identical hash entry.
    p:   prior identical forward, OR prior *forward* with swapped pair (p, out, in).
    q:   prior identical inverse, OR prior *inverse* with swapped pair (q, in, out).
    """
    k = e[0]
    if k == 'h':
        return prev == e
    if k == 'p':
        return prev == e or (prev[0] == 'p' and prev[1] == e[2] and prev[2] == e[1])
    return prev == e or (prev[0] == 'q' and prev[1] == e[2] and prev[2] == e[1])


def cert_paper(prev, e):
    """Paper CO25 Def 5.5 (eqs 21-23).

    h:   prior identical hash entry.                                   (21)
    p (s_in,s_out): prior identical, OR prior ('q', s_out, s_in)
                    i.e. opposite-direction inverse entry.             (22)
    q (s_out,s_in): prior identical, OR prior ('p', s_in, s_out).      (23)
    """
    k = e[0]
    if k == 'h':
        return prev == e
    if k == 'p':
        return prev == e or (prev[0] == 'q' and prev[1] == e[2] and prev[2] == e[1])
    return prev == e or (prev[0] == 'p' and prev[1] == e[2] and prev[2] == e[1])


def base_trace(tr, cert):
    """Keep first occurrence of each certificate class (= removeRedundantEntryDS fixpoint)."""
    out = []
    for e in tr:
        red = False
        for p in out:
            if cert(p, e):
                red = True
                break
        if not red:
            out.append(e)
    return out


# --------------------------------------------------------------------------
# Combined bad event E on the base trace
# --------------------------------------------------------------------------

def E_lean(b):
    """Mirror of BadEventDS.E (BadEvents.lean) clause-for-clause, incl. its quirks:
    - E_p disjunct 3 uses j' <= j on the inverse ANSWER capacity;
    - E_pinv disjunct 3 uses the inverse QUERY capacity (j' < j) and has NO
      inverse-answer disjunct (disjunct 5 repeats the query side with j' <= j).
    Returns a reason string or None.
    """
    # E_h
    for j, e in enumerate(b):
        if e[0] == 'h':
            c = e[2]
            for jp in range(j):
                f = b[jp]
                if f[0] == 'h' and f[2] == c:
                    return f'E_h@{j}<-h@{jp}'
                if f[0] in 'pq' and (cap(f[1]) == c or cap(f[2]) == c):
                    return f'E_h@{j}<-perm@{jp}'
    # E_p
    for j, e in enumerate(b):
        if e[0] == 'p':
            c = cap(e[2])
            for jp in range(j + 1):
                f = b[jp]
                if jp < j:
                    if f[0] == 'h' and f[2] == c:
                        return f'E_p@{j}d1@{jp}'
                    if f[0] == 'p' and cap(f[2]) == c:
                        return f'E_p@{j}d2@{jp}'
                if f[0] == 'q' and cap(f[2]) == c:
                    return f'E_p@{j}d3@{jp}'
                if f[0] == 'p' and cap(f[1]) == c:
                    return f'E_p@{j}d4@{jp}'
                if f[0] == 'q' and cap(f[1]) == c:
                    return f'E_p@{j}d5@{jp}'
    # E_pinv (Lean quirks preserved)
    for j, e in enumerate(b):
        if e[0] == 'q':
            c = cap(e[2])
            for jp in range(j + 1):
                f = b[jp]
                if jp < j:
                    if f[0] == 'h' and f[2] == c:
                        return f'E_pinv@{j}d1@{jp}'
                    if f[0] == 'p' and cap(f[2]) == c:
                        return f'E_pinv@{j}d2@{jp}'
                    if f[0] == 'q' and cap(f[1]) == c:
                        return f'E_pinv@{j}d3@{jp}'
                if f[0] == 'p' and cap(f[1]) == c:
                    return f'E_pinv@{j}d4@{jp}'
                if f[0] == 'q' and cap(f[1]) == c:
                    return f'E_pinv@{j}d5@{jp}'
    # E_func
    for j, e in enumerate(b):
        if e[0] == 'p':
            sin = e[1]
            for jp in range(j):
                f = b[jp]
                if f[0] == 'p' and f[1] == sin:
                    return f'E_func@{j}p@{jp}'
                if f[0] == 'q' and f[2] == sin:
                    return f'E_func@{j}q@{jp}'
    return None


def E_lean_pinvfixed(b):
    """Lean E with ONLY the E_pinv disjunct-3 quirk repaired (inverse ANSWER capacity,
    j' < j, per the paper), keeping the in-tree shape otherwise. Used to attribute
    counterexamples to the dedup deviation vs. the E_pinv clause deviation."""
    r = E_lean(b)
    if r:
        return r
    for j, e in enumerate(b):
        if e[0] == 'q':
            c = cap(e[2])
            for jp in range(j):
                f = b[jp]
                if f[0] == 'q' and cap(f[2]) == c:
                    return f'E_pinv@{j}d3fix@{jp}'
    return None


def E_paper(b):
    """CO25 Definition 5.7 exactly (eqs 24-27): answer-side matches with j' < j,
    query-side matches with j' <= j, symmetric between E_p and E_pinv."""
    # E_h (all five disjuncts j' < j)
    for j, e in enumerate(b):
        if e[0] == 'h':
            c = e[2]
            for jp in range(j):
                f = b[jp]
                if f[0] == 'h' and f[2] == c:
                    return f'E_h@{j}<-h@{jp}'
                if f[0] in 'pq' and (cap(f[1]) == c or cap(f[2]) == c):
                    return f'E_h@{j}<-perm@{jp}'
    # E_p and E_pinv (anchor on answer capacity)
    for j, e in enumerate(b):
        if e[0] in 'pq':
            tag = 'E_p' if e[0] == 'p' else 'E_pinv'
            c = cap(e[2])  # answer-side capacity
            for jp in range(j + 1):
                f = b[jp]
                if jp < j:
                    if f[0] == 'h' and f[2] == c:
                        return f'{tag}@{j}d1@{jp}'
                    if f[0] == 'p' and cap(f[2]) == c:
                        return f'{tag}@{j}d2@{jp}'
                    if f[0] == 'q' and cap(f[2]) == c:
                        return f'{tag}@{j}d3@{jp}'
                if f[0] == 'p' and cap(f[1]) == c:
                    return f'{tag}@{j}d4@{jp}'
                if f[0] == 'q' and cap(f[1]) == c:
                    return f'{tag}@{j}d5@{jp}'
    # E_func
    for j, e in enumerate(b):
        if e[0] == 'p':
            sin = e[1]
            for jp in range(j):
                f = b[jp]
                if f[0] == 'p' and f[1] == sin:
                    return f'E_func@{j}p@{jp}'
                if f[0] == 'q' and f[2] == sin:
                    return f'E_func@{j}q@{jp}'
    return None


# --------------------------------------------------------------------------
# Backtrack chains, E_time, E_fork (over the RAW trace)
# --------------------------------------------------------------------------

def parse_trace(tr):
    """Returns (H, hidx, pairs):
    H     : cap -> set of stmts with a hash anchor ('h', stmt, cap) in tr
    hidx  : (stmt, cap) -> first occurrence index of that exact hash entry
    pairs : list of (s_in, s_out, first_idx) functional perm pairs with
            cap(s_in) != cap(s_out) (Def 5.3 condition (e));
            first_idx = first occurrence of EITHER orientation
            (mirrors firstOccurrenceOfEither)."""
    H = {}
    hidx = {}
    pidx = {}
    for i, e in enumerate(tr):
        k = e[0]
        if k == 'h':
            H.setdefault(e[2], set()).add(e[1])
            hidx.setdefault((e[1], e[2]), i)
        elif k == 'p':
            pidx.setdefault((e[1], e[2]), i)
        else:  # 'q': query s_out = e[1], answer s_in = e[2]; pair is (s_in, s_out)
            pidx.setdefault((e[2], e[1]), i)
    pairs = [(a, b, i) for (a, b), i in pidx.items() if a[1] != b[1]]
    return H, hidx, pairs


def reach_caps(H, pairs):
    """Capacities reachable forward from some hash anchor along chain links."""
    reach = set(H.keys())
    changed = True
    while changed:
        changed = False
        for a, b, _ in pairs:
            if a[1] in reach and b[1] not in reach:
                reach.add(b[1])
                changed = True
    return reach


def etime_fires_any_state(H, hidx, pairs):
    """E_time fires for SOME end state s (exact, unbounded chain length).

    Since end states range over all of U^2, every capacity is the capacity of some
    state, so 'ends at s' is no constraint beyond reachability:
    - E_time_h: a pair p anchored directly by hash ('h',x,cap(in_p)) whose exact
      hash entry first occurs AFTER first_idx(p): chain [p] has j_h > j_0.
    - E_time_p: a backward-anchored pair p and a linked successor p' with
      first_idx(p) > first_idx(p'): chain prefix..p,p' has adjacent decrease.
    Returns a tag or None."""
    for a, b, i in pairs:
        for x in H.get(a[1], ()):
            if hidx[(x, a[1])] > i:
                return ('E_time_h', (a, b, i), (x, hidx[(x, a[1])]))
    reach = reach_caps(H, pairs)
    for a, b, i in pairs:
        if a[1] in reach:
            for a2, b2, i2 in pairs:
                if a2[1] == b[1] and i > i2:
                    return ('E_time_p', (a, b, i), (a2, b2, i2))
    return None


def etime_fires_at_state(H, hidx, pairs, s):
    """Per-state variant (used for the step-1 countermodel at the exact sT)."""
    # forward closure on caps
    def fwd_closure(c0):
        seen = {c0}
        changed = True
        while changed:
            changed = False
            for a, b, _ in pairs:
                if a[1] in seen and b[1] not in seen:
                    seen.add(b[1])
                    changed = True
        return seen

    cs = cap(s)
    for a, b, i in pairs:
        for x in H.get(a[1], ()):
            if hidx[(x, a[1])] > i and cs in fwd_closure(b[1]):
                return 'E_time_h'
    reach = reach_caps(H, pairs)
    for a, b, i in pairs:
        if a[1] in reach:
            for a2, b2, i2 in pairs:
                if a2[1] == b[1] and i > i2 and cs in fwd_closure(b2[1]):
                    return 'E_time_p'
    return None


def fork_check(tr, H, pairs, U, maxchains=20000):
    """E_fork fires for SOME end state s: two distinct chains ending at the same s,
    mutually non-subsumed under (stmt eq + inputState subset + outputState subset).
    Chains enumerated up to length len(tr)+3 (bounded; 'overflow' if the cap is hit)."""
    maxlen = len(tr) + 3
    endcap = {}
    cnt = 0
    for c0, stmts in H.items():
        for x in stmts:
            endcap.setdefault(c0, []).append((x, ()))
            cnt += 1
    for c0, stmts in H.items():
        stack = [(c0, ())]
        while stack:
            cur, steps = stack.pop()
            if len(steps) >= maxlen:
                continue
            for a, b, _ in pairs:
                if a[1] == cur:
                    ns = steps + ((a, b),)
                    for x in stmts:
                        endcap.setdefault(b[1], []).append((x, ns))
                        cnt += 1
                        if cnt > maxchains:
                            return 'overflow'
                    stack.append((b[1], ns))
    for ce, lst in endcap.items():
        if len(lst) < 2:
            continue
        for r in U:
            s = (r, ce)
            full = []
            for x, steps in lst:
                ins = tuple(p[0] for p in steps) + (s,)
                outs = tuple(p[1] for p in steps)
                full.append((x, ins, outs, frozenset(ins), frozenset(outs)))
            n = len(full)
            for ii in range(n):
                xi, insi, outsi, fii, foi = full[ii]
                for jj in range(ii + 1, n):
                    xj, insj, outsj, fij, foj = full[jj]
                    if xi == xj and insi == insj and outsi == outsj:
                        continue  # same BacktrackSequence
                    sub_ij = xi == xj and fii <= fij and foi <= foj
                    sub_ji = xi == xj and fij <= fii and foj <= foi
                    if not sub_ij and not sub_ji:
                        return True
    return False


# --------------------------------------------------------------------------
# Step 1: the Lemma516TimePFalse countermodel, both semantics
# --------------------------------------------------------------------------

def step1():
    print('=' * 72)
    print('STEP 1 — Lemma516TimePFalse countermodel (U=UInt8 values, r=1, c=1)')
    print('=' * 72)
    sB = (1, 1)
    sA = (0, 2)
    sa = (2, 1)
    sb = (0, 3)
    sT = (1, 3)
    trc = [('h', 0, 1), ('p', sa, sb), ('p', sB, sA), ('p', sA, sB)]
    Uvals = (0, 1, 2, 3)
    ok = True

    # ---- IN-TREE semantics ----
    b_in = base_trace(trc, cert_intree)
    expected = [('h', 0, 1), ('p', sa, sb), ('p', sB, sA)]
    print(f'in-tree base trace : {b_in}')
    if b_in != expected:
        print('  MISMATCH: expected', expected)
        ok = False
    e_in = E_lean(b_in)
    print(f'in-tree E          : {"FIRES " + e_in if e_in else "does NOT fire"}'
          f'  (Lean proves: does NOT fire)')
    if e_in is not None:
        ok = False
    H, hidx, pairs = parse_trace(trc)
    et = etime_fires_at_state(H, hidx, pairs, sT)
    print(f'E_time at sT={sT}   : {"FIRES " + str(et) if et else "does NOT fire"}'
          f'  (Lean proves: E_time_p FIRES)')
    if et != 'E_time_p':
        ok = False
    verdict_intree = (e_in is None) and (et == 'E_time_p')
    print(f'-> IN-TREE verdict : countermodel reproduced = {verdict_intree}')

    # ---- PAPER semantics ----
    b_pap = base_trace(trc, cert_paper)
    print(f'paper base trace   : {b_pap}')
    kept4 = (b_pap == trc)
    print(f'4th entry kept     : {kept4}  (paper Def 5.5: (p,sA,sB) only redundant '
          f'given prior (p^-1,sB,sA), absent)')
    if not kept4:
        ok = False
    e_pap = E_paper(b_pap)
    print(f'paper E            : {"FIRES " + e_pap if e_pap else "does NOT fire"}'
          f'  (expected: FIRES)')
    if e_pap is None:
        ok = False
    verdict_paper = kept4 and (e_pap is not None)
    print(f'-> PAPER verdict   : 4th entry survives and E fires = {verdict_paper}')

    # ---- Step 1b: same countermodel translated into U={0,1,2} (caps 0,1,2) ----
    print('-' * 72)
    print('STEP 1b — countermodel translated to U={0,1,2} (in enumeration reach at len 4)')
    tB = (0, 0)
    tA = (0, 1)
    ta = (1, 0)
    tb = (0, 2)
    tT = (0, 2)
    trc3 = [('h', 0, 0), ('p', ta, tb), ('p', tB, tA), ('p', tA, tB)]
    b3_in = base_trace(trc3, cert_intree)
    e3_in = E_lean(b3_in)
    H3, hidx3, pairs3 = parse_trace(trc3)
    et3 = etime_fires_at_state(H3, hidx3, pairs3, tT)
    b3_pap = base_trace(trc3, cert_paper)
    e3_pap = E_paper(b3_pap)
    print(f'  in-tree: base={b3_in}')
    print(f'  in-tree: E={"FIRES " + e3_in if e3_in else "no"};  E_time@{tT}={et3}')
    print(f'  paper  : base keeps 4th entry={b3_pap == trc3}; '
          f'E={"FIRES " + e3_pap if e3_pap else "no"}')
    cm3_intree = (e3_in is None) and (et3 == 'E_time_p')
    cm3_paper = (b3_pap == trc3) and (e3_pap is not None)
    print(f'  -> in-tree countermodel also lives in U=3 space: {cm3_intree}; '
          f'paper repairs it: {cm3_paper}')

    return ok, verdict_intree, verdict_paper


# --------------------------------------------------------------------------
# Step 2: exhaustive enumeration
# --------------------------------------------------------------------------

def entry_universe(U, stmts):
    states = [(r, c) for r in U for c in U]
    ents = [('h', x, c) for x in stmts for c in U]
    ents += [('p', a, b) for a in states for b in states]
    ents += [('q', a, b) for a in states for b in states]
    return ents


def enumerate_run(U, stmts, lengths, report_limit=6):
    ents = entry_universe(U, stmts)
    stats = {
        'total': 0, 'with_h': 0, 'etime': 0, 'efork': 0, 'fork_overflow': 0,
        'cex_paper': 0, 'cex_intree': 0, 'cex_intree_pinvfixed': 0,
        'cex_intree_fork': 0,
    }
    cex_paper = []
    cex_intree = []
    t0 = time.time()
    for L in lengths:
        for tr in itertools.product(ents, repeat=L):
            stats['total'] += 1
            if not any(e[0] == 'h' for e in tr):
                continue  # no hash anchor -> no chain -> no E_time/E_fork
            stats['with_h'] += 1
            trl = list(tr)
            H, hidx, pairs = parse_trace(trl)
            event = None
            et = etime_fires_any_state(H, hidx, pairs)
            if et:
                stats['etime'] += 1
                event = et[0]
            else:
                fk = fork_check(trl, H, pairs, U)
                if fk == 'overflow':
                    stats['fork_overflow'] += 1
                    event = 'E_fork(overflow)'
                elif fk:
                    stats['efork'] += 1
                    event = 'E_fork'
            if event is None:
                continue
            # paper semantics
            b_pap = base_trace(trl, cert_paper)
            if E_paper(b_pap) is None:
                stats['cex_paper'] += 1
                if len(cex_paper) < report_limit:
                    cex_paper.append((trl, event, b_pap))
            # in-tree semantics
            b_in = base_trace(trl, cert_intree)
            if E_lean(b_in) is None:
                stats['cex_intree'] += 1
                # attribution: does the E_pinv disjunct-3 repair alone cure it?
                if E_lean_pinvfixed(b_in) is None:
                    stats['cex_intree_pinvfixed'] += 1
                # full event tags for this rare CEX trace (E_fork may also fire)
                tags = [event]
                if et and fork_check(trl, H, pairs, U) is True:
                    tags.append('E_fork')
                    stats['cex_intree_fork'] += 1
                if len(cex_intree) < report_limit:
                    cex_intree.append((trl, '+'.join(tags), b_in))
    stats['secs'] = time.time() - t0
    return stats, cex_paper, cex_intree


def show_run(name, stats, cex_paper, cex_intree):
    print('-' * 72)
    print(f'RUN {name}: traces={stats["total"]}  with_hash={stats["with_h"]}  '
          f'E_time_fires={stats["etime"]}  E_fork_fires={stats["efork"]}  '
          f'fork_overflow={stats["fork_overflow"]}  [{stats["secs"]:.1f}s]')
    print(f'  PAPER-semantics counterexamples : {stats["cex_paper"]}')
    print(f'  IN-TREE-semantics counterexamples: {stats["cex_intree"]}'
          f'  (of which E_fork also fires: {stats["cex_intree_fork"]};'
          f' surviving the E_pinv-d3-only repair: {stats["cex_intree_pinvfixed"]})')
    for tag, lst in (('PAPER', cex_paper), ('IN-TREE', cex_intree)):
        for trl, event, b in lst:
            print(f'  {tag} CEX [{event}]: trace={trl}')
            print(f'      base={b}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--len5', action='store_true',
                    help='also run U={0,1}, stmts={0}, length 5 (slow, ~45M traces)')
    ap.add_argument('--skip-enum', action='store_true')
    args = ap.parse_args()

    ok, v_in, v_pap = step1()
    if not ok:
        print('\nSTEP 1 FAILED — mirror does not reproduce the Lean facts; aborting.')
        sys.exit(1)
    print('\nSTEP 1 PASSED: mirror reproduces the Lean countermodel facts.\n')

    if args.skip_enum:
        return

    print('=' * 72)
    print('STEP 2 — exhaustive enumeration (falsify-first, paper semantics)')
    print('=' * 72)
    runs = []
    s, cp, ci = enumerate_run(U=(0, 1), stmts=(0, 1), lengths=(1, 2, 3, 4))
    show_run('A: U={0,1}, stmts={0,1}, len 1-4', s, cp, ci)
    runs.append(('A', s))
    s, cp, ci = enumerate_run(U=(0, 1, 2), stmts=(0,), lengths=(1, 2, 3))
    show_run('B: U={0,1,2}, stmts={0}, len 1-3', s, cp, ci)
    runs.append(('B', s))
    if args.len5:
        s, cp, ci = enumerate_run(U=(0, 1), stmts=(0,), lengths=(5,))
        show_run('C: U={0,1}, stmts={0}, len 5', s, cp, ci)
        runs.append(('C', s))

    print('=' * 72)
    print('SUMMARY')
    print('=' * 72)
    tot = sum(s['total'] for _, s in runs)
    cexp = sum(s['cex_paper'] for _, s in runs)
    cexi = sum(s['cex_intree'] for _, s in runs)
    ovf = sum(s['fork_overflow'] for _, s in runs)
    print(f'step1 in-tree countermodel reproduced: {v_in}')
    print(f'step1 paper semantics repairs it     : {v_pap}')
    print(f'traces enumerated                    : {tot}')
    print(f'paper-semantics counterexamples      : {cexp} (expected 0)')
    print(f'in-tree-semantics counterexamples    : {cexi}')
    print(f'unresolved fork overflows            : {ovf}')


if __name__ == '__main__':
    main()
