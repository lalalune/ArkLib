#!/usr/bin/env python3
"""Regenerate audit/live-debt-2026-06-10.md from AUDIT_LEDGER.md.

Splits residual-named def/class/structure/abbrev declarations into discharged vs live,
using (a) discharger-suffix siblings, (b) a hand-maintained list of known dischargers whose
names do not follow the suffix convention (verb-form theorems, lowercase twins), and
(c) a hand-maintained exclusion list of mathematical objects that merely have residual-ish
names. Preserves the "Crossed off this campaign" section of the existing file verbatim.

Run scripts/audit_ledger.py first.
"""
import re

SUFFIXES = ('_holds', '_proven', '_proved', '_unconditional', '_wired', '_false',
            '_holds_as_stated', '_trivially_true', '_holds_pointwise', '_holds_proof', '_proof')

# Residual name -> discharging theorem (verified manually; verb-form / nonstandard names).
KNOWN_DISCHARGED = {
    'OuterCompletenessRunFactsResidual': 'outer_completenessRunFactsResidual',
    'D2sQueryStepGSpecBudgetResidual': 'd2sQueryStepGSpecBudget',
    'D2fOuterImplSharedBudgetResidual': 'd2fOuterImplSharedBudget',
    'SimulatedProverChallengeBudgetResidual': 'simulatedProverChallengeBudget',
    'SimulatedProverSharedBudgetResidual': 'simulatedProverSharedBudget',
    'OuterCompletenessResidual': 'outerCompletenessResidual_of_neverFail (NeverFail-standard)',
    'Lemma5_12HonestResidual': 'lemma5_12_honest (Lemma512Honest.lean)',
    'stirCheckingRbrSoundnessResidual':
        'stirCheckingRbrSoundness_genuine (SubUnitRbr.lean, at the genuine stirEpsStar budget)',
    'stirCheckingRepRbrSoundnessResidual':
        'stirCheckingRepRbrSoundness_genuine (RepWire.lean, at the (.)^t stirEpsStarRep budget)',
    'fiatShamir_soundnessTransferResidual':
        'fiatShamir_soundnessTransferResidual_canonical (StateRestorationTransport.lean — '
        'proven at the canonical coupled SR implementation; #116 closure)',
    'fiatShamir_knowledgeSoundnessTransferResidual':
        'fiatShamir_knowledgeSoundnessTransferResidual_canonical (StateRestorationTransport.lean'
        ' — #116 closure)',
    'fiatShamir_statisticalHVZKTransferResidual':
        'fiatShamir_statisticalHVZKTransferResidual_canonical_proved (HVZKCanonicalClose.lean — '
        '#116 closure)',
    'fiatShamir_hvzkTransferResidual':
        'fiatShamir_hvzkTransferResidual_canonical_proved (HVZKKernelClose.lean — #116 closure)',
    'MonicHighYResidual':
        'residualw (FaithfulFrontierWitness.lean — per-bundle interface, witness instance '
        'proven) + general-monic boundary half (882d85173)',
}

# Honest non-proof end-states (documented obstruction / suspected-false / documented-dead).
DOCUMENTED_END_STATE = {
    'appendKnowledgeSoundnessResidual':
        'PROVEN phase-1 oracle-access obstruction documented at def; rbr route live',
    'queryRoundPerfectCompletenessResidual':
        'SUSPECTED FALSE as stated (relation/check mismatch) — documented at def',
    'LogupSoundnessFullResidual': 'documented-DEAD apex (hOuter refuted in typical regime)',
    'LogupSoundnessUncondResidual': 'documented-DEAD apex (hOuter refuted in typical regime)',
    'appendRunRightResidual':
        'documented GENUINELY FALSE at challenge seams; Dist form is the live statement',
    'oracleReductionToReductionResidual':
        'documented LEGACY/superseded: unconditional completeness exists bridge-free '
        '(oracleReduction_perfectCompleteness_unconditional); consumers routed around it',
}

# Mathematical objects, not proof obligations.
FALSE_POSITIVES = {
    'r1csResidualAt', 'r1csResidual', 'mcaConjectureBound', 'johnsonConjectureEta',
    # interface-Prop on data with a canonical rfl witness (batchingConsistencyResidual_sum):
    'BatchingConsistencyResidual',
    # plain structure-to-structure converter (where-def), not an obligation:
    'toAlgebraicData',
}

pat = re.compile(r"- `([^:`]+):(\d+)` (\w+) \*\*([A-Za-z0-9_.']+)\*\*")
entries = []
for line in open('AUDIT_LEDGER.md', encoding='utf-8'):
    m = pat.match(line.strip())
    if m:
        entries.append((m.group(1), int(m.group(2)), m.group(3), m.group(4)))
names = {e[3] for e in entries}
props = [e for e in entries if e[2] in ('def', 'class', 'structure', 'abbrev', 'opaque')]


def discharged(n):
    base = n.split('.')[-1]
    if base in KNOWN_DISCHARGED:
        return [KNOWN_DISCHARGED[base]]
    cands = []
    for b in {base, base[0].lower() + base[1:], base[0].upper() + base[1:]}:
        cands += [b + s for s in SUFFIXES] + ['not_' + b]
    return [c for c in cands if c in names]


old = open('audit/live-debt-2026-06-10.md', encoding='utf-8').read()
crossed = old[old.index('## Crossed off this campaign'):old.index('## Scan false-positives')] \
    if '## Scan false-positives' in old else \
    old[old.index('## Crossed off this campaign'):old.index('## Props WITH')]

closed, openp, docstate, routes = [], [], [], []
for f, l, k, n in sorted(props, key=lambda e: (e[0], e[1])):
    base = n.split('.')[-1]
    if base in FALSE_POSITIVES:
        continue
    d = discharged(n)
    if d:
        closed.append((f, l, k, n, d))
    elif base in DOCUMENTED_END_STATE:
        docstate.append((f, l, k, n, DOCUMENTED_END_STATE[base]))
    elif base.startswith('of') or '_of_' in base or '.of' in n:
        # conditional-constructor supply routes (X.ofInTree, *_of_* …): discharge ROUTES,
        # not debt items (see preamble).
        routes.append((f, l, k, n))
    else:
        openp.append((f, l, k, n))

out = open('audit/live-debt-2026-06-10.md', 'w', encoding='utf-8')
out.write("""# Live residual-debt surface — regenerated by scripts/live_debt.py

Method: every def/class/structure/abbrev residual-named declaration in the regenerated ledger,
split by discharge state. CAVEAT: existence-in-source only — verify axiom-cleanliness
(#print axioms) before trusting any discharger. Conditional-constructor defs (`X.ofInTree`,
`*_of_*` supply routes) are discharge ROUTES, not debt items per se. Research-tier KEEP-OPEN
props (mcaConjecture, UniformPolyListSizeConjecture, epsMCAgsPrizeUniversalConjecture,
mca_johnson_bound_CONJECTURE and the BCIKS20/GKL24/Hab25 families) are NOT closeable — their
honest end-state is conditional consumers + OPEN docs.

""")
out.write(crossed)
out.write('## Scan false-positives (mathematical objects, NOT proof debt — excluded)\n\n')
for n in sorted(FALSE_POSITIVES):
    out.write('- `%s`\n' % n)
out.write('\n## Honest non-proof end-states (documented at the def)\n\n')
for f, l, k, n, why in docstate:
    out.write('- %s `%s` — %s (`%s:%d`)\n' % (k, n, why, f, l))
out.write('\n## Props WITH in-source discharger/refutation (%d)\n\n' % len(closed))
for f, l, k, n, d in closed:
    out.write('- `%s` <- `%s` (`%s:%d`)\n' % (n, d[0], f, l))
out.write('\n## Conditional-constructor supply routes — not debt items (%d)\n\n' % len(routes))
for f, l, k, n in routes:
    out.write('- %s `%s` — `%s:%d`\n' % (k, n, f, l))
out.write('\n## Props WITHOUT discharger — live surface (%d)\n\n' % len(openp))
for f, l, k, n in openp:
    out.write('- %s `%s` — `%s:%d`\n' % (k, n, f, l))
out.close()
print('live:', len(openp), 'discharged:', len(closed), 'documented:', len(docstate))
