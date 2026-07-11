// Adversarial wall-audit workflow for the delta*/proximity-prize reduction (DISPROOF_LOG O186, 2026-06-16).
// Run via: Workflow({scriptPath: "scripts/probes/genlaw/wall_audit_workflow.js"})
// 12 agents each try to BREAK a recent "wall" (declared dead-end); 4 completeness lenses hunt any
// unattempted escape; 1 synthesis agent produces the bulletproof one-conjecture statement + dossier
// updates. Verdict: all 12 walls sound-deadend (conf 0.84-0.92), walled set complete. See the ledger.
export const meta = {
  name: 'deltastar-wall-audit',
  description: 'Adversarially verify every recent delta* wall-claim is a sound dead-end, completeness-critic for unattempted escapes, synthesize the bulletproof one-conjecture statement',
  phases: [
    { title: 'WallAudit', detail: 'one skeptic per wall-claim, tries to break it' },
    { title: 'Completeness', detail: 'diverse lenses hunt any unattempted escape route' },
    { title: 'Synthesize', detail: 'verdict + dossier updates' },
  ],
}
const REPO = '/home/nubs/Git/ArkLib'
const LEDGER = REPO + '/ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md'
const WALLS = [
  { id: 'O173_O182', claim: 'second-moment pair-sum gate = Theta(E^2) not o(E^2) through the upper window at all 4 rates; moment methods blind to KKH26 worst line' },
  { id: 'O174', claim: 'closed-form-free per-line injection into C(n/2,r)*2^r BREAKS for r>=4 (axis-support mismatch)' },
  { id: 'O175', claim: 'C-half #bad<=K/2: calibration exact but reduces-to-open; /2 is a calibration fit, no proof handle' },
  { id: 'O176', claim: 'general-r #bad<=K no closed form (refuted); tightest bound = E_12(mu_n) joint additive energy, absent from literature' },
  { id: 'O177', claim: 'r=4 rung PROVEN; open core anchored to quadratic Vinogradov/PTE (Mansfield-Mudgal); per-fiber lead reduces-to-open' },
  { id: 'O178', claim: 'theta/AFE route PINNED: eta_b/sqrt(n) i.i.d. Gaussian not DAM theta; Poisson transform a length-preserving fixed point not contraction' },
  { id: 'O179', claim: 'partition-rank/CLP/analytic-rank PINNED on N0: rank bounds empty diagonal not off-diagonal fiber; cyclic index group d=1 not a cube' },
  { id: 'O183', claim: 'Phi-image-collapse REDUCES-TO-WALL: image=orbits+{0}, residual orbit count = |Sigma_r(mu_s)| = BGK wall; naive axis injection REFUTED' },
  { id: 'plotkin_cap', claim: 'antipodal/far-line route caps at delta*>=1/2 (odd poly cannot hit nonzero c at z and -z => #A_c<=|G|/2); prize-inert rho<1/4' },
  { id: 'collinearity_ne_count', claim: 'collinearity route does NOT escape count wall; collinear<=>antipodal-balance char-0 but mod-p transfer needs p>(6n)^(n/2), fails n>=64' },
  { id: 'sidon_antipodal', claim: 'Sidon bootstrap REFUTED (collective = BGK moment by Parseval); antipodal dominates but pins delta*=Johnson+1/n proxy' },
  { id: 'P7_rmds', claim: 'explicit mu_n HOMDS/BGM/rMDS route CLOSED; corank Theta(a) not O(1)' },
]
const AUDIT_SCHEMA = {
  type: 'object',
  required: ['claim_id', 'verdict', 'grounding', 'reasoning', 'escape_or_gap', 'confidence'],
  properties: {
    claim_id: { type: 'string' },
    verdict: { type: 'string', description: 'one of: sound-deadend | premature | overclaimed | cannot-verify' },
    grounding: { type: 'string', description: 'the specific repo artifact the verdict rests on, with path; "none-found" if no checkable artifact' },
    reasoning: { type: 'string', description: 'why the wall holds OR where it leaks; concrete and technical' },
    escape_or_gap: { type: 'string', description: 'if premature/overclaimed: the SPECIFIC escape or leap; if sound: "none". Do NOT invent escapes.' },
    confidence: { type: 'number', description: '0 to 1' },
  },
}
const COMPLETENESS_SCHEMA = {
  type: 'object',
  required: ['lens', 'untried_routes', 'assessment'],
  properties: {
    lens: { type: 'string' },
    untried_routes: { type: 'array', description: 'routes NOT in the walled set that could bound |Sigma_r| or sidestep it; empty if none genuinely new',
      items: { type: 'object', required: ['route', 'why_might_escape', 'feasibility'],
        properties: { route: { type: 'string' }, why_might_escape: { type: 'string' }, feasibility: { type: 'string' } } } },
    assessment: { type: 'string', description: 'honest verdict: is the walled set COMPLETE or is there a real gap? Do not manufacture routes.' },
  },
}
const auditPrompt = (w) =>
  'Adversarial skeptic auditing a claimed DEAD-END in the ArkLib delta*/proximity-prize ledger. Repo: ' + REPO +
  '. Prize believed to reduce to ONE open object: |Sigma_r(mu_n)| = BCHKS Conj 1.12 = BGK wall at deep r ~ log n.\n\n' +
  'CLAIM ' + w.id + ': ' + w.claim + '\n\nFind it: grep ' + LEDGER + ' for the O-number, and git log for the commit. Read the entry + any cited probe/Lean file.\n\n' +
  'Try to BREAK it: (1) grounded in a real checkable artifact or hand-wave? (2) does the conclusion FOLLOW or is there a gap? (3) OVERCLAIMED (one regime, small n, finite-size artifact)? (4) could it ACTUALLY escape the BGK wall (only claim escape with a SPECIFIC grounded mechanism)?\n' +
  'Most walls are probably sound; your value is catching the rare premature/overclaimed one OR confirming with grounding. Default sound-deadend unless a concrete grounded crack. Never fabricate an escape.'
const LENSES = [
  { key: 'methods', focus: 'METHODS not attempted that could bound |Sigma_r(mu_n)|: polynomial method variants, Fourier/L-function, sieve, Stepanov on sumsets, additive-combinatorics container/hypergraph, AG point-counting' },
  { key: 'levers', focus: 'NAMED-BUT-UNTRIED levers: scan ledger for "next lever"/"would need"/"untried"/"NEXT"/"absent from literature"; especially E_12(mu_n) joint energy (O176), Mansfield-Mudgal per-fiber extraction (O177)' },
  { key: 'literature', focus: 'RECENT LITERATURE 2024-2026 bounding incomplete char sums / subset-sums over thin multiplicative subgroups, or sidestepping BGK; check PAPERS_NEEDED.md + docs/kb/deltastar-*.md' },
  { key: 'structure', focus: 'STRUCTURAL features of mu_(2^k) not fully exploited: 2-power/antipodal/Frobenius/Galois/cyclotomic, or a reformulation (orbit-size x clique-orbits D*, Lam-Leung, tower descent)' },
]
const completePrompt = (L) =>
  'COMPLETENESS CRITIC for the ArkLib delta*/proximity-prize program. Repo: ' + REPO +
  '. ~15 routes walled, all converging on ONE open object: |Sigma_r(mu_n)| = BCHKS 1.12 = BGK wall at deep r ~ log n.\n' +
  'Read ledger ' + LEDGER + ' (O170-O184) and docs/kb/deltastar-*.md.\n\nYOUR LENS: ' + L.focus + '\n\n' +
  'Is the walled set COMPLETE, or is there a genuinely UNATTEMPTED grounded escape under your lens? ~25y-open analytic-NT barrier; do NOT manufacture routes. "Complete, no new route" is valid and likely correct. If a candidate, state honestly whether truly new or a relabeling.'
phase('WallAudit')
const audits = (await parallel(WALLS.map(w => () =>
  agent(auditPrompt(w), { label: 'audit:' + w.id, phase: 'WallAudit', model: 'opus', schema: AUDIT_SCHEMA, agentType: 'Explore' })
))).filter(Boolean)
phase('Completeness')
const completeness = (await parallel(LENSES.map(L => () =>
  agent(completePrompt(L), { label: 'complete:' + L.key, phase: 'Completeness', model: 'opus', schema: COMPLETENESS_SCHEMA, agentType: 'Explore' })
))).filter(Boolean)
phase('Synthesize')
const synthInput = 'Wall-audits:\n' + JSON.stringify(audits, null, 1) + '\n\nCompleteness:\n' + JSON.stringify(completeness, null, 1)
const synthesis = await agent(
  'SYNTHESIS lead making the ArkLib "$1M prize reduced to ONE conjecture" artifact bulletproof + honest. Repo: ' + REPO + '.\n\n' + synthInput + '\n\n' +
  '1. VERDICT: do all walls hold? list any premature/overclaimed with the gap. 2. COMPLETENESS: complete or a grounded untried route? 3. BULLETPROOF STATEMENT: honest one-paragraph reduction (delta* in [1-sqrt(rho) GG floor, 1-rho-Theta(1/log n) KKH26 ceiling]; residual = |Sigma_r(mu_n)| = BCHKS 1.12 = BGK wall; all escapes walled) + 3 caveats. 4. DOSSIER: which docs/kb/deltastar-*.md need updating + exact append text. Reduction not proof; no hype.',
  { label: 'synthesize', phase: 'Synthesize', model: 'opus' }
)
return { audits, completeness, synthesis }
