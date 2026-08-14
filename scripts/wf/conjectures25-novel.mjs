export const meta = {
  name: 'conjectures25-novel',
  description: 'Generate 25 highly-novel NT conjectures to prove δ* exactly (loop-until-25 at NOVELTY≥9, notBGK as ranking score, dead-ledger re-skins banned), then adversarially attack/refute all 3-lens (#444)',
  phases: [
    { title: 'Generate', detail: 'loop: diverse-angle generators (dead lanes banned) → novelty judge → accumulate 25, ranked by notBGK' },
    { title: 'Refute', detail: 'each survivor attacked by 3 adversarial lenses (reduce-to-BGK / reduce-to-Johnson / countermodel)' },
    { title: 'Synthesize', detail: 'the conjecture ledger with verdicts' },
  ],
}

const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'
const TARGET = 25
const ROUND_CAP = 8

const FRAME = `THE PROBLEM (#444). Prove δ* — the mutual-correlated-agreement / list-decoding threshold for
EXPLICIT dyadic Reed-Solomon codes — EXACTLY, in the window interior (1−√ρ, 1−ρ−Θ(1/log n)), prize
regime n=2^μ~2^30, q=n^β (β≈4-5, the Burgess barrier), ε*=2^-128. Repo ${REPO}.

THE DEFINITIVE STATE (proven, axiom-clean): δ* is bracketed [1−√ρ (Johnson), (1−ρ)−Θ(1/log n) (KKH26
ceiling)] and reaches the window INTERIOR (toward capacity) ⟺ the char-p BGK/Paley floor
  M(n) = max_{b≠0}|Σ_{x∈μ_n} e_p(bx)| ≤ C√(n·log m),  m=(q−1)/n,
equivalently the char-p Lam-Leung energy A_r = E_r(μ_n) − n^{2r}/q ≤ (2r−1)‼·n^r at depth r≈ln q≈89.
char-0 is CLOSED (Lam-Leung antipodal pairing, all r); the open prize is the char-p transfer at deep r.

⚠️ THE HARD CONSTRAINT — almost everything REDUCES TO THIS BGK WALL. The campaign ran 79/50/100/140-
conjecture sweeps with ZERO survivors: every moment method, energy bound, second-order method, additive-
energy, spectral λ₂, SDP/LP, cumulant, sum-product, Stepanov (μ_n is 0-dim, door SHUT), discriminant
(class-field-fixed), completion-sum, dyadic-tower descent, the complete-homog SPECTRUM (super-poly /
exponentially loose, REFUTED s=32), the over-det / distinct-γ deep union (O(n) = Johnson proxy, REFUTED
as escape). The META-THEOREM proves any winning method must be SIMULTANEOUSLY (a) b-sensitive, (b)
deterministic-archimedean (NOT probabilistic-EVT: periods are exchangeable white-noise Cov=−Var/(m−1)),
(c) genuinely L-infinity (sup not RMS). The far-line proxy → Johnson (Plotkin lower envelope).

YOUR JOB: invent NT hypotheses that, IF TRUE, would pin δ* EXACTLY, prioritizing structural ORTHOGONALITY
to the M≤C√(n log m) / energy wall (a different invariant, a different equidistribution input, a phase/
valuation object the moment-blind meta-theorem cannot see, an exact arithmetic identity that pins the value
without √-cancellation, a rigidity/structure result). The notBGK axis (likelihood NOT to reduce) is a
RANKING score — report it honestly; near-certain reduction is fine to report as long as the IDEA is
genuinely NEW. The GATE for acceptance is NOVELTY ≥ 9: the conjecture must be a genuinely new MECHANISM,
NOT a re-skin of an already-swept lane.

⛔ BANNED — these are DEAD-LEDGER repackagings; do NOT emit them (they auto-score novelty ≤4):
Stickelberger/Chebotarev/Spur_r divisor-count (in-tree _AvW2), Delsarte/LP/Krein/SDP "third route"
(delsartelpnogo), theta/metaplectic/Weil-rep self-similarity & AFE, root-number/cocycle/Galois-defect
sign rigidity (in-tree finite-2-group, ArchimedeanPhaseRealDFT), SoS/PC-degree/Dvir-Mehta-Oliveira/
Razborov-Smolensky relation-rank (proof-complexity bounds CERTIFYING not COUNTING), subconvexity/QUE/
Kuznetsov main-term, discriminant/disc (class-field-fixed, discnogo), Stepanov/curve (μ_n 0-dim, SHUT),
cosh-MGF/Bessel saddle, dyadic-tower/crossCell descent, complete-homog spectrum, sum-product/Elekes-Szabo,
o-minimal/Pila-Wilkie height-count of the period (height = LOWER bound, wrong direction). If your idea is
ANY of these, it is NOT novel — discard it and think harder.

✅ WANT — push into genuinely UNTRIED structural territory. Examples of the FLAVOR (not a checklist):
a conjecture relating δ* to a quantity that is EXACTLY COMPUTABLE and provably p-independent yet NOT the
distinct-γ union; an exact functional/recursion with a COMPUTABLE fixed point that is NOT the energy
ladder; a rigidity statement forcing the worst-direction to a STRUCTURED form whose list is exactly
countable; a connection to a DIFFERENT solved problem (a transfer FROM a place where the analog IS known);
an obstruction-theoretic / cohomological exact count; a combinatorial-design / finite-geometry EXACT
realization; a connection to a computable spectral invariant of a DIFFERENT operator. Invent boldly.

HONESTY: bold in EXPLORATION (false/speculative conjectures are FINE and expected — label them conjecture);
strict in PROOF-CLAIMS (never claim δ* closed). A conjecture that turns out to reduce-to-BGK is a SUCCESSFUL
refutation in the later phase, NOT a reason to suppress a genuinely novel idea now.`

const GEN_SCHEMA = {
  type:'object', additionalProperties:false, required:['angle','candidates'],
  properties:{
    angle:{type:'string'},
    candidates:{type:'array', items:{type:'object', additionalProperties:false,
      required:['signature','statement','mechanism','whyNotBGK','feasibility','novelty','notBGK'],
      properties:{
        signature:{type:'string', description:'short canonical name for dedup, e.g. "QUE-subconvexity-rate"'},
        statement:{type:'string', description:'the precise NT hypothesis, math notation, that if true pins δ* exactly'},
        mechanism:{type:'string', description:'HOW it pins δ* exactly — the chain from hypothesis to exact δ*'},
        whyNotBGK:{type:'string', description:'the structural reason it does NOT reduce to M≤C√(n log m) / energy — what orthogonal object it uses'},
        feasibility:{type:'integer', description:'1-10, plausibility of proving it with current/near math'},
        novelty:{type:'integer', description:'1-10, genuinely new vs the dead ledger'},
        notBGK:{type:'integer', description:'1-10, likelihood it does NOT collapse to the BGK/energy wall (10=fully orthogonal)'},
      }}},
  },
}
const JUDGE_SCHEMA = {
  type:'object', additionalProperties:false, required:['signature','verdict','feasibility','novelty','notBGK','reason'],
  properties:{
    signature:{type:'string'}, statement:{type:'string'}, mechanism:{type:'string'},
    verdict:{type:'string', enum:['ACCEPT','REJECT']},
    feasibility:{type:'integer'}, novelty:{type:'integer'}, notBGK:{type:'integer'},
    reason:{type:'string'},
  },
}
const REFUTE_SCHEMA = {
  type:'object', additionalProperties:false, required:['signature','outcome','reason'],
  properties:{
    signature:{type:'string'},
    outcome:{type:'string', enum:['REDUCES-TO-BGK','REDUCES-TO-JOHNSON','REFUTED-FALSE','SURVIVES','SURVIVES-PARTIAL']},
    reason:{type:'string'}, lens:{type:'string'},
  },
}

// Distinct mathematical angles — each generator gets one (rotated/varied by round to avoid repeats).
const ANGLES = [
  'Automorphic / subconvexity / QUE: reframe M≤... as an effective equidistribution / shifted-convolution / spectral-gap rate for the μ_n-orbit; use a subconvexity or Hecke-Maass / cat-map QUE input as the pinning hypothesis. Orthogonal: it pins the EXACT rate via L-function analytic continuation, not √-cancellation moments.',
  'Optimal transport / Wasserstein / value-distribution: pin δ* via a W₁/W₂ extreme-value upgrade of the Kowalski-Untrau Gauss-period family limiting law (the LIMITING DISTRIBUTION + effective rate gives the exact max, not a moment bound). Frequency-side correlation only (period-side is white-noise).',
  'Association schemes / pseudocyclic / van Dam-Muzychuk: the cyclotomic scheme on μ_n is ALMOST pseudocyclic (where all |η|=√v EXACTLY); pin δ* by a hypothesis on the exact pseudocyclic DEFECT (a design-theoretic invariant), giving the value exactly, not a bound.',
  'p-adic / Newton polygon / Stickelberger / valuation: the NP slopes v_2(η_b) / Stickelberger congruences are NOT functions of archimedean moments (escape the moment-blind meta-theorem). Pin δ* by a divisibility/valuation rigidity hypothesis on the period max.',
  'Phase-aware transfer operator / dynamics: the operator (𝒯f)(b)=f(b)+e^{iθ_b}f(ζb) retains the relative dilation phase θ_b the magnitude recursion drops. Pin δ* via a hypothesis on the spectral radius / phase-law θ_b — a b-sensitive deterministic-archimedean object.',
  'Diophantine / continued-fraction / three-gap: pin δ* via an equidistribution-RATE / discrepancy hypothesis on the orbit positions (three-gap positional rigidity), giving the exact constant via low-discrepancy structure, not moments.',
  'Model theory / o-minimality / unlikely intersections (Habegger 1611.07287): pin the HOUSE/sup-norm of the degree-m Gauss-period algebraic integer via o-minimal point-counting (Pila-Wilkie style) — an exact-count input orthogonal to energy.',
  'Additive combinatorics BEYOND energy (Kelley-Meka / PFR / structure-vs-randomness): replace the lossy Cauchy-Schwarz energy→sup step with an entropy / density-increment hypothesis; pin δ* via a structure theorem for the worst direction, not its energy.',
  'Proof complexity / SoS / Dvir-Mehta-Oliveira: pin δ* via a hypothesis on the SoS/PC degree to CERTIFY (or bound the COUNT of) vanishing sums of 2^μ-th roots mod p — a complexity-theoretic invariant of the defect, orthogonal to analytic cancellation.',
  'Class field theory / Stark / heights / Gross-Koblitz: pin δ* via an exact arithmetic identity (Stark units, height pairing, Gross-Koblitz Γ_p product) that EQUATES the period max to a class-number / regulator quantity computable exactly — value not bound.',
  'Metaplectic / Weil representation / theta self-similarity: pin δ* via the x↦x² metaplectic self-similarity / theta functional equation giving an exact RECURSION on M(n) with a computable fixed-point, orthogonal to dyadic-tower descent (which is dead).',
  'Liu-Zhou subgroup-restriction eigenvalue recursion (1809.09829): λ₂(μ_{2^μ}) ≤ λ₂(boundary on index-2 sublattice) + ... — a MULTISCALE eigenvalue recursion (NOT the dead crossCell descent); pin δ* via a per-level boundary-Cayley hypothesis.',
  'FKM / Fourier-stability / l-adic sheaves (1508.00512): M(n) is literally a DFT of 1_{μ_n}; pin δ* via an FKM Fourier-stability hypothesis transporting a sub-√p sheaf estimate through the DFT — a trace-function / monodromy object.',
  'Hidden-coset / averaged-advantage (Legendre-PRF, 2024/1252): pin δ* via a hypothesis that bounds the AVERAGE-over-m-cosets advantage (the worst-case follows by a smoothness/regularity transfer) — an information-theoretic reframing avoiding the worst-case sup.',
  'Restriction / decoupling on the FREQUENCY side: the period side is flat/white-noise (decoupling dead there), but the b↦η_b field over m=2^128 cosets may carry curvature; pin δ* via a frequency-side restriction/decoupling hypothesis.',
  'EXACT closed-form / generating-function for δ* itself (not the spectrum): a pole-structure / functional-equation hypothesis on Z(t)=Σ I_r t^r that yields the EXACT δ* value as a residue — bypassing the bound entirely.',
]

function sig(s){ return (s||'').toLowerCase().replace(/[^a-z0-9]+/g,'-').replace(/^-|-$/g,'').slice(0,60) }
function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, sz){
  let acc=[]
  for (const w of chunk(items,sz)) acc=acc.concat(((await parallel(w.map(it=>()=>mk(it))))||[]).filter(Boolean))
  return acc
}

phase('Generate')
const survivors = []          // accepted conjectures
const seen = new Set()        // dedup signatures
let round = 0
while (survivors.length < TARGET && round < ROUND_CAP) {
  round++
  // rotate angles by round so each round explores a different slice + a "wildcard new angle" instruction
  const roundAngles = ANGLES.map((a,i) => ({a, i})).filter((_,i)=> (i + round) % 2 === round % 2 || round >= 4)
  const useAngles = round >= 4 ? ANGLES.map((a,i)=>({a,i})) : roundAngles   // later rounds use ALL angles
  log(`Generate round ${round}: ${survivors.length}/${TARGET} survivors so far, ${useAngles.length} angles`)
  // generate
  const gens = await waved(useAngles, ({a,i}) => agent(
    `${FRAME}

ANGLE (round ${round}): ${a}
Generate 3-4 DISTINCT candidate NT hypotheses from THIS angle that, if true, pin δ* EXACTLY. Be your OWN
harshest critic on NOVELTY: only emit candidates that are a genuinely NEW MECHANISM (novelty≥9), NOT a
re-skin of any BANNED dead-ledger lane. For each: a precise math statement, the mechanism pinning δ*
exactly, and the structural object it uses. Score each on feasibility/novelty/notBGK (1-10) — report
notBGK HONESTLY (it is a ranking score, not a gate; a novel idea that probably reduces is still wanted).
${survivors.length>0 ? `ALREADY ACCEPTED (do NOT duplicate these signatures/mechanisms): ${survivors.map(s=>s.signature).join('; ')}` : ''}`,
    {label:`gen:r${round}-a${i}`, phase:'Generate', schema:{...GEN_SCHEMA}}
  ), 4)
  // collect fresh candidates
  const cands = gens.flatMap(g => (g.candidates||[]).map(c=>({...c, angle:g.angle}))).filter(c => {
    const k = sig(c.signature); if (seen.has(k)) return false; seen.add(k); return true
  })
  // pre-filter on self-novelty, then hard independent judge (gate = NOVELTY; notBGK is a ranking score)
  const preFiltered = cands.filter(c => (c.novelty>=8))
  log(`  round ${round}: ${cands.length} fresh candidates, ${preFiltered.length} pass self-novelty → judging`)
  const judged = await waved(preFiltered, (c) => agent(
    `${FRAME}

ADVERSARIALLY JUDGE this candidate conjecture for NOVELTY (the acceptance gate). DEFAULT TO REJECT — most
ideas are re-skins of an already-swept lane. ACCEPT only if it is a GENUINELY NEW MECHANISM not in the
dead ledger / BANNED list.
  signature: ${c.signature}
  statement: ${c.statement}
  mechanism: ${c.mechanism}
  whyNotBGK: ${c.whyNotBGK}
Score HARD and INDEPENDENTLY (ignore the generator's scores): feasibility (provable?), novelty (is it
REALLY a new mechanism, or a repackaging of a BANNED/dead lane? — be ruthless about repackagings), notBGK
(your honest estimate it avoids the M≤C√(n log m)/energy wall — a RANKING score, NOT a gate; report it and
note the likely reduction if you see one, but do NOT reject for it). VERDICT=ACCEPT iff **novelty ≥ 9**
(a genuinely new mechanism). The reduce-to-BGK test happens in a LATER adversarial phase — your job here is
ONLY to certify genuine novelty and rank by notBGK. Reject re-skins of: ${''}Stickelberger/Chebotarev,
Delsarte/Krein, theta/metaplectic, root-number/cocycle, SoS/PC-degree, subconvexity/QUE, o-minimal-height,
discriminant, Stepanov, cosh-saddle, dyadic descent, complete-homog spectrum, sum-product.`,
    {label:`judge:r${round}-${sig(c.signature).slice(0,20)}`, phase:'Generate', schema:{...JUDGE_SCHEMA}}
  ), 4)
  // accept on NOVELTY gate; notBGK retained as a ranking score
  const cmap = new Map(cands.map(c=>[sig(c.signature), c]))
  for (const j of judged.filter(Boolean)) {
    if (j.verdict==='ACCEPT' && j.novelty>=9 && survivors.length<TARGET) {
      const c = cmap.get(sig(j.signature)) || {}
      survivors.push({signature:j.signature, statement:j.statement||c.statement, mechanism:j.mechanism||c.mechanism,
        whyNotBGK:c.whyNotBGK, feasibility:j.feasibility, novelty:j.novelty, notBGK:j.notBGK, angle:c.angle, judgeReason:j.reason})
    }
  }
  log(`  round ${round} done: ${survivors.length}/${TARGET} accepted`)
}
log(`Generation complete: ${survivors.length} survivors after ${round} rounds`)

phase('Refute')
// each survivor attacked by 3 adversarial lenses
const LENSES = [
  {k:'reduce-BGK', p:`Try to REDUCE this conjecture to the BGK/energy wall M≤C√(n log m) / A_r≤(2r−1)‼n^r. Trace an explicit reduction: does proving it require / imply the char-p √-cancellation? If yes, outcome=REDUCES-TO-BGK with the chain.`},
  {k:'reduce-Johnson', p:`Try to show this conjecture only reaches JOHNSON (the far-line Plotkin proxy δ*→1/2, or caps at 1−√ρ), not the window interior. If it pins only the proxy / a lower envelope, outcome=REDUCES-TO-JOHNSON.`},
  {k:'countermodel', p:`Try to REFUTE the conjecture FALSE: find a machine-checkable countermodel (exact small-n F_p computation, a structural contradiction with an in-tree proven fact, or a vacuity). If false/vacuous, outcome=REFUTED-FALSE with the countermodel.`},
]
const refuteJobs = survivors.flatMap(s => LENSES.map(L => ({s, L})))
const refutations = await waved(refuteJobs, ({s,L}) => agent(
  `${FRAME}

ADVERSARIALLY ATTACK this surviving conjecture via ONE lens. Default to KILLING it.
  signature: ${s.signature}
  statement: ${s.statement}
  mechanism: ${s.mechanism}
LENS [${L.k}]: ${L.p}
If the attack fails (you cannot reduce/refute it), outcome=SURVIVES (or SURVIVES-PARTIAL) with what you
tried. Be concrete: an exact computation, a named reduction, or a structural argument — not vague.`,
  {label:`refute:${sig(s.signature).slice(0,18)}-${L.k}`, phase:'Refute', schema:{...REFUTE_SCHEMA}}
), 5)

phase('Synthesize')
// aggregate per-conjecture verdicts
const byConj = new Map(survivors.map(s=>[sig(s.signature), {conj:s, attacks:[]}]))
for (const r of refutations.filter(Boolean)) {
  const e = byConj.get(sig(r.signature)); if (e) e.attacks.push(r)
}
const ledger = [...byConj.values()].map(({conj, attacks}) => {
  const killed = attacks.find(a => ['REDUCES-TO-BGK','REDUCES-TO-JOHNSON','REFUTED-FALSE'].includes(a.outcome))
  return {
    signature: conj.signature, statement: conj.statement, mechanism: conj.mechanism,
    feasibility: conj.feasibility, novelty: conj.novelty, notBGK: conj.notBGK, angle: conj.angle,
    finalVerdict: killed ? killed.outcome : 'SURVIVES',
    killReason: killed ? killed.reason : null,
    attacks: attacks.map(a=>({lens:a.lens||a.outcome, outcome:a.outcome, reason:(a.reason||'').slice(0,300)})),
  }
})
const tally={}; for(const l of ledger) tally[l.finalVerdict]=(tally[l.finalVerdict]||0)+1
log(`conjectures25 done: ${survivors.length} generated, verdicts ${JSON.stringify(tally)}`)
return { rounds:round, generated: survivors.length, tally, ledger }
