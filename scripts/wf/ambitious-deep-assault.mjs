export const meta = {
  name: 'ambitious-deep-assault',
  description: 'Maximal-ambition meta-attack on the char-p bound: BREAK the two obstructions themselves, build the proof BACKWARD from the answer, non-Fourier bases, RG bootstrap, WZ/holonomic, info-theoretic, wild leaps — with REPAIR-before-refute (#444)',
  phases: [
    { title: 'Build',   detail: 'construct each ambitious approach maximally (max effort, real machinery)' },
    { title: 'Repair',  detail: 'ADVOCATE role: try hard to SAVE each before refuting' },
    { title: 'Judge',   detail: 'final honest kill-or-confirm on repaired survivors' },
  ],
}
const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444 ($1M). PROVE char-p: rEnergy(μ_n,r) ≤ (2r−1)‼·n^r over F_p, r≈ln p, n=2^30, p≈n·2^128
(n≈p^{0.19}). Equiv M=max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| ≤ √(2n log m). The campaign has tried ~50 single-domain
approaches; ALL reduce, caught in a PINCER: (i) MOMENT-NECESSITY (in-tree MomentLadderExceedsPrize: any
NON-NEGATIVE count c with Σc=n^r has (q·Σc²)^{1/2r} ≥ n > target — magnitude methods can't reach); (ii)
√p-VACUITY (Weil/Deligne eigenvalues are √p=n^{2.6}≫n; the period sheaf's H^1 eigenvalues ARE the n Gauss sums
g(χ), each |g(χ)|=√p). The additive↔multiplicative bridge is TAUTOLOGICAL (_BridgeOneWall). The only joint lever
(sum-product) vanishes at p^{0.19} (724× too thin). Explicit Gauss phases floor at n/4 DOF.
THIS ASSAULT IS DIFFERENT — be MAXIMALLY AMBITIOUS. Do NOT just try to escape the obstructions from a new domain.
ATTACK THE OBSTRUCTIONS THEMSELVES and build the proof BACKWARD. The two obstruction theorems have HYPOTHESES —
moment-necessity assumes a NON-NEGATIVE count; √p-vacuity assumes the STANDARD period sheaf. A genuinely new
object outside those hypotheses (a SIGNED/determinantal functional; a NON-standard cohomology with sub-√p weights;
a non-Fourier basis breaking Parseval) is NOT covered by them.
BUILD: scripts/pg-iterate.sh <file> (lock-free; READ #print axioms). autoImplicit OFF. Repo ${REPO}. MINIMAL imports.
HONESTY (PARAMOUNT): a fabricated proof wins nothing. A real escape must be machine-checkable axiom-clean and
genuinely outside BOTH obstruction hypotheses (not a count in disguise, not a cyclotomic char-0 object). Bold,
even wild, construction is encouraged in Build/Repair; only the final Judge verdict must be strict. Mark
escapesBoth=true only if you can defend it. Clobber-proof: RETURN full fileContent.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['ESCAPES','PROMISING','REDUCES','REFUTED','PARTIAL','FAILED']},
    axiomsClean:{type:'boolean'}, escapesBoth:{type:'boolean'}, escapesMoment:{type:'boolean'}, escapesVacuity:{type:'boolean'},
    mechanism:{type:'string'}, theNewClaim:{type:'string'}, repairTried:{type:'string'}, theGapOrFlaw:{type:'string'},
    file:{type:'string'}, keyTheorem:{type:'string'}, fileContent:{type:'string'}, summary:{type:'string'} },
}

const ANGLES = [
  {id:'A1-break-moment', file:'_AmbBreakMomentNecessity', t:`BREAK the moment-necessity obstruction from INSIDE. It only constrains NON-NEGATIVE counts c (Σc=n^r). Construct a SIGNED, computable functional of μ_n that is NOT a non-negative count — a DETERMINANT / Pfaffian / Fredholm determinant / alternating (inclusion-exclusion) sum / a resultant — that (a) bounds M, (b) genuinely sits below the n-floor because it carries CANCELLATION (signs), (c) is tractable. The Gauss period IS such a signed object; the question is whether a determinantal/Pfaffian REPRESENTATION of the energy (e.g. as a minor of a structured matrix, a Toeplitz/circulant determinant, or a Cauchy–Binet expansion) gives a bound the moment method cannot. Build the determinantal object + the bound it yields; check it escapes moment-necessity (is it really not a magnitude?).`},
  {id:'A2-break-vacuity', file:'_AmbBreakSqrtPVacuity', t:`BREAK the √p-vacuity. Weil gives √p because the STANDARD period sheaf has weight-1 Frobenius. Find a NON-standard geometric/cohomological realization of E_r whose relevant Frobenius eigenvalues are SUBGROUP-scale √n, not √p. Ideas: a sheaf on the n-dimensional SUBGROUP (not the p-element field) where the "field size" in Weil is n; a motivic/Voevodsky realization that REDUCES the weight; a relative/fibered cohomology where the √p's cancel in the fiber-integration leaving √n; or a perverse-sheaf decomposition isolating a sub-√p summand. Build the realization, compute the actual weight, and HONESTLY check whether √n-scale is achieved or √p re-enters (the N7 finding was √p re-enters — find a DIFFERENT realization that doesn't).`},
  {id:'A3-backward', file:'_AmbBackwardConstruction', t:`BUILD THE PROOF BACKWARD (co-design). ASSUME M ≤ √(2n log m) holds (it is believed true, numerics 0.77–0.85). The η_b are determined by the Gauss sums g(χ) via η_b=(n/(p−1))Σ_χ χ̄(b)g(χ). Derive the EXACT analytic constraint the bound places on the g(χ) (a constraint on their joint phase distribution / their correlations). Then identify which KNOWN property of Gauss sums (Hasse–Davenport, Gross–Koblitz, the Weil bound, a NEW relation) would IMPLY that constraint — and whether any is strong enough. The point: find what the proof MUST look like, then check if the required Gauss-sum input exists or is itself open. Land the backward-derived constraint + the precise missing input.`},
  {id:'A4-walsh-basis', file:'_AmbWalshNonFourier', t:`NON-FOURIER BASIS breaking Parseval symmetry. The additive↔multiplicative bridge is tautological because both are FOURIER bases (Parseval-dual). n=2^μ ⟹ the WALSH–HADAMARD / dyadic basis is natural and is NEITHER the additive nor multiplicative Fourier basis. Express the energy / the period in the Walsh basis adapted to the 2-power tower. Does η have a SPARSE or structured Walsh representation? Does the Walsh transform of the phase sequence concentrate (giving a bound the Fourier bases can't)? Build the Walsh representation of η_b and check whether it breaks the additive-multiplicative symmetry to give √n.`},
  {id:'A5-rg-bootstrap', file:'_AmbRGBootstrap', t:`RENORMALIZATION-GROUP BOOTSTRAP (non-decoupling). The 2-power tower μ_2⊂…⊂μ_n is self-similar. Tower DECOUPLING is refuted (saving-neutral). But build a genuine RG FLOW: a coarse-graining map T on the bound/energy under doubling n→2n that is CONTRACTIVE — where a weak bound at level k improves at level k+1 toward √n, with the improvement coming from the JOINT (not decoupled) structure of consecutive levels. Construct T, find its fixed point, check whether the fixed point is √n (escape) or √n^{1−o(1)} (BGK floor = no improvement). Honest: tower decoupling failed because it preserved the saving; find a NON-saving-preserving coarse-graining or show none exists.`},
  {id:'A6-holonomic-wz', file:'_AmbHolonomicWZ', t:`HOLONOMIC / CREATIVE-TELESCOPING (WZ) certificate. Treat Σ_{b≠0}|η_b|^{2r} or the period as a HOLONOMIC sequence in r (and n). Use Zeilberger creative telescoping / a WZ pair to derive an EXACT recurrence in r, then bound its solution. The energy E_r satisfies a P-recurrence (it is a diagonal of a rational generating function); if the recurrence has the right sign structure / its characteristic roots are √n-scale, the bound follows. Build the holonomic recurrence for E_r(μ_n) (or its char-0/char-p ratio) and analyze its asymptotics — does it give sub-Gaussian growth (escape) or does the recurrence's dominant root reproduce BGK?`},
  {id:'A7-info-theoretic', file:'_AmbInfoTheoretic', t:`INFORMATION-THEORETIC / complexity bound. Argue M is small because a large |η_b| would encode too much information. Candidates: (a) a Kolmogorov-complexity argument — the worst-case b is a short description, so η_b can't be "specially aligned" beyond its description length, bounding it; (b) a quantum query / communication-complexity lower bound that translates to a sup-norm bound; (c) an entropy/transport bound on the phase distribution. The genuinely-new content: a bound that comes from the COMPLEXITY of the worst-case configuration, not its magnitude. Build the info-theoretic functional and the bound; check it escapes moment-necessity (complexity is not a count) and √p-vacuity.`},
  {id:'A8-wild', file:'_AmbWildLeap', t:`THE WILD LEAP — the single most unexpected, never-tried idea, with a real kernel. Candidates (pick ONE and build it hard, or invent better): (a) a FIXED-POINT theorem on the space of phase configurations forcing the bound; (b) a self-referential / diagonalization argument; (c) a connection to a ZERO-FREE REGION / explicit-formula identity where M is bounded by a zero-density estimate; (d) a HOLOGRAPHIC / AdS-CFT-style duality mapping the sup to a bulk geometric quantity with a curvature bound; (e) a TROPICAL/idempotent-semiring linearization where max becomes sum; (f) an aperiodic-order / quasicrystal diffraction bound. Maximum creativity. Build the object, state the claim, and HONESTLY assess whether it escapes both obstructions or collapses.`},
]

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, sz, lbl){
  let acc=[]
  for (const [i,w] of chunk(items,sz).entries()){
    log(`${lbl} wave ${i+1}/${Math.ceil(items.length/sz)} (${w.map(x=>x.id).join(', ')})`)
    acc=acc.concat(((await parallel(w.map(it=>()=>mk(it))))||[]).filter(Boolean))
  }
  return acc
}

phase('Build')
const built = await waved(ANGLES, (T)=>agent(
  `${FRAME}

BUILD (maximal ambition) ${T.id}. Create ${DIR}/${T.file}.lean. ${T.t}
Construct the machinery as far as you genuinely can — real objects, real Lean skeleton, the precise new claim.
Be bold; this is the build phase. Return mechanism + theNewClaim + escapesMoment/escapesVacuity self-assessment
+ full fileContent.`,
  {label:`build:${T.id}`, phase:'Build', effort:'high', schema:{...SCHEMA}}), 4, 'Build')

phase('Repair')
const repaired = await waved(built.filter(r=>r.outcome!=='FAILED'), (r)=>agent(
  `${FRAME}

REPAIR (ADVOCATE role — your job is to SAVE this, not kill it) ${r.id}. Mechanism: ${(r.mechanism||'').slice(0,500)}.
Claim: ${(r.theNewClaim||'').slice(0,300)}. Self-assessed escapesMoment=${r.escapesMoment} escapesVacuity=${r.escapesVacuity}.
File: ${DIR}/${(r.file||'').split('/').pop()}. Try HARD to find the FIX that makes it genuinely escape BOTH
obstructions — a different normalization, a missing twist, a sharper object, a combination with another mechanism.
Only concede (PARTIAL/REDUCES) if after real effort it is truly irreparable, and say exactly why. If you can
repair it into a genuine escape, build the repaired Lean (axiom-clean) and mark escapesBoth=true. Return the
repaired version + fileContent.`,
  {label:`repair:${r.id}`, phase:'Repair', effort:'high', schema:{...SCHEMA}}), 4, 'Repair')

phase('Judge')
const rmap=new Map(repaired.filter(Boolean).map(v=>[v.id,v]))
const merged=built.map(r=>rmap.get(r.id)||r)
const candidates=merged.filter(r=>r.escapesBoth===true||r.outcome==='ESCAPES'||r.outcome==='PROMISING')
const judged = candidates.length ? await waved(candidates, (r)=>agent(
  `${FRAME}

FINAL JUDGE (strict, honest) ${r.id} — it survived repair claiming escapesBoth. Mechanism: ${(r.mechanism||'').slice(0,400)}.
Claim: ${(r.theNewClaim||'').slice(0,300)}. Repair: ${(r.repairTried||'').slice(0,300)}. File: ${DIR}/${(r.file||'').split('/').pop()}.
Re-run pg-iterate, audit #print axioms (sorryAx? native_decide? fabricated axiom? vacuous/circular hyp?). Decide
DEFINITIVELY: does it GENUINELY escape BOTH obstructions (not a count in disguise, not cyclotomic char-0, not the
tautological bridge), is it axiom-clean, and would it close the bound? ESCAPES only if all yes. Else REDUCES/REFUTED
with the exact flaw. Be the final honest arbiter. Return verdict + fileContent.`,
  {label:`judge:${r.id}`, phase:'Judge', effort:'high', schema:{...SCHEMA}}), 3, 'Judge') : []

const jmap=new Map(judged.filter(Boolean).map(v=>[v.id,v]))
const fin=merged.map(r=>jmap.get(r.id)||r)
const escapes=fin.filter(r=>r.outcome==='ESCAPES'&&r.escapesBoth===true&&r.axiomsClean===true)
const tally={}; for(const r of fin) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`ambitious-deep-assault done: ${JSON.stringify(tally)} | ESCAPES: ${escapes.length}`)
return { tally, escapeCount: escapes.length,
  escapes: escapes.map(r=>({id:r.id, file:r.file, claim:r.theNewClaim, key:r.keyTheorem})),
  results: fin.map(r=>({id:r.id, outcome:r.outcome, escapesBoth:r.escapesBoth, axiomsClean:r.axiomsClean, file:r.file,
    mechanism:(r.mechanism||'').slice(0,180), theNewClaim:(r.theNewClaim||'').slice(0,180),
    theGapOrFlaw:(r.theGapOrFlaw||'').slice(0,260), fileContent:r.fileContent||''})) }
