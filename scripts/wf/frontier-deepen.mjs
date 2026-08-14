export const meta = {
  name: 'frontier-deepen',
  description: 'Deepen the genuine survivors (N7 sheaf-conductor decisive √p-vacuity test, N12 log-concavity), stress the 3 un-tested skeletons (N8/N10/N11), and try fresh angles — all toward the char-p energy bound (#444)',
  phases: [
    { title: 'Deepen',  detail: 'N7 conductor √p-vacuity test; N12 log-concavity true/false/open' },
    { title: 'Stress',  detail: 'adversarial test of the 3 un-stressed skeletons N8/N10/N11' },
    { title: 'Fresh',   detail: 'genuinely-untried angles' },
    { title: 'Verdict', detail: 'honest synthesis' },
  ],
}
const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444 ($1M). TARGET: prove the char-p energy bound (the prize core, everything else formalized):
  rEnergy(μ_n; F_p, r) ≤ (2r−1)‼·n^r over F_p at r≈ln p≈110, n=2^30, p≈n·2^128 (n≈p^{0.19}).
Equivalently M = max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| ≤ √(2n log m) (BGK / generalized-Paley near-Ramanujan, exponent 1/2).
HARD CONSTRAINTS any approach must clear (else dead): (i) the MOMENT-METHOD NECESSITY OBSTRUCTION (in-tree
MomentLadderExceedsPrize): no single-moment/2nd-order count reaches the target — must capture CANCELLATION; (ii)
the **√p-VACUITY**: the subgroup has only n terms but Weil/Deligne gives O(√p) = O(p^{1/2}) ≫ n (since p≈n^{5.27},
√p≈n^{2.6}) — a naive Weil/cohomology bound is VACUOUS (bigger than the trivial n). An approach using
algebraic geometry MUST get the bound at the SUBGROUP scale (√n·polylog), not the field scale √p.
PRIOR (honest, after 4 assaults — literature 0 routes, Λ(q) reduces, 11 threads → 1 residual, 12 novel → 0
closures): every direction reduces to BGK/√p-vacuity. The genuine survivors that escape a SPECIFIC obstruction:
N7 _NovelEllAdicSheaf (escapes the 0-DIM Weil-vacuity — period lives on a 1-dim base A^1, H^1_c(A^1,[n]_*L_ψ)
pure non-vacuous; open=conductor of [n]_*L_ψ), N12 _NovelWildcard (Lorentzian/Hodge log-concavity of the energy
ladder; open=char-p log-concavity). The 3 un-stressed skeletons: N8 _NovelFiniteFreeEdge (finite-N edge
cumulant), N10 _NovelShawInvariant (Stickelberger norm-divisibility), N11 _NovelNilsequence (GTZ inverse at
depth~log p). EXHAUSTED (don't rehash): generic moment/energy/sup-norm, Λ(q), 2-power tower (refuted), good-prime
counting, GRH, modular gen-fn, decoupling/restriction/VMVT (μ_n flat), probabilistic extreme-value, di-Benedetto
(vanishes below p^{1/4}).
BUILD: scripts/pg-iterate.sh <file> (lock-free; READ #print axioms). autoImplicit OFF. Repo ${REPO}. Keep imports
MINIMAL (heavy imports time out the build).
HONESTY (PARAMOUNT): a fabricated proof wins NOTHING (committee runs the same Lean checker). CLOSED = genuine
axiom-clean char-p proof, no sorry/native_decide/fabricated-axiom/vacuous-or-circular hypothesis/hidden
[CharZero]. Default truth = "reduces or has a gap"; burden on the approach. Label honestly. Clobber-proof: RETURN
full fileContent.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['CLOSED','SKELETON','PARTIAL','REDUCES','REFUTED','OBSTRUCTION','FAILED']},
    axiomsClean:{type:'boolean'}, closesCharP:{type:'boolean'}, reducesToVacuity:{type:'boolean'},
    finding:{type:'string'}, theNewClaim:{type:'string'}, theGapOrFlaw:{type:'string'},
    file:{type:'string'}, keyTheorem:{type:'string'}, fileContent:{type:'string'}, summary:{type:'string'} },
}

const DEEPEN = [
  {id:'D-N7-conductor', file:'_FrontierSheafConductor', t:`DECISIVE TEST OF N7 (the best lead). The period η_b = Σ_{x∈μ_n}ψ(bx) is the trace function, on the b-line A^1, of the sheaf [n]_*L_ψ (multiplicative pushforward of Artin–Schreier by x↦x^n). Weil-II: |η_b| ≤ (dim H^1_c)·max|eigenvalue|. THE DECISIVE QUESTION: the Frobenius eigenvalues on H^1_c have weight giving |eigenvalue| = √p (NOT √n), and dim H^1_c ≈ conductor ≈ O(n) — so the naive bound is O(n·√p) ≫ n = VACUOUS (the √p-vacuity). Determine HONESTLY: (a) is there a normalization/twist (e.g. η_b/√? , or the RIGHT sheaf whose eigenvalues are √n not √p) that gives the subgroup-scale bound? (b) Or does N7 inescapably reduce to √p-vacuity = the same wall? Compute the actual conductor + weight via Katz (Gauss-sum sheaves, GKM). Land the precise verdict (CLOSED only if a genuine √n-scale bound emerges; else REDUCES with the exact vacuity mechanism). This resolves whether the sheaf route is real.`},
  {id:'D-N7-swan', file:'_FrontierSwanConductor', t:`N7 from the Katz SWAN side. Compute the Swan conductor of [n]_*L_ψ at 0 and ∞ explicitly (the wild ramification of the n-th-power pushforward of L_ψ). The number of singular points / total drop = dim H^1_c. KEY: does the eigenvalue weight on the relevant H^1 piece correspond to the SUBGROUP (√n) or the FIELD (√p)? In Katz's work on Gauss/Kloosterman sheaves the relevant sums ARE √p-scale per term — but η_b is a sum of n such, so the cancellation must be IN the cohomology dimension. Determine if dim H^1 can be o(√(p/n))·(needed) — i.e. whether the cohomological cancellation beats the √p-per-eigenvalue. Honest verdict + the precise conductor computation.`},
  {id:'D-N12-logconcave', file:'_FrontierLogConcavity', t:`DEEPEN N12: is the char-p energy ladder LOG-CONCAVE? The claim: rEnergy(F_p,·) is a Lorentzian/log-concave sequence in r, i.e. rEnergy(r)² ≥ rEnergy(r−1)·rEnergy(r+1)·(combinatorial factor), which would force the sub-Gaussian growth ⟹ prize. TEST it: (a) compute the char-p energy ladder EXACTLY for small n (8,16,32) multi-prime and CHECK log-concavity numerically (probe); (b) is char-0 energy log-concave (provable via the falling-factorial/Lam–Leung structure)? (c) does char-p log-concavity FOLLOW from a Hodge/Lorentzian structure, or is it REFUTED by wraparound (the excess could break log-concavity)? Land: if log-concave & provable → the prize; if refuted → countermodel; if open → the precise named Hodge residual. Be decisive with exact computation.`},
]
const STRESS = [
  {id:'S-N8-finitefree', file:'_FrontierFiniteFreeStress', t:`ADVERSARIALLY STRESS N8 (_NovelFiniteFreeEdge). Its open claim FiniteFreeEdgeBound is the finite-N edge inequality for the generalized-Paley characteristic polynomial. BREAK it: (1) does it reduce to the moment method / a magnitude (finite-free cumulants κ_2,κ_3,… ARE the moments in disguise)? (2) is the edge bound M ≤ κ_1 + C√(κ_2 log n) REFUTABLE — does a higher finite-free cumulant κ_j (j≈log n) blow up at the prize, exceeding the bound? (3) compute κ_2,κ_3 for μ_n exactly (small n) — do they match the BGK-required decay or violate it? Land the verdict + countermodel if refutable.`},
  {id:'S-N10-shaw', file:'_FrontierShawStress', t:`ADVERSARIALLY STRESS N10 (_NovelShawInvariant). Open claim ShawVanishingAtPrizeScale = the Stickelberger orbit-summed cyclotomic norm of every short 2^a-root relation is coprime to the prize prime. BREAK it: (1) is this just "no wraparound" renamed (= the prize, circular)? (2) is it REFUTABLE — does some short relation have norm divisible by a prize-scale prime (the norm is ≤ (2r)^{n/2}, and primes up to that size divide SOME norm)? (3) the orbit-sum: does the Galois orbit-summing actually reduce the divisibility, or is it the same bad-prime set? Land the verdict + countermodel.`},
  {id:'S-N11-nilseq', file:'_FrontierNilseqStress', t:`ADVERSARIALLY STRESS N11 (_NovelNilsequence). Open claims: NilsequenceInverseW (W_r large ⟹ period correlates with a degree-s nilsequence) + the no-correlation lemma (μ_n admits no such correlation). BREAK it: (1) the GTZ inverse theorem at depth s~r~ln p has complexity/bounds that are INEFFECTIVE or blow up — is the quantitative version even applicable at s~110? (2) does the "no-correlation" lemma secretly assume the bound (circular)? (3) is the U^s-norm ↔ W_r identification correct, or does it lose the cancellation? Land the verdict + the precise obstruction.`},
]
const FRESH = [
  {id:'F1-disproof-construct', file:'_FrontierDisproofConstruct', t:`THE DUAL (resolving δ* either way wins). Try HARD to CONSTRUCT a prize-scale counterexample: a prime p≈n^β (β≈5) and frequency b with |η_b| > C√(n log m), i.e. a genuine wraparound resonance at depth r≈log p. Search structured primes (Fermat-like, p with small order of 2, p≡1 mod high 2-power) where the 2-power subgroup might resonate. Either (a) construct/prove such a bad (p,b) exists → DISPROOF (prize floor FALSE, δ* below interior); or (b) prove the construction is impossible at p≫n² (no wraparound) → supports the bound. Exact computation at moderate n (64,128). Honest verdict on disproof feasibility.`},
  {id:'F2-subconvexity', file:'_FrontierSubconvexity', t:`SUBCONVEXITY for the degenerate L-function. Model M = sup over the n-element character group of the Gauss-sum sequence g(χ); this is the sup-norm of a finite Dirichlet polynomial. A subconvexity bound for the associated (degenerate, finite) L-function would give M ≤ √n·polylog. Determine: is there a NEW subconvexity-type input (amplification, moments of the family {g(χ)}) that gives sub-√p at the subgroup scale? Or does it reduce to the same √p-vacuity / the Lindelöf-hard case? Build the L-function model, state the subconvexity claim, honest verdict.`},
  {id:'F3-relative-trace', file:'_FrontierRelativeTrace', t:`RELATIVE TRACE / spectral identity. Invent a Kuznetsov/relative-trace-formula-type identity for the subgroup sum: expand Σ_b |η_b|^{2r} spectrally (over automorphic data of the right group) so cancellation appears as a spectral gap. KEY: must produce √n-scale, escape both the moment obstruction and √p-vacuity. State the identity, the spectral-gap claim, honest verdict (likely reduces — say where).`},
  {id:'F4-additive-deligne', file:'_FrontierWildcard2', t:`WILDCARD — a genuinely-new connection not yet tried in this campaign: e.g. a perfectoid/prismatic-cohomology angle on the char-p energy; an o-minimal/point-counting (Pila–Wilkie) bound on wraparound solutions; a quantitative-equidistribution input from homogeneous dynamics with EFFECTIVE rate; a Delsarte–LP bound on the period spectrum of Cay(F_p,μ_n). Pick the most promising, build it, escape both obstructions, honest verdict.`},
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
const mk = (phase) => (T) => agent(
  `${FRAME}

${phase.toUpperCase()} ${T.id}. Create ${DIR}/${T.file}.lean. ${T.t}
Return the structured verdict (set reducesToVacuity if it hits the √p-vacuity; closesCharP only if a genuine
axiom-clean char-p proof) + the COMPLETE fileContent.`,
  {label:`${phase}:${T.id}`, phase: phase==='deepen'?'Deepen':phase==='stress'?'Stress':'Fresh',
   effort:'high', schema:{...SCHEMA}})

phase('Deepen')
const deepened = await waved(DEEPEN, mk('deepen'), 3, 'Deepen')
phase('Stress')
const stressed = await waved(STRESS, mk('stress'), 3, 'Stress')
phase('Fresh')
const fresh = await waved(FRESH, mk('fresh'), 4, 'Fresh')

const all=[...deepened,...stressed,...fresh]
const closed=all.filter(r=>r.outcome==='CLOSED'&&r.closesCharP===true&&r.axiomsClean===true)
const tally={}; for(const r of all) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`frontier-deepen done: ${JSON.stringify(tally)} | CLOSED-and-clean: ${closed.length}`)
return { tally, closedCount: closed.length,
  closed: closed.map(r=>({id:r.id, file:r.file, key:r.keyTheorem})),
  results: all.map(r=>({id:r.id, outcome:r.outcome, closesCharP:r.closesCharP, reducesToVacuity:r.reducesToVacuity,
    axiomsClean:r.axiomsClean, file:r.file, theNewClaim:(r.theNewClaim||'').slice(0,200),
    theGapOrFlaw:(r.theGapOrFlaw||'').slice(0,300), finding:(r.finding||'').slice(0,400), fileContent:r.fileContent||''})) }
