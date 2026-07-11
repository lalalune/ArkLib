export const meta = {
  name: 'buildoff-onset',
  description: 'Build novel directions OFF the Jacobi/onset learnings: the prize = wraparound onset r_0>log p = geometry-of-numbers of 𝔭-divisible sumset elements in ℤ[ζ_n]; attack via GoN / minimal relation / weight-lowering / Stickelberger 𝔭-adic / mollified signed period (#444)',
  phases: [
    { title: 'Build',  detail: '8 build-off directions, each a new object grounded in the onset/GoN learning' },
    { title: 'Verify', detail: 'adversarial: genuinely new + does it bound r_0 / escape, or hit the same wall?' },
  ],
}
const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444 ($1M). LEARNINGS to build off (all established this session, axiom-clean):
- The prize ⟺ the wraparound onset r_0(n) > r*≈log p: W_r=E_r(F_p)−E_r^{char0}=0 (no wraparound) for r<r_0, and
  r_0 is the smallest r with a 𝔭-DIVISIBLE non-antipodal element of Z[ζ_n] (𝔭|p) in the radius-r sumset disk.
- W_r is exactly 0 in the deep-thin prize regime up to computable depth; the off-diagonal Jacobi correlation is
  STRUCTURED (not √-cancelling: W/√offdiag GROWS 0,0.95,19.4 at r=2,3,4). So the prize is NOT a √-cancellation —
  it is the onset/no-wraparound statement.
- The worst-case NORM bound r_0 ≳ (½)p^{1/φ(n)} is TOO WEAK at scale (φ(2^30)=2^29 ⟹ (2r)^{2^29}≫p for all r≥1 ⟹
  gives r_0≥1 only). The actual onset is governed by the SPARSE structure of wrapping relations, not worst-case norm.
- √p RE-ENTERS in the Fermat/AG framing at the MIDDLE cohomology H^{2r-1} of the correlation variety V_corr (weight
  2r-1, residual p^{1/2}); Fermat Betti ~n^r blows up; Katz equidist is fixed-order distributional. (_JacobiFermatCohomology.)
- Vanishing sums of 2^μ-th roots are ANTIPODAL pairs {x,−x} only (Conway–Jones/Mann); a wrapping relation must be a
  NON-antipodal short ±1 combination divisible by 𝔭.
THE GENUINELY-NEW DOORS (build off these, don't repeat AG/character-sum/moment): GEOMETRY OF NUMBERS of the ideal
𝔭⊂Z[ζ_n] (shortest vector / covering radius / successive minima / transference — these bound r_0 by the ACTUAL
lattice geometry, NOT the worst-case norm); the minimal non-antipodal wrapping relation; a weight-LOWERING
geometric realization; the 𝔭-adic Stickelberger valuation structure of wrapping relations; a mollified/weighted
SIGNED period whose off-diagonal genuinely cancels.
TWO OBSTRUCTIONS still apply (an escape must clear both): moment-necessity (must be cancellation/structure, not a
count) + √p-vacuity (subgroup scale √n, not field √p). But the onset/GoN framing is NOT obviously either — it is a
LATTICE question. Test honestly whether GoN gives a real r_0 bound or reduces.
BUILD: scripts/pg-iterate.sh <file> (lock-free; READ #print axioms). autoImplicit OFF. Repo ${REPO}. MINIMAL imports.
HONESTY (PARAMOUNT): a fabricated proof wins nothing. CLOSED = genuine axiom-clean proof of r_0>log p (or the prize).
NEW r_0 BOUND = a genuinely better-than-norm lower bound on the onset, machine-checked. Default = reduces. RETURN full fileContent.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['CLOSED','NEW_BOUND','PROMISING','REDUCES','REFUTED','PARTIAL','FAILED']},
    axiomsClean:{type:'boolean'}, boundsOnset:{type:'boolean'}, genuinelyNew:{type:'boolean'},
    mechanism:{type:'string'}, theNewClaim:{type:'string'}, theGapOrFlaw:{type:'string'},
    file:{type:'string'}, keyTheorem:{type:'string'}, fileContent:{type:'string'}, summary:{type:'string'} },
}

const ANGLES = [
  {id:'G1-shortest-vector', file:'_OnsetShortestVector', t:`GEOMETRY OF NUMBERS — the shortest 𝔭-vector. The onset r_0 is the first r where the radius-r sumset disk of μ_n contains a NONZERO non-antipodal element of the ideal 𝔭⊂Z[ζ_n]. Lower-bound r_0 by the LENGTH of the shortest nonzero element of 𝔭 in the relevant (archimedean × all-embeddings) metric: a sum of ≤2r roots of unity has each archimedean embedding of size ≤2r, so r_0 ≥ (½)·(shortest-𝔭-vector length in the sup-over-embeddings norm). Compute/bound the shortest 𝔭-vector of Z[ζ_{2^μ}] (𝔭 above p): is it ≥ p^{1/φ(n)} (Minkowski, = the weak norm bound) or can the 2-POWER cyclotomic structure (the explicit integral basis / the different) give a BETTER shortest-vector bound? This is the crux: does GoN beat the worst-case norm for 2-power cyclotomic 𝔭? Build the GoN object + the r_0 bound it yields; honest verdict (better than norm, or same).`},
  {id:'G2-covering-transference', file:'_OnsetCoveringTransference', t:`COVERING RADIUS / TRANSFERENCE. r_0 relates to the COVERING RADIUS of 𝔭 (when does the radius-r disk start covering a 𝔭-point) via Minkowski's 2nd theorem / Banaszczyk transference (λ_1·μ ≤ stuff). Use transference between 𝔭 and its dual 𝔭^∨ (the inverse different / the codifferent) to bound r_0. The dual lattice of 𝔭 in Z[ζ_{2^μ}] has explicit structure (the different of Q(ζ_{2^μ}) is (2^μ)·… ). Does transference give a better r_0 than Minkowski's 1st theorem? Build the transference bound; honest verdict.`},
  {id:'G3-minimal-relation', file:'_OnsetMinimalRelation', t:`THE MINIMAL NON-ANTIPODAL WRAPPING RELATION. A wrapping relation is a non-antipodal ±1 combination Σ ε_i ζ^{a_i} ≡ 0 (mod 𝔭), ε_i=±1, NOT a sum of {ζ,−ζ} pairs. Characterize the MINIMAL such (fewest terms / smallest support); its length = a lower bound on 2r_0. For 2-power roots, non-antipodal vanishing-mod-p relations: what is the minimal number of terms? Connect to the structure of Z[ζ_{2^μ}]/𝔭 ≅ F_{p^f} and the minimal F_p-linear dependence among {ζ^a mod 𝔭}. Build the minimal-relation object + the r_0 bound; honest.`},
  {id:'G4-weight-lowering', file:'_OnsetWeightLowering', t:`WEIGHT-LOWERING REALIZATION. _JacobiFermatCohomology found √p re-enters at weight 2r-1 of the correlation variety V_corr. Is there a DIFFERENT geometric/motivic realization of the SAME onset/W_r where the relevant Frobenius weight is LOWER (subgroup scale, ~log n)? Candidates: a quotient of V_corr by the (large) automorphism group (μ_n^r ⋊ S_r acts); the ISOTYPIC piece of H^{2r-1} for the trivial character (the invariants, much smaller weight); or a motive with smaller Hodge numbers. Compute whether the invariant/isotypic cohomology has weight < 2r-1 (escape) or still 2r-1 (same). Honest verdict on weight-lowering.`},
  {id:'G5-stickelberger-padic', file:'_OnsetStickelbergerPadic', t:`𝔭-ADIC STICKELBERGER STRUCTURE of the wraparound. The wrapping relations are 𝔭-DIVISIBLE; Stickelberger gives the exact 𝔭-adic valuation of Gauss/Jacobi sums (the Stickelberger element θ). Use the 𝔭-adic VALUATION (not the archimedean size) to constrain which short relations can be 𝔭-divisible: v_𝔭(Σε_i ζ^{a_i}) ≥ 1 is a strong p-adic condition. Does the Stickelberger/Gross–Koblitz valuation structure FORBID short non-antipodal wrapping relations (forcing r_0 large)? Build the 𝔭-adic valuation constraint + the r_0 consequence; honest verdict (forbids short wraps, or doesn't).`},
  {id:'G6-mollified-signed', file:'_OnsetMollifiedSigned', t:`MOLLIFIED / WEIGHTED SIGNED PERIOD. The raw off-diagonal is structured-not-cancelling. Build a SIGNED functional = a WEIGHTED moment Σ_b w(b)|η_b|^{2r} (or a smoothed/mollified period Σ_x φ(x)e_p(bx) with a cleverly-chosen mollifier φ supported near μ_n) whose off-diagonal genuinely cancels the structured wraparound. The mollifier is the new degree of freedom (Vinogradov/Selberg mollification adapted to the subgroup). Does a mollifier exist that kills the wraparound while preserving the diagonal? Build it; honest verdict (real cancellation, or the mollifier can't separate).`},
  {id:'G7-lattice-gap', file:'_OnsetLatticeGap', t:`THE ONSET AS A LATTICE SUCCESSIVE-MINIMA GAP. r_0 = the first r where the radius-r ball meets 𝔭∖(antipodal sublattice). The antipodal relations form a SUBLATTICE A ⊂ Z[ζ_n] (the {x,−x} span); wrapping = a 𝔭-point OUTSIDE A. So r_0 = the radius at which 𝔭 first leaves the antipodal sublattice A — a SUCCESSIVE-MINIMA / quotient-lattice question for 𝔭 in Z[ζ_n]/A. Compute the structure of Z[ζ_n]/A (the non-antipodal quotient) and the shortest 𝔭-image there. Does the quotient have large minimum (r_0 large)? Genuinely-new lattice reframing; honest verdict.`},
  {id:'G8-wild-buildoff', file:'_OnsetWildBuildoff', t:`WILD build-off: invent ONE more genuinely-new object grounded in the onset/GoN/no-wraparound learning that none of G1–G7 nor the prior campaign covers. Candidates: an L-function whose zeros encode the onset; a height/Mahler-measure bound on wrapping relations (the relation Σε_iζ^{a_i} has small Mahler measure ⟹ Lehmer-type lower bound on its norm ⟹ r_0 large); an entropy/additive-combinatorics bound on the wrapping-relation count; a dynamical (β-expansion / continued-fraction in Z[ζ_n]) characterization of r_0. Pick the most promising (the MAHLER MEASURE / Lehmer angle looks strong — a non-antipodal cyclotomic relation has Mahler measure bounded below, forcing its norm large, forcing r_0 large), build it, honest verdict.`},
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

BUILD ${T.id}. Create ${DIR}/${T.file}.lean. ${T.t}
Set boundsOnset=true only for a genuine machine-checked r_0 lower bound; CLOSED only for r_0>log p at prize scale.
Return mechanism + theNewClaim + verdict + full fileContent.`,
  {label:`build:${T.id}`, phase:'Build', effort:'high', schema:{...SCHEMA}}), 4, 'Build')

phase('Verify')
const toV = built.filter(r=>r.fileContent && (r.boundsOnset===true || r.outcome==='CLOSED' || r.outcome==='NEW_BOUND' || r.outcome==='PROMISING'))
const verified = toV.length ? await waved(toV, (r)=>agent(
  `${FRAME}

ADVERSARIALLY VERIFY ${r.id} (claims ${r.outcome}, boundsOnset=${r.boundsOnset}). Mechanism: ${(r.mechanism||'').slice(0,500)}.
Claim: ${(r.theNewClaim||'').slice(0,300)}. File: ${DIR}/${(r.file||'').split('/').pop()}. Break it: does the GoN/lattice
bound ACTUALLY beat the worst-case norm r_0≳p^{1/φ(n)} (which is too weak)? Does √p / the norm re-enter? Is the
shortest-vector / Mahler-measure bound genuinely better for 2-power cyclotomic 𝔭, or the same Minkowski bound? Re-run
pg-iterate, audit #print axioms. CLOSED/NEW_BOUND only if genuinely better + axiom-clean. Else REDUCES + exact flaw.
Return verdict + fileContent.`,
  {label:`vfy:${r.id}`, phase:'Verify', effort:'high', schema:{...SCHEMA}}), 4, 'Verify') : []

const vmap=new Map(verified.filter(Boolean).map(v=>[v.id,v]))
const fin=built.map(r=>vmap.get(r.id)||r)
const wins=fin.filter(r=>(r.outcome==='CLOSED'||r.outcome==='NEW_BOUND')&&r.boundsOnset===true&&r.axiomsClean===true)
const tally={}; for(const r of fin) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`buildoff-onset done: ${JSON.stringify(tally)} | wins: ${wins.length}`)
return { tally, winCount: wins.length,
  wins: wins.map(r=>({id:r.id, file:r.file, claim:r.theNewClaim, key:r.keyTheorem})),
  results: fin.map(r=>({id:r.id, outcome:r.outcome, boundsOnset:r.boundsOnset, genuinelyNew:r.genuinelyNew,
    axiomsClean:r.axiomsClean, file:r.file, mechanism:(r.mechanism||'').slice(0,200),
    theGapOrFlaw:(r.theGapOrFlaw||'').slice(0,300), finding:(r.summary||'').slice(0,300), fileContent:r.fileContent||''})) }
