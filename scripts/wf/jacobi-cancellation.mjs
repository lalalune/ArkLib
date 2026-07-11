export const meta = {
  name: 'jacobi-cancellation',
  description: 'Push the NEW target: prove the off-diagonal Jacobi-phase cancellation (the √p-removed moment correlation) via Fermat-variety AG / Katz equidistribution / new Jacobi relations — or pin exactly where √p re-enters (#444)',
  phases: [
    { title: 'Attack',  detail: 'Fermat-variety cohomology, Katz equidistribution, new Jacobi relations, exact scales' },
    { title: 'Verify',  detail: 'adversarial: does it close, or does √p re-enter / reduce to BGK?' },
  ],
}
const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444 ($1M). NEW TARGET (just formalized, axiom-clean, _JacobiMomentIdentity + _JacobiCocycleDispersion):
the period's 2r-th moment is a UNIT-PHASE Jacobi correlation — Σ_b‖η_b‖^{2r} = (norm)·Σ_{Σx=Σy} Jphase(x)·conj(Jphase(y)),
where Jphase(x)=(∏θ(x_i))·conj(θ(Σx_i)) is a UNIT phase (θ=Gauss phase g(χ)/√p; the √p CANCELLED out of the whole
moment). DIAGONAL (Jphase(y)=Jphase(x)) → 1 = the Wick count = char-0 energy. The PRIZE ⟺
  OffDiagonalJacobiCancellation: |Σ_{Σx=Σy, off-diag} Jphase(x)conj(Jphase(y))| ≤ slack (square-root cancellation)
at depth r≈log m, for μ_n (n=2^30, 2-power), p≈n·2^128. The Jphase are normalized iterated JACOBI SUMS
j_r(χ)=J_r(χ_1,..,χ_r)/p^{(r-1)/2}; J_r are FROBENIUS EIGENVALUES of FERMAT-TYPE VARIETIES (x_1^n+..+x_r^n type /
the diagonal hypersurface), |J_r|=p^{(r-1)/2}. This is a CONCRETE algebraic-geometry object — strictly
better-structured than a raw character sum.
THE DECISIVE QUESTION: do the Fermat-variety AG tools (Deligne Weil-II on the Fermat hypersurface, Katz
equidistribution of Jacobi sums, the Gross-Koblitz/Hasse-Davenport relations for Jacobi sums) PROVE the
off-diagonal cancellation at the SUBGROUP scale √n at depth log m — OR does √p RE-ENTER (the Fermat variety is
over F_p, its Frobenius eigenvalues are p-power-scale; Katz equidistribution is fixed-order DISTRIBUTIONAL not
growing-order WORST-CASE)? Resolve this HONESTLY and precisely.
PRIOR (be aware, don't naively repeat): the additive↔multiplicative bridge is tautological (_BridgeOneWall);
generic sum-product vanishes at p^{0.19}; the raw period sheaf [n]_*L_ψ has √p eigenvalues (N7, √p-vacuity);
Katz Gauss-period equidistribution is fixed-d distributional (literature sweep). The NEW angle here is that the
JACOBI correlation (not the raw period) has Fermat-variety structure that MIGHT be exploitable where the period
wasn't — test this rigorously.
BUILD: scripts/pg-iterate.sh <file> (lock-free; READ #print axioms). autoImplicit OFF. Repo ${REPO}. MINIMAL imports.
HONESTY (PARAMOUNT): a fabricated proof wins nothing. CLOSED = genuine axiom-clean proof of the off-diagonal
cancellation. If √p re-enters on the Fermat variety, say EXACTLY where (which cohomology, which weight). If the
cancellation is genuinely provable, prove it. Default = "reduces / √p re-enters". Clobber-proof: RETURN full fileContent.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['CLOSED','PROMISING','REDUCES','VACUITY','REFUTED','PARTIAL','FAILED']},
    axiomsClean:{type:'boolean'}, closesCancellation:{type:'boolean'}, sqrtPReenters:{type:'boolean'},
    mechanism:{type:'string'}, theNewClaim:{type:'string'}, theGapOrFlaw:{type:'string'},
    file:{type:'string'}, keyTheorem:{type:'string'}, fileContent:{type:'string'}, summary:{type:'string'} },
}

const ANGLES = [
  {id:'J1-fermat-cohomology', file:'_JacobiFermatCohomology', t:`FERMAT-VARIETY COHOMOLOGY. The off-diagonal Jacobi correlation Σ_{Σx=Σy} Jphase(x)conj(Jphase(y)) is a trace over the cohomology of the Fermat-type variety whose Frobenius eigenvalues are the Jacobi sums J_r. Set up the EXACT variety (the diagonal hypersurface / Fermat hypersurface attached to depth r and the n-power), compute its dimension and the weight of the relevant H^i, and apply Deligne Weil-II. DECISIVE: is the resulting bound √n-scale (subgroup, escape) or √p-scale (field, √p re-enters)? The Jacobi sums |J_r|=p^{(r-1)/2} are field-scale — does the cohomological cancellation in the CORRELATION (Jphase·conj Jphase, where the p-powers cancel to unit) give subgroup scale, or does the variety's dimension reintroduce √p? Resolve precisely with the actual cohomology computation.`},
  {id:'J2-katz-equidist', file:'_JacobiKatzEquidist', t:`KATZ EQUIDISTRIBUTION of Jacobi sums at GROWING order. Katz proved Jacobi/Gauss sums equidistribute (Sato-Tate, vertical). The off-diagonal correlation is a sum of n^{2r-1} unit Jacobi phases; square-root cancellation needs equidistribution with an EFFECTIVE rate at order r≈log m. DECISIVE: is Katz's equidistribution rate strong enough at GROWING order r (not fixed)? Compute the exact discrepancy bound Katz gives and whether it beats the off-diagonal count. The literature sweep flagged "fixed-order distributional" — verify EXACTLY whether the growing-order quantitative version exists or is the open gap. If it's the open gap, name it precisely as the Jacobi-equidistribution-rate residual; if it closes, prove it.`},
  {id:'J3-jacobi-relations', file:'_JacobiNewRelations', t:`NEW JACOBI-SUM RELATIONS beyond Hasse-Davenport. The iterated Jacobi sums J_r(χ_1,..,χ_r) satisfy: HD for Jacobi sums, the recursion J_r = J(χ_1,χ_2)·J(χ_1χ_2,χ_3)·…, the Gross-Koblitz p-adic formula, prime-ideal factorization (Stickelberger). Do these relations cut the off-diagonal Jphase DOF below the generic, FORCING cancellation (analogous to the n/4 Gauss-DOF but for the CORRELATION)? Compute the free DOF of the off-diagonal Jacobi-phase system under all known Jacobi relations; is it o(count) (cancellation forced) or Θ(count) (the wall)? Build the DOF object + the consequence. Honest verdict.`},
  {id:'J4-exact-scales', file:'_JacobiExactScales', t:`EXACT SCALE ANALYSIS + numerics. Compute EXACTLY (small n=8,16,32, multi-prime, exact integer Jacobi sums): (a) the diagonal count (Wick, ~(2r-1)!!·n^r-scale); (b) the off-diagonal sum Σ Jphase(x)conj(Jphase(y)) — does it exhibit square-root cancellation (~n^{r-1/2}) or larger? (c) the ratio off-diag/diag at the relevant depth. Is the off-diagonal cancellation EMPIRICALLY TRUE (prize holds for this object)? What is the precise rate, and does it match what's needed at r≈log m? Build a probe (scripts/probes/) + an axiom-clean Lean brick recording the exact diagonal/off-diagonal scale relation. Decisive on whether the target is true and by what margin.`},
  {id:'J5-fermat-pointcount', file:'_JacobiFermatPointCount', t:`FERMAT-CURVE POINT-COUNT BRIDGE. The Jacobi sum J(χ,χ') = (Frobenius eigenvalue contribution to) the number of points on the Fermat curve x^n+y^n=1 over F_p (or the relevant superelliptic/diagonal curve). Bridge the off-diagonal Jacobi correlation to point-counts of an EXPLICIT family of Fermat-type curves/varieties, and use the Weil bound (genus·√p) on those. DECISIVE: does the genus of the relevant Fermat variety stay BOUNDED (giving a useful Weil bound at subgroup scale) or does it GROW with n/r (genus ~ n^2 for the degree-n Fermat curve → Weil bound n^2·√p, vacuous)? This is the crux of whether the AG route escapes or hits the same genus-growth √p-vacuity. Resolve with the exact genus computation.`},
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

phase('Attack')
const attacked = await waved(ANGLES, (T)=>agent(
  `${FRAME}

ATTACK ${T.id}. Create ${DIR}/${T.file}.lean. ${T.t}
Set closesCancellation=true ONLY for a genuine axiom-clean proof; sqrtPReenters=true if √p re-enters on the
Fermat variety. Return mechanism + theNewClaim + verdict + full fileContent.`,
  {label:`atk:${T.id}`, phase:'Attack', effort:'high', schema:{...SCHEMA}}), 5, 'Attack')

phase('Verify')
const toV = attacked.filter(r=>r.fileContent && (r.closesCancellation===true || r.outcome==='PROMISING' || r.outcome==='CLOSED'))
const verified = toV.length ? await waved(toV, (r)=>agent(
  `${FRAME}

ADVERSARIALLY VERIFY ${r.id} (claims outcome ${r.outcome}, closesCancellation=${r.closesCancellation}). Mechanism:
${(r.mechanism||'').slice(0,500)}. Claim: ${(r.theNewClaim||'').slice(0,300)}. File: ${DIR}/${(r.file||'').split('/').pop()}.
Break it: does √p re-enter (Fermat genus/dimension growth)? Is Katz's rate actually strong enough at growing
order, or is that the open gap? Re-run pg-iterate, audit #print axioms (sorryAx/native_decide/vacuous hyp?).
CLOSED only if it genuinely proves the off-diagonal cancellation axiom-clean. Else VACUITY/REDUCES + exact flaw.
Return verdict + fileContent.`,
  {label:`vfy:${r.id}`, phase:'Verify', effort:'high', schema:{...SCHEMA}}), 3, 'Verify') : []

const vmap=new Map(verified.filter(Boolean).map(v=>[v.id,v]))
const fin=attacked.map(r=>vmap.get(r.id)||r)
const closed=fin.filter(r=>r.outcome==='CLOSED'&&r.closesCancellation===true&&r.axiomsClean===true)
const tally={}; for(const r of fin) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`jacobi-cancellation done: ${JSON.stringify(tally)} | CLOSED: ${closed.length}`)
return { tally, closedCount: closed.length,
  closed: closed.map(r=>({id:r.id, file:r.file, claim:r.theNewClaim, key:r.keyTheorem})),
  results: fin.map(r=>({id:r.id, outcome:r.outcome, closesCancellation:r.closesCancellation, sqrtPReenters:r.sqrtPReenters,
    axiomsClean:r.axiomsClean, file:r.file, mechanism:(r.mechanism||'').slice(0,200),
    theGapOrFlaw:(r.theGapOrFlaw||'').slice(0,300), finding:(r.finding||r.summary||'').slice(0,400), fileContent:r.fileContent||''})) }
