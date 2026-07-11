export const meta = {
  name: 'verify-and-continue',
  description: 'Adversarially verify the equivariant-descent √p-removal claim (finite vs 1-dim group), re-run the failed thesis section (what-has-been-tried) and the conditional capstone (A3), and continue the attack (#444)',
  phases: [
    { title: 'Verify',   detail: 'ruthless adversarial check of the descent weight-drop + re-run failed thesis pieces' },
    { title: 'Continue', detail: 'if descent genuine push the induction; build the capstone' },
  ],
}
const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444 PhD thesis. A proof attempt (_EquivariantDescentWeightDrop, axiom-clean) CLAIMS the diagonal
μ_n-action g·(x,y)=(gx,gy) on the off-diagonal correlation, by a "free quotient by the 1-dimensional group μ_n",
drops the cohomological weight by 1 ⟹ removes the √p (residual exponent 1/2 → 0) on the nontrivial-winding part of
Off=Tr(Frob|H^{2r-1}(V_corr)). The brick proves: the action is free on nonzero roots (diag_action_free_on_nonzero),
the summand transforms by a linear character of the winding difference (summand_transforms_by_winding, the genuine
WINDING SPLIT Off=Σ_w Off_w), and the weight ARITHMETIC ((2r-2)/2−(r-1)=0). It NAMES residuals TrivialWindingClosure
(induction-on-r) + DescendedGrowingOrderControl. CONTEXT: _JacobiFermatCohomology proved √p re-enters at H^{2r-1}(V_corr)
weight 2r-1 (BGK in cohomology dress); _BridgeOneWall (additive=multiplicative); the open core = growing-order
Jacobi-pair equidistribution. HONESTY (PARAMOUNT): a claimed √p-removal must be RIGOROUSLY correct; do NOT rubber-stamp.
BUILD: scripts/pg-iterate.sh. autoImplicit OFF. Repo ${REPO}. RETURN findings/fileContent.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{ id:{type:'string'}, outcome:{type:'string', enum:['GENUINE','FLAWED','PARTIAL','DRAFTED','ADVANCED','REDUCES','FAILED']},
    axiomsClean:{type:'boolean'}, verdict:{type:'string'}, finding:{type:'string'}, file:{type:'string'}, fileContent:{type:'string'}, summary:{type:'string'} },
}

const TASKS = [
  {id:'V1-verify-descent', phase:'Verify', t:`ADVERSARIALLY VERIFY the _EquivariantDescentWeightDrop √p-removal claim — be RUTHLESS. THE DECISIVE QUESTION: μ_n = the n-th roots of unity is a FINITE group scheme of DIMENSION 0 (not 1-dimensional). A quotient of a variety by a FREE action of a FINITE group is an ÉTALE cover: it does NOT change the dimension, and the cohomology satisfies H^i(X)^χ ≅ H^i(X/G ⊗ ℒ_χ) at the SAME degree i — NO weight drop. The weight-drop-by-1 the brick claims requires a quotient by a POSITIVE-DIMENSIONAL group (Gm, dim 1), NOT the finite μ_n. So: (Q1) Is the brick CONFLATING the finite group μ_n (dim 0, étale quotient, gives only a factor-n combinatorial saving) with the 1-dim torus Gm (genuine dimension/weight drop)? (Q2) Does the diagonal μ_n-action actually give a √p (half-power-of-p) saving, or merely a factor-n combinatorial saving (which is NOT a half-power and does NOT touch the BGK exponent)? (Q3) Is "H^{2r-1}(V_corr)" even the right object — V_corr over the FINITE subgroup μ_n is a finite point set (dim 0, cohomology in degree 0 only), so the H^{2r-1} must refer to the Fermat hypersurface over the FIELD; does the finite μ_n-action even act on THAT with a weight drop? Resolve DEFINITIVELY: is the √p-removal GENUINE or FLAWED? If FLAWED, give the exact error (finite-vs-1-dim) and what the descent ACTUALLY gives (factor-n). If GENUINE, explain precisely why the finite-group objection fails. Build an axiom-clean Lean record of the verdict (the honest correction or confirmation). This determines whether the thesis's headline advance stands.`},
  {id:'S3-tried-wall', phase:'Verify', t:`Draft the THESIS SECTION "What Has Been Tried and Why It Hit the Wall" (the earlier attempt returned empty). Rigorous scholarly section: the TWO-OBSTRUCTION PINCER (moment-necessity: moment_ladder_exceeds_prize, must be cancellation not count; √p-vacuity: Weil gives √p≫n for thin μ_n, _FrontierSheafConductor); the dead-routes ledger (~100 directions: sum-product/di Benedetto vanishes at p^{0.19} needing p^{1/4}; modern tools decoupling/restriction/VMVT — μ_n flat 0-dim; the ~70-domain exhaustive loop; the ambitious meta-assault — even a signed Hankel determinant reduces; geometry of numbers — cyclotomic lattice too round, _OnsetMinimalRelation). For each KEY route give the PRECISE refutation mechanism (each a theorem). Then "what people said the next step would be" (Paley conjecture; effective growing-order Katz equidistribution; the BCHKS 1.12 char-sum cancellation). Return ~1800-2800 words polished prose in 'finding' (DRAFTED).`},
  {id:'A3-capstone', phase:'Continue', t:`Build the STRONGEST honest CONDITIONAL capstone Lean brick (_ThesisCapstone): the tightest end-to-end axiom-clean theorem reducing the prize to the single most credible named open hypothesis. Consolidate the chain: (sub-Poisson wraparound variance over the prime family) ⟹ [Chebyshev] (∃ good prime with W_r ≤ slack) ⟹ [energy bound] (E_r ≤ Wick at that prime) ⟹ [saddle, period_le_prizeFloor-style] (M ≤ prize floor). Build it SELF-CONTAINED (abstract over the prime family / variance, inline the saddle, like _ProveAssemblyConcrete) so it is axiom-clean (#print axioms ⊆ standard, no sorryAx). This is the thesis's central positive result: 'sub-Poisson variance ⟹ prize floor', machine-checked. Return the full fileContent + prose explaining the capstone.`},
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
phase('Verify')
const done = await waved(TASKS, (T)=>agent(`${FRAME}\n\nTASK ${T.id}. ${T.t}`,
  {label:T.id, phase:T.phase, effort:'high', schema:{...SCHEMA}}), 2, 'Run')

const tally={}; for(const r of done) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`verify-and-continue done: ${JSON.stringify(tally)}`)
return { tally, results: done.map(r=>({id:r.id, outcome:r.outcome, axiomsClean:r.axiomsClean, verdict:(r.verdict||'').slice(0,300),
  finding:r.finding||'', file:r.file, fileContent:r.fileContent||''})) }
