export const meta = {
  name: 'bridge-unify',
  description: 'The unification question: the additive↔multiplicative bridge is tautological; is the JOINT structure (sum-product + explicit Gauss-phases) a non-tautological lever that reaches the prize, or does it definitively vanish at p^{0.19}? (#444)',
  phases: [
    { title: 'Joint',   detail: 'joint sum-product at exact prize params; explicit-Gauss-phase lever; joint-information hunt; bridge-asymmetry stress' },
    { title: 'Verify',  detail: 'adversarial audit' },
  ],
}
const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444 ($1M). The char-p energy bound (rEnergy(μ_n,r) ≤ (2r−1)‼·n^r over F_p at r≈ln p, n=2^30,
p≈n·2^128, n≈p^{0.19}) is caught in a TWO-OBSTRUCTION PINCER: (i) moment-necessity (must be cancellation not
count) + (ii) √p-vacuity (Weil sees √p≫n for thin μ_n). JUST PROVED (axiom-clean, _BridgeOneWall): the additive
energy E_r and the worst-case sup-norm M BRACKET each other within q−1 — the additive basis (count E_r, escapes
√p-vacuity) and the multiplicative basis (Gauss phases θ_χ=G(χ)/√p, escapes moment-necessity) are the SAME
object via the EXACT identity Σ_{b≠0}|η_b|^{2r}=q·E_r−n^{2r}. So the additive↔multiplicative bridge is
TAUTOLOGICAL (Parseval-dual; no info gain). The ONLY non-tautological combination is the JOINT
additive-multiplicative (sum-product) structure: bound the additive energy of a MULTIPLICATIVE subgroup using
BOTH structures at once (di Benedetto–Solymosi–White trilinear |X|^{3/4}|Y|^{3/4}|Z|^{7/8}, H^{1−31/2880}). That
is the SOTA — but it has a p^{1/4} tax and VANISHES at the prize thinness p^{0.19} < p^{1/4}.
KNOWN (don't rehash): generic sum-product, BGK n^{1−o(1)}, di Benedetto vanishes <p^{1/4}, HD/Stickelberger DOF
reduction stops at n/4 (still Θ(n) free Gauss phases ⟹ √n concentration but worst-case = BGK), HBK vacuous
<p^{1/3}, the Gauss-period equidistribution is fixed-d+distributional (literature sweep, 0 routes).
BUILD: scripts/pg-iterate.sh <file> (lock-free; READ #print axioms). autoImplicit OFF. Repo ${REPO}. MINIMAL imports.
HONESTY (PARAMOUNT): a fabricated proof wins nothing. CLOSED = genuine axiom-clean char-p proof. Default truth =
"the joint lever vanishes at the prize / reduces". Burden on the approach. Label honestly. RETURN full fileContent.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['CLOSED','PARTIAL','REDUCES','REFUTED','VANISHES','OBSTRUCTION','FAILED']},
    axiomsClean:{type:'boolean'}, closesCharP:{type:'boolean'}, reachesPrize:{type:'boolean'},
    finding:{type:'string'}, theNewClaim:{type:'string'}, theGapOrFlaw:{type:'string'},
    file:{type:'string'}, keyTheorem:{type:'string'}, fileContent:{type:'string'}, summary:{type:'string'} },
}

const ANGLES = [
  {id:'U1-joint-sumproduct', file:'_BridgeJointSumProduct', t:`THE JOINT SUM-PRODUCT at EXACT prize params. Survey EVERY known additive-energy-of-multiplicative-subgroup / sum-product bound (Bourgain–Glibichuk–Konyagin, di Benedetto–Solymosi–White, Petridis–Shparlinski, Shkredov higher-energy, Murphy–Rudnev, Konyagin–Shkredov, Macourt, Kerr, + any 2023–2026) and compute the EXACT exponent each gives for E_r(μ_n) / M at n=p^{0.19}, r≈log p. For each: the |H| threshold it needs, and the exponent at the prize. Is ANY non-vanishing at p^{0.19}? What is the precise threshold gap (each needs |H|>p^{?}, prize is p^{0.19})? Land a Lean brick recording the best joint exponent at the prize as a function of the sum-product input, with the named residual = the sum-product exponent that would close it. Honest: this is the SOTA frontier; quantify the exact gap.`},
  {id:'U2-joint-information', file:'_BridgeJointInformation', t:`THE JOINT-INFORMATION HUNT (the user's real question). Is there an invariant of the JOINT additive×multiplicative structure of μ_n — NOT visible in either the additive projection (E_r) or the multiplicative projection (Gauss phases) alone — that could close the bound? Candidates: (a) a "mixed energy" counting solutions to additive AND multiplicative relations simultaneously; (b) a Bourgain–Gamburd-style spectral gap of the COMBINED affine action (x↦ax+b) on F_p restricted to μ_n; (c) the additive energy of the GRAPH of the multiplication map; (d) a Larsen–Shalev / growth-in-groups invariant for the joint structure. For the most promising: define it, determine if it genuinely carries joint info beyond the two projections, and whether bounding it ⟹ the prize. Honest verdict: does joint info exist, or does every joint invariant factor through one projection (= tautological/reduces)?`},
  {id:'U3-bridge-asymmetry', file:'_BridgeAsymmetryStress', t:`STRESS the "tautological bridge". The bridge bracket (q·E_r−n^{2r})/(q−1) ≤ M^{2r} ≤ q·E_r−n^{2r} has a factor q−1≈p between the two sides. Is there an EXPLOITABLE asymmetry? (a) Does the energy→sup direction (averaging) lose something the sup→energy direction keeps, or vice versa? (b) Could a bound on a DIFFERENT moment (odd, fractional, or weighted) break the symmetry? (c) Is the factor q−1 ever improvable to o(p) using structure (so the average pins the worst case)? Determine HONESTLY whether the bridge is strictly tautological (no exploitable asymmetry — the q−1 factor is exactly the worst-case-vs-average gap that IS the problem) or whether some asymmetry is a genuine lever. Land the verdict + any brick.`},
  {id:'U4-explicit-gauss-phase', file:'_BridgeExplicitGaussPhase', t:`THE EXPLICIT-GAUSS-PHASE LEVER. Generic sum-product treats the Gauss phases θ_χ=G(χ)/√p as arbitrary; but they are STICKELBERGER-DETERMINED (the prime factorization of G(χ) in Z[ζ_n] is explicit; Gross–Koblitz gives G(χ) p-adically; Hasse–Davenport relates them). The HD+reflection relations cut the n Gauss-phase DOF to n/4 (Katz ceiling, in-tree issue407-hasse-davenport-dof-n4). THE QUESTION: does using the EXPLICIT phase arithmetic (beyond the n/4 DOF count) — e.g. a NEW Gauss-sum relation, or the p-adic Gross–Koblitz structure, or the Galois-module structure of the phases — force MORE cancellation than the generic n/4-DOF √n concentration, reaching below BGK at the prize? Build the explicit-phase object, state the new claim, honest verdict (likely the n/4 DOF is the wall — confirm or break).`},
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

phase('Joint')
const joint = await waved(ANGLES, (T)=>agent(
  `${FRAME}

ANGLE ${T.id}. Create ${DIR}/${T.file}.lean. ${T.t}
Set reachesPrize=true ONLY if a genuine non-vanishing-at-p^{0.19} lever is found; closesCharP only if a real
axiom-clean char-p proof. Return the verdict + full fileContent.`,
  {label:`joint:${T.id}`, phase:'Joint', effort:'high', schema:{...SCHEMA}}), 4, 'Joint')

phase('Verify')
const toV = joint.filter(r=>r.fileContent && (r.reachesPrize===true || r.closesCharP===true || r.outcome==='PARTIAL'))
const verified = toV.length ? await waved(toV, (r)=>agent(
  `${FRAME}

ADVERSARIALLY VERIFY ${r.id} (claims reachesPrize=${r.reachesPrize}, closesCharP=${r.closesCharP}). Claim:
${(r.theNewClaim||'').slice(0,400)}. Break it: does the joint lever ACTUALLY beat BGK at p^{0.19} (compute the
exponent), or does it secretly need |H|>p^{1/4} / reduce to a tautology / hide the sum-product exponent as the
open step? Re-run pg-iterate, audit axioms. Honest re-verdict + fileContent.`,
  {label:`vfy:${r.id}`, phase:'Verify', effort:'high', schema:{...SCHEMA}}), 3, 'Verify') : []

const vmap=new Map(verified.filter(Boolean).map(v=>[v.id,v]))
const fin=joint.map(r=>vmap.get(r.id)||r)
const reaches=fin.filter(r=>r.reachesPrize===true||r.closesCharP===true)
const tally={}; for(const r of fin) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`bridge-unify done: ${JSON.stringify(tally)} | reaches-prize: ${reaches.length}`)
return { tally, reachesCount: reaches.length,
  results: fin.map(r=>({id:r.id, outcome:r.outcome, reachesPrize:r.reachesPrize, closesCharP:r.closesCharP,
    axiomsClean:r.axiomsClean, file:r.file, theNewClaim:(r.theNewClaim||'').slice(0,200),
    theGapOrFlaw:(r.theGapOrFlaw||'').slice(0,300), finding:(r.finding||'').slice(0,450), fileContent:r.fileContent||''})) }
