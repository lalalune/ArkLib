export const meta = {
  name: 'deltastar-bridge-grind',
  description: 'Grind 50 bridge attempts from proven substrate up to the empirical δ* formulas (#444)',
  phases: [
    { title: 'Attempt', detail: 'one agent per bridge spec: Lean brick or honest reduction' },
    { title: 'Verify', detail: 'adversarial axiom-audit of every LANDED claim' },
    { title: 'Synthesize', detail: 'collect survivors, write grind log' },
  ],
}

// ---- The 50 bridge specs: proven substrate ==> empirical formula E1..E7 ----
// Each: id, target, claim (the lemma to prove), approach, substrate (in-tree files to import).
const SPECS = [
  // E1 master gap identity (tractable)
  {id:'B01',t:'E1',claim:'deltaStar = 1 - rho - (m*-1)/n from the OpenCoreConverse budget-crossing pin and the def of m*',approach:'unwind deltaStar_iff_incidence_budget + def m*=s*-k, k=rho*n; ℚ algebra',sub:'OpenCoreConverse'},
  {id:'B02',t:'E1',claim:'deltaStar > Johnson (1-sqrt rho) <-> m* < (sqrt rho - rho)*n + 1',approach:'ℝ/ℚ inequality from E1; no analysis',sub:'OpenCoreConverse'},
  {id:'B03',t:'E1',claim:'binding depth m* >= 1 (full agreement at s=k saturates, incidence infinite/over budget)',approach:'at s=k the system is not over-determined, every gamma agrees; D*(k)>budget',sub:'OpenCoreConverse'},
  {id:'B04',t:'E1',claim:'capacity - deltaStar = (m*-1)/n as an exact rational identity',approach:'rearrange E1',sub:'OpenCoreConverse'},
  // E6 FFT-graded exact recursion (high value)
  {id:'B05',t:'E6',claim:'odd-graded #bad_{2n}(k,m)=0 for odd m via the antipodal involution -1 in mu_{2n}',approach:'pair x with -x in mu_{2n}; odd graded frequency vector is antisymmetric, sums to 0',sub:'DyadicTowerRecursion'},
  {id:'B06',t:'E6',claim:'the doubling map Z/2n->Z/n on (k+2m\')-subsets preserves the graded frequency vector',approach:'a |-> a mod n folds bins; show fhat invariant on the zero-lower-graded locus',sub:'DyadicTowerRecursion'},
  {id:'B07',t:'E6',claim:'#bad_{2n}(k,2m\') = #bad_n(k/2,m\') (the full graded recursion, even m)',approach:'bijection of distinct graded vectors under doubling; the hard one',sub:'DyadicTowerRecursion'},
  {id:'B08',t:'E6',claim:'graded frequency-vector bin index halves under doubling (j*a mod 2n binned mod n)',approach:'arithmetic of residues under a|->2a',sub:'DyadicTowerRecursion'},
  {id:'B09',t:'E6',claim:'bridge eta-parallelogram (DyadicTowerRecursion) to the even-only graded count',approach:'eta_b^{(mu)}=eta_b^{(mu-1)}+eta_{b w}^{(mu-1)}; odd part cancels',sub:'DyadicTowerRecursion'},
  {id:'B10',t:'E6',claim:'even-tau-exactness: sum_{x in mu_{2n}} x^{odd}*(graded indicator) = 0',approach:'geometric sum over full subgroup of a nonzero power = 0',sub:'DyadicTowerRecursion'},
  // E3 orbit closed form / partial orbit
  {id:'B11',t:'E3',claim:'bad-gamma set is closed under gamma |-> gamma*h^{b-a} (orbit closure)',approach:'multiply the line word by h^{b-a}; RS-agreement set is dilation-stable',sub:'OrbitCountCrossingLaw'},
  {id:'B12',t:'E3',claim:'z in {0,1}: the fixed point gamma=0 contributes at most 1 to the count',approach:'gamma=0 is the only fixed point of the dilation; membership is a single boolean',sub:'OrbitCountCrossingLaw'},
  {id:'B13',t:'E3',claim:'nonzero orbit size S = n/gcd(b-a,n)',approach:'order of h^{b-a} in mu_n',sub:'OrbitCountCrossingLaw'},
  {id:'B14',t:'E3',claim:'crossing law D<=n <-> O<=gcd(b-a,n) at budget=n (instantiate P3)',approach:'apply crossing_law with S*d=n',sub:'OrbitCountCrossingLaw'},
  {id:'B15',t:'E3',claim:'at a primitive binder (d=1) the binding count D=z+(proper sub-orbit count), not a full multiple of S',approach:'characterize partial orbit: agreement set is not full dilation orbit at the crossing radius',sub:'OrbitCountCrossingLaw'},
  {id:'B16',t:'E3',claim:'primitive binder (gcd(b-a,n)=1) forces the hard constraint O<=1',approach:'d=1 in crossing law',sub:'OrbitCountCrossingLaw'},
  {id:'B17',t:'E3',claim:'orbit-closed => D-z is divisible by S (integrality of O)',approach:'orbit partition of the nonzero bad set into size-S blocks',sub:'OrbitCountCrossingLaw'},
  // E4 leading value / decay
  {id:'B18',t:'E4',claim:'k-th divided difference DD_k(x^a) over nodes T equals complete homogeneous symmetric h_{a-k}(T)',approach:'classical: divided difference of monomial = complete homogeneous symmetric poly',sub:'IncidencePeriodBridge'},
  {id:'B19',t:'E4',claim:'D*(1) = #distinct values of -h_{a-k}(T)/h_{b-k}(T) over (k+1)-subsets T of mu_n',approach:'gamma is forced by single-window DD ratio; count distinct',sub:'IncidencePeriodBridge'},
  {id:'B20',t:'E4',claim:'D*(1) <= C(n,k+1) (each (k+1)-subset yields at most one bad gamma)',approach:'map subset -> gamma, image-size bound',sub:'IncidencePeriodBridge'},
  {id:'B21',t:'E4',claim:'the over-det agreement condition is linear (affine) in gamma per window',approach:'DD_k(u0+gamma u1)=DD_k(u0)+gamma DD_k(u1)=0',sub:'IncidencePeriodBridge'},
  {id:'B22',t:'E4',claim:'m windows of constraints cut the bad-gamma set: D*(m) <= count of gamma solving m ratio equations',approach:'intersection of affine conditions; codimension count',sub:'IncidencePeriodBridge'},
  {id:'B23',t:'E4',claim:'D* is non-increasing and drops by a factor>1 per step in the measured regime',approach:'monotonicity (B48) + measured ratios; state the factor as a hypothesis if not provable',sub:'IncidencePeriodBridge'},
  {id:'B24',t:'E4',claim:'D*(1) closed form ~ (n/2-1)^2 over-det edge value (cyclotomic ratio count)',approach:'the n^3/S leading behavior; reduce to a cyclotomic distinct-ratio count',sub:'IncidencePeriodBridge'},
  // E5 dyadic cascade (partial recursion)
  {id:'B25',t:'E5',claim:'one-sided lift D*_{2n}(m) <= D*_n(m-1) + (plateau term)',approach:'doubling embeds level-n bad set into level-2n; bound the new contributions',sub:'OrbitCountCrossingLaw'},
  {id:'B26',t:'E5',claim:'primitive directions satisfy the clean recursion D*_{2n}(m)=D*_n(m-1) (no plateau)',approach:'gcd(b-a,2n)=1 forces clean descent',sub:'OrbitCountCrossingLaw'},
  {id:'B27',t:'E5',claim:'plateau-doubling occurs only at imprimitive (b-a even) directions',approach:'even b-a => h^{b-a} has a fixed mu_2; extra invariant rung',sub:'OrbitCountCrossingLaw'},
  {id:'B28',t:'E5',claim:'IF plateau excess per tower level is O(1) THEN m*=O(log n) (conditional brick)',approach:'state plateau-excess<=c as hypothesis; induct m*(2n)<=m*(n)+1+c',sub:'OrbitCountCrossingLaw'},
  {id:'B29',t:'E5',claim:'m*(2n) <= m*(n)+1 conditional on the clean recursion holding at the binder',approach:'budget doubles, cascade shifts by 1',sub:'OrbitCountCrossingLaw'},
  {id:'B30',t:'E5',claim:'net m* increment per doubling <= plateau width at the binding value',approach:'crossing-radius bookkeeping',sub:'OrbitCountCrossingLaw'},
  // E7 prize reductions
  {id:'B31',t:'E7',claim:'m*=O(log n) <-> BCHKS Conjecture 1.12 (distinct r-fold subset-sum |Sigma_r(mu_s)|<=q eps* at r~log m): name the reduction',approach:'identify D*(m) with the distinct r-fold subset-sum count; state the equivalence as a Prop',sub:'OpenCoreConverse'},
  {id:'B32',t:'E7',claim:'m*=o(n) => deltaStar -> capacity - c_rho (bridge E1 to upper bracket P5)',approach:'combine E1 with DeltaStarConstantGapBelowCapacity',sub:'OpenCoreConverse'},
  {id:'B33',t:'E7',claim:'D*(m) equals the distinct r-fold subset-sum count of mu_s at r=m (object identity)',approach:'unfold both definitions; show same Finset.card',sub:'OpenCoreConverse'},
  // cross-cutting glue
  {id:'B34',t:'X',claim:'at the binding crossing s* the monomial far direction achieves the max incidence (binding is monomial-controlled)',approach:'period-sum P2 at far line; non-monomial decays below by the crossing (dirworst empirical) - attempt or reduce',sub:'IncidencePeriodBridge'},
  {id:'B35',t:'X',claim:'antipodal pairing kills odd graded moments: sum over mu_{2n} of an odd-degree graded weight = 0',approach:'-1 involution',sub:'DyadicTowerRecursion'},
  {id:'B36',t:'X',claim:'divided-difference vanishing on s points <-> the word interpolates a degree<k polynomial (RS membership)',approach:'definitional bridge DD_k=0 iff in RS',sub:'IncidencePeriodBridge'},
  {id:'B37',t:'X',claim:'far-line incidence equals the period sum (strengthen/re-derive P2 cleanly)',approach:'IncidencePeriodBridge.lineIncidence_period_sum',sub:'IncidencePeriodBridge'},
  {id:'B38',t:'X',claim:'lower bound: D*(m) > budget for m < m* (the bad side of the crossing) - Johnson floor witness',approach:'monomial witness x^{n/2} gives incidence > n below binding',sub:'OpenCoreConverse'},
  {id:'B39',t:'X',claim:'eps_mca >= incidence/q (the inequality linking MCA error to far-line incidence)',approach:'count bad lines / total',sub:'OpenCoreConverse'},
  {id:'B40',t:'X',claim:'worstCase Lambda^2 = max_b ||eta_b||^2 ties to D* via the period sum',approach:'P2 + PrizeStructuralConstant if present',sub:'IncidencePeriodBridge'},
  // E6/E3 depth
  {id:'B41',t:'E6',claim:'#bad support max depth m equals k (linear) via 2-adic descent',approach:'iterate the recursion until k halves to odd; support cutoff',sub:'DyadicTowerRecursion'},
  {id:'B42',t:'E6',claim:'v_2(m) controls the FFT-recursion descent depth',approach:'each descent step halves m and k; stops at odd m',sub:'DyadicTowerRecursion'},
  {id:'B43',t:'E6',claim:'base cases #bad_4(1,1) and #bad_4(1,2) are explicit finite values',approach:'decide/Finset.card on mu_4 (n=4, small, kernel-feasible)',sub:'DyadicTowerRecursion'},
  {id:'B44',t:'E6',claim:'fhat odd-vanishing expressed as a character sum over mu_{2n} that is identically 0',approach:'orthogonality of characters',sub:'DyadicTowerRecursion'},
  {id:'B45',t:'E3',claim:'over-det edge orbit count O(m=1) = (n/2 - 1) closed form',approach:'count nonzero orbits at the edge; cyclotomic',sub:'OrbitCountCrossingLaw'},
  // foundations
  {id:'B46',t:'E1',claim:'m* is well-defined: the set {m: D*(k+m)<=budget} is nonempty (min exists)',approach:'D*(n) trivial: at s=n only RS words, finite/=1<=budget',sub:'OpenCoreConverse'},
  {id:'B47',t:'E4',claim:'cascade tail: D*(n-k)=1 (full over-determination leaves only the trivial gamma)',approach:'s=n forces the word in RS; single solution',sub:'IncidencePeriodBridge'},
  {id:'B48',t:'E4',claim:'D* is monotone non-increasing in m (more agreement points => fewer bad gamma)',approach:'agreement on s+1 pts implies agreement on s pts: subset of bad set',sub:'IncidencePeriodBridge'},
  {id:'B49',t:'X',claim:'budget = q*eps* and at prize params equals ~n (state exactly)',approach:'q=n^beta, eps*=2^-128, q*eps*; the floor(q*eps*) value',sub:'OpenCoreConverse'},
  {id:'B50',t:'E7',claim:'ASSEMBLY: deltaStar in (Johnson,capacity) follows from {B48 monotone, B47 tail, m*<k}',approach:'combine the landed bricks; state the precise remaining hypothesis (m*<k)',sub:'OpenCoreConverse'},
]

const ATTEMPT_SCHEMA = {
  type:'object', additionalProperties:false,
  required:['id','target','status','summary'],
  properties:{
    id:{type:'string'},
    target:{type:'string'},
    status:{type:'string', enum:['LANDED','REDUCED','FAILED']},
    file:{type:'string', description:'path to the Lean file written (or empty)'},
    axioms:{type:'string', description:'the #print axioms output, or empty'},
    gap:{type:'string', description:'for REDUCED: the exact remaining named hypothesis; for FAILED: the obstruction'},
    summary:{type:'string', description:'one-paragraph honest account of what was proven and what was not'},
  },
}

const VERDICT_SCHEMA = {
  type:'object', additionalProperties:false,
  required:['id','confirmed','reason'],
  properties:{
    id:{type:'string'},
    confirmed:{type:'boolean', description:'true iff the LANDED claim genuinely builds axiom-clean with no sorry/fake-axiom'},
    reason:{type:'string'},
  },
}

const guide = `You are proving a BRIDGE lemma in the ArkLib Lean 4 Proximity-Gap cone (#444), working dir
/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib.
GOAL: build from proven substrate UP TO an empirical formula that pins delta*.
Read first (do not skip):
 - docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md  (the E1..E7 targets + P1..P6 anchors)
 - ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md (build rules)
 - the substrate file(s) named in your spec, under ArkLib/Data/CodingTheory/ProximityGap/
HONESTY CONTRACT (paramount):
 - Write your lemma in a NEW file ArkLib/Data/CodingTheory/ProximityGap/Frontier/_Bridge<ID>.lean,
   importing ONLY the minimal substrate modules you consume (fast lock-free build).
 - Build/check with:  scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_Bridge<ID>.lean
 - status=LANDED ONLY IF: it elaborates with NO errors, NO 'sorry', NO fake 'axiom', and the
   axiom audit shows the print-axioms set is a SUBSET of {propext, Classical.choice, Quot.sound}.
   Paste the actual #print axioms output into the 'axioms' field. If you cannot show this, it is NOT landed.
 - If you can prove it only modulo a hypothesis, status=REDUCED and state that hypothesis PRECISELY
   as a named Prop in 'gap' (it is fine to 'variable (h : <Prop>)' and use it - that is an honest reduction).
 - If it resists, status=FAILED and name the concrete obstruction in 'gap'.
 - NEVER claim LANDED without the build+axiom evidence. Fabrication is the worst outcome.
 - Keep the file minimal. autoImplicit=false. Do not edit ArkLib.lean (pg-iterate does not need it).
 - If your spec's claim is FALSE or ill-posed, say so (FAILED) with the counter-reason - that is valuable.
Your spec is below. Return the structured result.`

phase('Attempt')
// Throttle-safe: run in WAVES of 6 (barrier between waves) so peak concurrency stays low
// and the server-side rate limiter is not tripped by a 50-way fan-out.
function chunk(arr, n){ const out=[]; for(let i=0;i<arr.length;i+=n) out.push(arr.slice(i,i+n)); return out }
const WAVES = chunk(SPECS, 6)
let attempts = []
for (let w=0; w<WAVES.length; w++){
  log(`wave ${w+1}/${WAVES.length} (${WAVES[w].map(s=>s.id).join(',')})`)
  const waveRes = await pipeline(
  WAVES[w],
  (spec) => agent(
    `${guide}\n\nSPEC ${spec.id} [target ${spec.t}]\nCLAIM: ${spec.claim}\nAPPROACH: ${spec.approach}\nSUBSTRATE: ${spec.sub}.lean`,
    {label:`bridge:${spec.id}`, phase:'Attempt', schema:ATTEMPT_SCHEMA}
  ),
  // Verify LANDED claims adversarially as soon as each attempt returns
  (res, spec) => {
    if (!res || res.status !== 'LANDED') return res
    return agent(
      `Adversarially VERIFY a LANDED bridge brick in the ArkLib Proximity-Gap cone. Working dir
/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib.
File: ${res.file}
Claim: ${spec.claim}
Re-run:  scripts/pg-iterate.sh -q ${res.file}
Then independently audit axioms (open the file, check for 'sorry', any 'axiom' decl, and run the
#print axioms on the main theorem). confirmed=true ONLY IF it builds with zero errors, zero sorry,
no fabricated axiom, and print-axioms subset of {propext, Classical.choice, Quot.sound}, AND the
theorem statement actually matches the claimed bridge (not a trivially weakened restatement).
Be skeptical: a brick that imports nothing and proves a tautology is NOT a confirmed bridge.`,
      {label:`verify:${spec.id}`, phase:'Verify', schema:VERDICT_SCHEMA}
    ).then(v => ({...res, verdict:v}))
  }
  )
  attempts = attempts.concat(waveRes)
}

phase('Synthesize')
const done = attempts.filter(Boolean)
const landed = done.filter(r => r.status==='LANDED' && r.verdict?.confirmed)
const landedUnverified = done.filter(r => r.status==='LANDED' && !r.verdict?.confirmed)
const reduced = done.filter(r => r.status==='REDUCED')
const failed = done.filter(r => r.status==='FAILED')
log(`Bridge grind complete: ${landed.length} LANDED(verified), ${landedUnverified.length} LANDED(unverified/refuted), ${reduced.length} REDUCED, ${failed.length} FAILED of ${done.length}`)

return {
  counts:{landed:landed.length, landedUnverified:landedUnverified.length, reduced:reduced.length, failed:failed.length, total:done.length},
  landed: landed.map(r=>({id:r.id, target:r.target, file:r.file, summary:r.summary, axioms:r.axioms})),
  landedRefuted: landedUnverified.map(r=>({id:r.id, file:r.file, why:r.verdict?.reason})),
  reduced: reduced.map(r=>({id:r.id, target:r.target, gap:r.gap, summary:r.summary})),
  failed: failed.map(r=>({id:r.id, target:r.target, gap:r.gap})),
}
