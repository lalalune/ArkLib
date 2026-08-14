export const meta = {
  name: 'deltastar-bridge-grind-v2',
  description: 'Audit+repair existing bridge bricks and grind the remaining δ* bridge specs (#444)',
  phases: [
    { title: 'Audit', detail: 'verify/repair the 16 existing _BridgeB* files; classify by real axioms' },
    { title: 'Grind', detail: 'fresh attempts at the 34 un-attempted specs (B15, B18-B50)' },
    { title: 'Verify', detail: 'adversarial axiom + faithfulness re-audit of every CLEAN claim' },
    { title: 'Synthesize', detail: 'grind log of genuine axiom-clean bricks' },
  ],
}

const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const ALLOWED = '{propext, Classical.choice, Quot.sound}'

// all 50 specs (id, target, claim, approach, substrate)
const SPECS = [
  {id:'B01',t:'E1',claim:'deltaStar = 1 - rho - (m*-1)/n from OpenCoreConverse budget-crossing + def m*',sub:'OpenCoreConverse'},
  {id:'B02',t:'E1',claim:'deltaStar > Johnson (1-sqrt rho) <-> m* < (sqrt rho - rho)*n + 1',sub:'OpenCoreConverse'},
  {id:'B03',t:'E1',claim:'binding depth m* >= 1 (full agreement at s=k saturates, over budget)',sub:'OpenCoreConverse'},
  {id:'B04',t:'E1',claim:'capacity - deltaStar = (m*-1)/n exact rational identity',sub:'OpenCoreConverse'},
  {id:'B05',t:'E6',claim:'odd-graded #bad_{2n}(k,m)=0 for odd m via antipodal involution -1 in mu_{2n}',sub:'DyadicTowerRecursion'},
  {id:'B06',t:'E6',claim:'doubling map Z/2n->Z/n on (k+2m\')-subsets preserves graded frequency vector',sub:'DyadicTowerRecursion'},
  {id:'B07',t:'E6',claim:'#bad_{2n}(k,2m\') = #bad_n(k/2,m\') (full graded recursion, even m)',sub:'DyadicTowerRecursion'},
  {id:'B08',t:'E6',claim:'graded frequency-vector bin index halves under doubling',sub:'DyadicTowerRecursion'},
  {id:'B09',t:'E6',claim:'bridge eta-parallelogram (DyadicTowerRecursion) to even-only graded count',sub:'DyadicTowerRecursion'},
  {id:'B10',t:'E6',claim:'even-tau-exactness: sum_{x in mu_{2n}} x^{odd}*(graded indicator) = 0',sub:'DyadicTowerRecursion'},
  {id:'B11',t:'E3',claim:'bad-gamma set closed under gamma|->gamma*h^{b-a} (orbit closure)',sub:'OrbitCountCrossingLaw'},
  {id:'B12',t:'E3',claim:'z in {0,1}: fixed point gamma=0 contributes at most 1',sub:'OrbitCountCrossingLaw'},
  {id:'B13',t:'E3',claim:'nonzero orbit size S = n/gcd(b-a,n)',sub:'OrbitCountCrossingLaw'},
  {id:'B14',t:'E3',claim:'crossing law D<=n <-> O<=gcd(b-a,n) at budget=n (instantiate P3)',sub:'OrbitCountCrossingLaw'},
  {id:'B15',t:'E3',claim:'at a primitive binder (d=1) binding D=z+(proper sub-orbit count), not full multiple of S',sub:'OrbitCountCrossingLaw'},
  {id:'B16',t:'E3',claim:'primitive binder (gcd(b-a,n)=1) forces O<=1',sub:'OrbitCountCrossingLaw'},
  {id:'B17',t:'E3',claim:'orbit-closed => D-z divisible by S (integrality of O)',sub:'OrbitCountCrossingLaw'},
  {id:'B18',t:'E4',claim:'k-th divided difference DD_k(x^a) over nodes T = complete homogeneous symmetric h_{a-k}(T)',sub:'IncidencePeriodBridge'},
  {id:'B19',t:'E4',claim:'D*(1) = #distinct values of -h_{a-k}(T)/h_{b-k}(T) over (k+1)-subsets T of mu_n',sub:'IncidencePeriodBridge'},
  {id:'B20',t:'E4',claim:'D*(1) <= C(n,k+1) (each (k+1)-subset yields at most one bad gamma)',sub:'IncidencePeriodBridge'},
  {id:'B21',t:'E4',claim:'over-det agreement condition is affine in gamma per window',sub:'IncidencePeriodBridge'},
  {id:'B22',t:'E4',claim:'m windows cut bad-gamma: D*(m) <= count of gamma solving m ratio equations',sub:'IncidencePeriodBridge'},
  {id:'B23',t:'E4',claim:'D* non-increasing and drops by factor>1 per step in measured regime',sub:'IncidencePeriodBridge'},
  {id:'B24',t:'E4',claim:'D*(1) closed form ~ (n/2-1)^2 over-det edge value',sub:'IncidencePeriodBridge'},
  {id:'B25',t:'E5',claim:'one-sided lift D*_{2n}(m) <= D*_n(m-1) + plateau term',sub:'OrbitCountCrossingLaw'},
  {id:'B26',t:'E5',claim:'primitive directions satisfy clean recursion D*_{2n}(m)=D*_n(m-1)',sub:'OrbitCountCrossingLaw'},
  {id:'B27',t:'E5',claim:'plateau-doubling only at imprimitive (b-a even) directions',sub:'OrbitCountCrossingLaw'},
  {id:'B28',t:'E5',claim:'IF plateau excess per tower level is O(1) THEN m*=O(log n) (conditional brick)',sub:'OrbitCountCrossingLaw'},
  {id:'B29',t:'E5',claim:'m*(2n) <= m*(n)+1 conditional on clean recursion at binder',sub:'OrbitCountCrossingLaw'},
  {id:'B30',t:'E5',claim:'net m* increment per doubling <= plateau width at binding value',sub:'OrbitCountCrossingLaw'},
  {id:'B31',t:'E7',claim:'m*=O(log n) <-> BCHKS 1.12 (distinct r-fold subset-sum |Sigma_r(mu_s)|<=q eps* at r~log m): name reduction',sub:'OpenCoreConverse'},
  {id:'B32',t:'E7',claim:'m*=o(n) => deltaStar -> capacity - c_rho (bridge E1 to upper bracket P5)',sub:'OpenCoreConverse'},
  {id:'B33',t:'E7',claim:'D*(m) equals distinct r-fold subset-sum count of mu_s at r=m (object identity)',sub:'OpenCoreConverse'},
  {id:'B34',t:'X',claim:'at binding crossing s* monomial far dir achieves max incidence (monomial-controlled)',sub:'IncidencePeriodBridge'},
  {id:'B35',t:'X',claim:'antipodal pairing kills odd graded moments: sum over mu_{2n} of odd-degree graded weight = 0',sub:'DyadicTowerRecursion'},
  {id:'B36',t:'X',claim:'divided-difference vanishing on s points <-> word interpolates degree<k poly (RS membership)',sub:'IncidencePeriodBridge'},
  {id:'B37',t:'X',claim:'far-line incidence equals period sum (strengthen P2)',sub:'IncidencePeriodBridge'},
  {id:'B38',t:'X',claim:'lower bound D*(m) > budget for m < m* (bad side of crossing) - Johnson floor witness',sub:'OpenCoreConverse'},
  {id:'B39',t:'X',claim:'eps_mca >= incidence/q (link MCA error to far-line incidence) - consume FarCosetExplosion',sub:'OpenCoreConverse'},
  {id:'B40',t:'X',claim:'worstCase Lambda^2 = max_b ||eta_b||^2 ties to D* via period sum',sub:'IncidencePeriodBridge'},
  {id:'B41',t:'E6',claim:'#bad support max depth m equals k (linear) via 2-adic descent',sub:'DyadicTowerRecursion'},
  {id:'B42',t:'E6',claim:'v_2(m) controls FFT-recursion descent depth',sub:'DyadicTowerRecursion'},
  {id:'B43',t:'E6',claim:'base cases #bad_4(1,1) and #bad_4(1,2) explicit finite values (define fhat in Lean, decide)',sub:'DyadicTowerRecursion'},
  {id:'B44',t:'E6',claim:'fhat odd-vanishing as a character sum over mu_{2n} identically 0',sub:'DyadicTowerRecursion'},
  {id:'B45',t:'E3',claim:'over-det edge orbit count O(m=1) = (n/2-1) closed form',sub:'OrbitCountCrossingLaw'},
  {id:'B46',t:'E1',claim:'m* well-defined: {m: D*(k+m)<=budget} nonempty (min exists)',sub:'OpenCoreConverse'},
  {id:'B47',t:'E4',claim:'cascade tail D*(n-k)=1 (full over-determination leaves only trivial gamma)',sub:'IncidencePeriodBridge'},
  {id:'B48',t:'E4',claim:'D* monotone non-increasing in m (agreement on s+1 pts => subset of bad set on s)',sub:'IncidencePeriodBridge'},
  {id:'B49',t:'X',claim:'budget = q*eps* and at prize params = ~n (state exactly)',sub:'OpenCoreConverse'},
  {id:'B50',t:'E7',claim:'ASSEMBLY: deltaStar in (Johnson,capacity) from {B48 monotone, B47 tail, m*<k}',sub:'OpenCoreConverse'},
]

const EXISTING = new Set(['B01','B02','B03','B04','B05','B06','B07','B08','B09','B10','B11','B12','B13','B14','B16','B17'])

const VERDICT = {
  type:'object', additionalProperties:false,
  required:['id','status','axiomsClean','summary'],
  properties:{
    id:{type:'string'},
    status:{type:'string', enum:['CLEAN_LANDED','SORRY_STUBBED','VACUOUS','REDUCED','BROKEN','FAILED']},
    axiomsClean:{type:'boolean', description:'true iff main theorem print-axioms subset of allowed AND no sorry/admit/native_decide/fake-axiom'},
    file:{type:'string'},
    keyTheorem:{type:'string', description:'name of the main bridge theorem'},
    axioms:{type:'string', description:'verbatim #print axioms output for the key theorem'},
    gap:{type:'string', description:'for REDUCED: exact remaining named hypothesis; for others: the issue'},
    summary:{type:'string'},
  },
}

const HONESTY = `HONESTY CONTRACT (paramount, per ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md §6):
- A brick is CLEAN_LANDED only if: it elaborates with NO error, contains NO 'sorry'/'admit'/
  'native_decide'/fabricated 'axiom' (a 'sorry' in a docstring sentence like "no sorry" does NOT
  count - check for an ACTUAL sorry term), and '#print axioms <keyThm>' prints a set that is a
  SUBSET of ${ALLOWED}. Paste the verbatim #print axioms output into 'axioms'.
- If the statement is a tautology / has a vacuous (False / unsatisfiable) hypothesis / is a trivial
  restatement that does NOT actually bridge proven math to the claimed empirical formula => VACUOUS.
- A genuine reduction (proves the target MODULO an explicitly named Prop hypothesis via 'variable
  (h : <Prop>)') is REDUCED, not VACUOUS - that is honest and valuable. State the Prop in 'gap'.
- pg-iterate.sh treats 'sorry' as a WARNING not an error, so a sorry-stubbed file still "builds":
  you MUST run the axiom audit (non-quiet) and read the #print axioms output to detect sorryAx.
- Build/check:  scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/<file>.lean
  (the non-quiet form prints the #print axioms lines).`

const COMMON = `You work in the ArkLib Lean 4 Proximity-Gap cone (#444), dir
/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib.
Read FIRST: docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md (E1..E7 + P1..P6),
ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md, and the substrate file(s) you consume under
ArkLib/Data/CodingTheory/ProximityGap/.
${HONESTY}`

function chunk(arr, n){ const out=[]; for(let i=0;i<arr.length;i+=n) out.push(arr.slice(i,i+n)); return out }
async function waved(specs, mk, label){
  let acc=[]
  const waves = chunk(specs, 6)
  for (let w=0; w<waves.length; w++){
    log(`${label} wave ${w+1}/${waves.length} (${waves[w].map(s=>s.id).join(',')})`)
    const r = await pipeline(waves[w], mk)
    acc = acc.concat(r)
  }
  return acc
}

phase('Audit')
const auditSpecs = SPECS.filter(s => EXISTING.has(s.id))
const audited = await waved(auditSpecs, (spec) => agent(
    `${COMMON}

AUDIT + REPAIR an EXISTING bridge file. A previous agent wrote
${DIR}/_Bridge${spec.id}.lean  (also possibly ${DIR}/_Bridge${spec.id.replace('B','')}* variants)
for spec ${spec.id} [target ${spec.t}]: ${spec.claim}.
Tasks:
 1. Run the axiom audit (non-quiet pg-iterate) and READ the #print axioms output.
 2. If it is already CLEAN_LANDED (builds, no real sorry, axioms subset of ${ALLOWED}, and the
    theorem FAITHFULLY states the claimed bridge - not a vacuous/tautological restatement) => report it.
 3. If it has a fixable defect (a sorry in a helper, a type mismatch, a missing import olean, a
    vacuous hypothesis) => REPAIR it in place (keep imports minimal; keep the honest scope) and
    rebuild. If you can only prove it modulo an honest named hypothesis, make that a 'variable
    (h : <Prop>)' and report REDUCED with the Prop named.
 4. If the claim is false/ill-posed, say FAILED with the reason.
Return the verdict for the (possibly repaired) file.`,
    {label:`audit:${spec.id}`, phase:'Audit', schema:VERDICT}
  ), 'Audit')

phase('Grind')
const grindSpecs = SPECS.filter(s => !EXISTING.has(s.id))
const ground = await waved(grindSpecs, (spec) => agent(
    `${COMMON}

ATTEMPT a fresh bridge. Write ${DIR}/_Bridge${spec.id}.lean (minimal imports), proving:
SPEC ${spec.id} [target ${spec.t}]: ${spec.claim}
SUBSTRATE to build on: ${spec.sub}.lean (read it; reuse its lemmas, don't re-derive).
Prove as much as is genuinely true. CLEAN_LANDED iff axiom-clean per the contract; otherwise
REDUCED (name the Prop in gap) or FAILED (name the obstruction). Never fake LANDED.
Return the verdict.`,
    {label:`grind:${spec.id}`, phase:'Grind', schema:VERDICT}
  ), 'Grind')

phase('Verify')
const all = [...audited, ...ground].filter(Boolean)
const claimed = all.filter(r => r.status==='CLEAN_LANDED' && r.axiomsClean)
const verified = await waved(claimed, (r) => agent(
    `${COMMON}

ADVERSARIALLY VERIFY a claimed CLEAN_LANDED bridge brick.
File: ${r.file || `${DIR}/_Bridge${r.id}.lean`}   Key theorem: ${r.keyTheorem || '(find it)'}
Claim: bridge ${r.id}.
Re-run scripts/pg-iterate.sh on it; independently open the file and look for an actual 'sorry'/
'admit'/'native_decide'/'axiom' decl; run #print axioms on the key theorem; CONFIRM the set is a
subset of ${ALLOWED}. Then judge FAITHFULNESS: does the theorem statement actually express the
claimed bridge, with no vacuous/unsatisfiable hypothesis and no trivial-tautology dodge? A brick
that imports nothing and proves 0=0 is NOT a confirmed bridge.
Set status=CLEAN_LANDED iff genuinely confirmed, else the honest downgrade (SORRY_STUBBED/VACUOUS/
REDUCED/BROKEN). Return the (re-)verdict.`,
    {label:`verify:${r.id}`, phase:'Verify', schema:VERDICT}
  ), 'Verify')

phase('Synthesize')
const vmap = new Map(verified.filter(Boolean).map(v => [v.id, v]))
const final = all.map(r => vmap.get(r.id) || r)
const landed = final.filter(r => r.status==='CLEAN_LANDED' && r.axiomsClean)
const reduced = final.filter(r => r.status==='REDUCED')
const stubbed = final.filter(r => r.status==='SORRY_STUBBED' || r.status==='VACUOUS')
const broken = final.filter(r => r.status==='BROKEN' || r.status==='FAILED')
log(`GRIND-v2 done: ${landed.length} CLEAN_LANDED, ${reduced.length} REDUCED, ${stubbed.length} stubbed/vacuous, ${broken.length} broken/failed of ${final.length}`)
return {
  counts:{landed:landed.length, reduced:reduced.length, stubbed:stubbed.length, broken:broken.length, total:final.length},
  landed: landed.map(r=>({id:r.id,t:vmap.get(r.id)?.id?undefined:undefined,file:r.file,keyTheorem:r.keyTheorem,summary:r.summary})),
  landedIds: landed.map(r=>r.id),
  reduced: reduced.map(r=>({id:r.id,gap:r.gap,summary:r.summary})),
  stubbed: stubbed.map(r=>({id:r.id,status:r.status,gap:r.gap})),
  broken: broken.map(r=>({id:r.id,gap:r.gap})),
}
