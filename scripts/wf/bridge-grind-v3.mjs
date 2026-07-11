export const meta = {
  name: 'deltastar-bridge-grind-v3',
  description: 'Repair broken/sorry bridge bricks and grind the remaining missing δ* specs (#444)',
  phases: [
    { title: 'Remaining', detail: 'repair B07-B11,B18 and grind B26-B50 missing; axiom-clean or honest reduction' },
    { title: 'Verify', detail: 'adversarial axiom + faithfulness audit of CLEAN claims' },
    { title: 'Synthesize', detail: 'final grind tally' },
  ],
}

const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const ALLOWED = '{propext, Classical.choice, Quot.sound}'

// the 24 remaining specs: 6 to REPAIR (file exists, broken/sorry) + 18 to GRIND (no file)
const SPECS = [
  {id:'B07',mode:'repair',t:'E6',claim:'#bad_{2n}(k,2m\')=#bad_n(k/2,m\') (even-fold counting bijection). HARD. If full bijection resists, land a clean PARTIAL (e.g. the injection one way, or the explicit doubling fold map as a function preserving the graded vector) and name the residual.',sub:'DyadicTowerRecursion'},
  {id:'B08',mode:'repair',t:'E6',claim:'graded frequency-vector bin index halves under doubling: residue (j*a mod 2n) binned mod n behaves as the level-n graded bin under a|->2a',sub:'DyadicTowerRecursion'},
  {id:'B09',mode:'repair',t:'E6',claim:'bridge eta-parallelogram (DyadicTowerRecursion.sum_tower_split) to even-only graded count: odd part cancels',sub:'DyadicTowerRecursion'},
  {id:'B10',mode:'repair',t:'E6',claim:'even-tau-exactness: sum_{x in mu_{2n}} x^{odd} = 0 (geometric sum of nonzero power over full subgroup). Fix the missing-olean import.',sub:'DyadicTowerRecursion'},
  {id:'B11',mode:'repair',t:'E3',claim:'bad-gamma set closed under gamma|->gamma*h^{b-a} (orbit closure). Replace the sorry with a real proof or an honest named-hypothesis reduction.',sub:'OrbitCountCrossingLaw'},
  {id:'B18',mode:'repair',t:'E4',claim:'k-th divided difference DD_k(x^a) over nodes T = complete homogeneous symmetric h_{a-k}(T). Use Mathlib divided-difference / Newton if available, else state the identity for small k via the recurrence and name the general case.',sub:'IncidencePeriodBridge'},
  {id:'B26',mode:'grind',t:'E5',claim:'primitive directions satisfy clean recursion D*_{2n}(m)=D*_n(m-1) (gcd(b-a,2n)=1 forces clean descent)',sub:'OrbitCountCrossingLaw'},
  {id:'B27',mode:'grind',t:'E5',claim:'plateau-doubling only at imprimitive (b-a even) directions: even b-a => h^{b-a} fixes mu_2, extra invariant rung',sub:'OrbitCountCrossingLaw'},
  {id:'B28',mode:'grind',t:'E5',claim:'IF plateau excess per tower level <= c THEN m*=O(log n): induct m*(2n)<=m*(n)+1+c (conditional brick, name the hypothesis)',sub:'OrbitCountCrossingLaw'},
  {id:'B30',mode:'grind',t:'E5',claim:'net m* increment per doubling <= plateau width at binding value (crossing-radius bookkeeping)',sub:'OrbitCountCrossingLaw'},
  {id:'B37',mode:'grind',t:'X',claim:'far-line incidence equals period sum (consume IncidencePeriodBridge.lineIncidence_period_sum, restate cleanly)',sub:'IncidencePeriodBridge'},
  {id:'B38',mode:'grind',t:'X',claim:'lower bound D*(m) > budget for m < m* (bad side of crossing): if any far dir has incidence > budget at depth m, then m < m* (def of binding)',sub:'OpenCoreConverse'},
  {id:'B39',mode:'grind',t:'X',claim:'eps_mca >= incidence/q: consume FarCosetExplosion (the in-tree ε_mca >= incidence/q fact), restate as a bridge lemma',sub:'OpenCoreConverse'},
  {id:'B40',mode:'grind',t:'X',claim:'worstCase Lambda^2 = max_b ||eta_b||^2 ties to D* via period sum (P2). If PrizeStructuralConstant exists, consume it.',sub:'IncidencePeriodBridge'},
  {id:'B41',mode:'grind',t:'E6',claim:'#bad support max depth m <= k: via the FFT 2-adic descent the support cutoff is bounded by k (state the monotone descent bound)',sub:'DyadicTowerRecursion'},
  {id:'B42',mode:'grind',t:'E6',claim:'v_2(m) controls FFT-recursion descent depth: each step halves m and k, stops at odd m (Nat 2-adic valuation lemma)',sub:'DyadicTowerRecursion'},
  {id:'B43',mode:'grind',t:'E6',claim:'base cases: define fhat graded count in Lean over ZMod 4 (n=4) and prove #bad_4(1,1), #bad_4(1,2) explicit by decide/Finset.card',sub:'DyadicTowerRecursion'},
  {id:'B44',mode:'grind',t:'E6',claim:'fhat odd-vanishing as character sum over mu_{2n} identically 0 (orthogonality of characters / geometric sum)',sub:'DyadicTowerRecursion'},
  {id:'B45',mode:'grind',t:'E3',claim:'over-det edge orbit count O(m=1) = (n/2-1) closed form (cyclotomic nonzero-orbit count at the edge)',sub:'OrbitCountCrossingLaw'},
  {id:'B46',mode:'grind',t:'E1',claim:'m* well-defined: {m : D*(k+m)<=budget} nonempty so Nat.find exists (D*(n) trivial <= budget). Use Nat.find machinery.',sub:'OpenCoreConverse'},
  {id:'B47',mode:'grind',t:'E4',claim:'cascade tail D*(n-k)=1 or <=1: full over-determination (s=n) leaves only the trivial RS-membership gamma',sub:'IncidencePeriodBridge'},
  {id:'B48',mode:'grind',t:'E4',claim:'D* monotone non-increasing in m: agreement on s+1 pts implies agreement on s pts, so the bad-gamma set at s+1 is a subset of that at s, hence card monotone (Finset.card_le_card)',sub:'IncidencePeriodBridge'},
  {id:'B49',mode:'grind',t:'X',claim:'budget = floor(q*eps*) and at prize params (q=n^beta, eps*=2^-128) approx n: state the exact arithmetic relation',sub:'OpenCoreConverse'},
  {id:'B50',mode:'grind',t:'E7',claim:'ASSEMBLY: deltaStar in (Johnson,capacity) from {B48 monotone, B47 tail, hypothesis m*<k}: combine the landed bricks into the window-interior conclusion, naming m*<k as the one remaining hypothesis',sub:'OpenCoreConverse'},
]

const VERDICT = {
  type:'object', additionalProperties:false,
  required:['id','status','axiomsClean','summary'],
  properties:{
    id:{type:'string'},
    status:{type:'string', enum:['CLEAN_LANDED','REDUCED','VACUOUS','BROKEN','FAILED']},
    axiomsClean:{type:'boolean'},
    file:{type:'string'},
    keyTheorem:{type:'string'},
    axioms:{type:'string'},
    gap:{type:'string'},
    summary:{type:'string'},
  },
}

const HONESTY = `HONESTY CONTRACT (ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md §6):
CLEAN_LANDED only if it elaborates with NO error, NO real 'sorry'/'admit'/'native_decide'/fake
'axiom' (a 'sorry' inside a docstring sentence does NOT count), and '#print axioms <thm>' is a
SUBSET of ${ALLOWED} (so [propext] or [propext, Quot.sound] is fine). Paste #print axioms into
'axioms'. A tautology / vacuous-False-hypothesis / trivial restatement that does not bridge =>
VACUOUS. A genuine reduction proving the target modulo an explicitly-named Prop ('variable
(h:<Prop>)') => REDUCED (name the Prop in 'gap'). pg-iterate.sh treats sorry as a WARNING so a
sorry-stubbed file still "builds" — you MUST read the #print axioms output (non-quiet) to detect
sorryAx. NEVER fake LANDED.`

const COMMON = `ArkLib Lean 4 Proximity-Gap cone (#444), dir
/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib.
Read FIRST: docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md (E1..E7,P1..P6),
ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md, your substrate file under
ArkLib/Data/CodingTheory/ProximityGap/. Build: scripts/pg-iterate.sh <file> (lock-free, non-quiet
prints #print axioms). ${HONESTY}`

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(specs, mk, label){
  let acc=[]
  for (const [i,w] of chunk(specs,6).entries()){
    log(`${label} wave ${i+1} (${w.map(s=>s.id).join(',')})`)
    acc = acc.concat(await pipeline(w, mk))
  }
  return acc
}

phase('Remaining')
const results = await waved(SPECS, (spec) => agent(
  `${COMMON}

${spec.mode==='repair'
  ? `REPAIR the existing file ${DIR}/_Bridge${spec.id}.lean (it currently FAILS to build or has a sorry).`
  : `WRITE a fresh file ${DIR}/_Bridge${spec.id}.lean (minimal imports).`}
SPEC ${spec.id} [target ${spec.t}]: ${spec.claim}
SUBSTRATE: ${spec.sub}.lean (read it, reuse its lemmas).
Prove as much as is genuinely true; CLEAN_LANDED iff axiom-clean per contract, else REDUCED (name
the Prop) or FAILED (name obstruction). Return the verdict.`,
  {label:`${spec.mode}:${spec.id}`, phase:'Remaining', schema:VERDICT}
), 'Remaining')

phase('Verify')
const claimed = results.filter(r => r && r.status==='CLEAN_LANDED' && r.axiomsClean)
const verified = await waved(claimed, (r) => agent(
  `${COMMON}

ADVERSARIALLY VERIFY claimed CLEAN_LANDED brick ${r.id}.
File: ${r.file||`${DIR}/_Bridge${r.id}.lean`}  Key thm: ${r.keyTheorem||'(find it)'}.
Re-run pg-iterate; open the file, look for a real sorry/admit/native_decide/axiom; run #print
axioms on the key theorem; confirm subset of ${ALLOWED}; judge FAITHFULNESS (no vacuous/False
hypothesis, not a 0=0 dodge, statement actually expresses the bridge). Return the (re)verdict.`,
  {label:`verify:${r.id}`, phase:'Verify', schema:VERDICT}
), 'Verify')

phase('Synthesize')
const vmap = new Map(verified.filter(Boolean).map(v=>[v.id,v]))
const final = results.filter(Boolean).map(r => vmap.get(r.id)||r)
const landed = final.filter(r=>r.status==='CLEAN_LANDED'&&r.axiomsClean)
const reduced = final.filter(r=>r.status==='REDUCED')
const other = final.filter(r=>!['CLEAN_LANDED','REDUCED'].includes(r.status))
log(`v3 done: ${landed.length} CLEAN_LANDED, ${reduced.length} REDUCED, ${other.length} other of ${final.length}`)
return {
  counts:{landed:landed.length, reduced:reduced.length, other:other.length, total:final.length},
  landedIds: landed.map(r=>r.id),
  landed: landed.map(r=>({id:r.id,file:r.file,keyTheorem:r.keyTheorem,summary:r.summary})),
  reduced: reduced.map(r=>({id:r.id,gap:r.gap,summary:r.summary})),
  other: other.map(r=>({id:r.id,status:r.status,gap:r.gap})),
}
