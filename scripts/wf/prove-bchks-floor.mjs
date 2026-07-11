export const meta = {
  name: 'prove-bchks-floor',
  description: 'Prove the CORRECT δ* floor (Sumset-Extremality / char-free complete-homogeneous), pinning the exact lower bound',
  phases: [
    { title: 'Prove', detail: 'attack each piece of the correct floor: complete-homog bound, crossing→δ*, Linnik, char-p exponent-0, re-targeted reduction' },
    { title: 'Verify', detail: 'adversarial axiom + faithfulness audit' },
    { title: 'Synthesize', detail: 'the floor proof ledger' },
  ],
}

const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const ALLOWED = '{propext, Classical.choice, Quot.sound}'

const COMMON = `ArkLib Lean 4 Proximity-Gap cone (#444), dir
/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib.
GOAL: fully PROVE the floor that pins the exact δ* LOWER BOUND.
Read FIRST: docs/kb/deltastar-444-BCHKS-correct-object-and-attack-2026-06-16.md — THE in-tree
'BCHKS1_12 = |Σ_r(μ_s)| ≤ budget' Prop is FALSE (the subset-sum count GROWS, never ≤ budget; verified).
The REAL floor (ABF26 §4) is **Sumset-Extremality**: #{λ : Δ(f+λg,C) ≤ δ} ≤ poly(n)·|H^{(+r)}|, with
|F| LARGE, δ* = where #bad goes poly(n)→super-poly. The worst CHAR-FREE direction is the
**complete-homogeneous** one: bad-count ~ h_j = C(s+r−1, r) (NOT the subset-sum C(s,r); that ceiling
is refuted, log ratio→0.26). Leading δ* is char-FREE-pinned by C(s+r−1,r) crossing ε*·|F|; the char-p
anomaly is EXPONENT-0 (irreducible residual, does NOT move leading order). Also read
docs/kb/prize-407-faithful-problem-map-from-abf26.md, the bridge ledger, CLAUDE.md §6.
In-tree substrate: SchurLagrangeBridge (dividedDifferencePow_eq_schurH: forced-γ = h_{a−k}(R) =
complete-homogeneous), _CoreA5 (monomial_dir_maximizes_overdet), _BridgeB19/B20 (D*(1) = distinct
forced-γ count ≤ C(n,k+1)), OrbitCountCrossingLaw, the E_r ladder (E_2..E_7 exact),
E2W4CyclotomicNonCollision / KKH26CharZeroCollisionLaw (good-prime collisions).
BUILD: scripts/pg-iterate.sh <file> (lock-free; sorry=WARNING — READ #print axioms for sorryAx).
Exact computation: scripts/probes/probe_*.py, scripts/rust-pg.
HONESTY (paramount): NEVER fabricate a closure. Honest outcomes: LANDED (axiom-clean brick ⊆
${ALLOWED}, no sorry/native_decide/fake-axiom; paste #print axioms — a CONDITIONAL brick with an
explicit named hypothesis is LANDED+REDUCED, that is the project convention), REFUTED (countermodel),
or REDUCED (the precise remaining named Prop). Pin the lower bound as far as it provably goes; name
the residual exactly.`

const SCHEMA = {
  type:'object', additionalProperties:false,
  required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['LANDED','REDUCED','REFUTED','PARTIAL','FAILED']},
    axiomsClean:{type:'boolean'}, file:{type:'string'}, keyTheorem:{type:'string'}, axioms:{type:'string'},
    finding:{type:'string'}, summary:{type:'string'},
  },
}

const TARGETS = [
  {id:'F1-CompHomogBound', file:'_BchksF1_CompleteHomogeneousFloor', task:`Prove the CHAR-FREE worst-direction bad-scalar bound: the distinct forced-γ count of the worst MONOMIAL far direction at depth r equals/is-bounded-by the COMPLETE-HOMOGENEOUS count. Using SchurLagrangeBridge (γ_R = −h_{a−k}(R)/h_{b−k}(R), the forced ratio per (k+1)-subset R, h = complete-homogeneous symmetric) + _CoreA5 (monomial is worst), prove #{distinct γ_R : R ∈ binom(μ_s, k+1)} ≤ C(s+r−1, r) (the dimension of degree-r complete-homogeneous = #multisets). This is the char-free ceiling on #bad. Land axiom-clean (the multiset-count upper bound is combinatorial), or REDUCE to the precise distinct-value count.`},
  {id:'F2-CrossingToDelta', file:'_BchksF2_PolyCrossingDeltaStar', task:`Prove the crossing that PINS the δ* LOWER BOUND: with #bad ≤ poly(n)·C(s+r−1, r) and the budget ε*·|F|, the threshold δ* (where poly·C(s+r−1,r) crosses ε*·|F|, r=⌊δs⌋-related) gives an EXPLICIT lower bound δ* ≥ 1−ρ−Θ(log(1/2ρ)/log(|F|ε*)). Derive the leading-order δ* formula from the crossing of the complete-homogeneous count (use Stirling/log on C(s+r−1,r)). Land the explicit lower-bound formula axiom-clean as a ℚ/ℝ-arithmetic brick (the crossing is elementary given the count bound F1), with #bad≤poly·C(s+r−1,r) as the named input. This is the deliverable: an explicit δ* lower bound.`},
  {id:'F3-RetargetReduction', file:'_BchksF3_RetargetedReduction', task:`RE-TARGET the in-tree reduction to the CORRECT object. The complete reduction (_CoreReductionComplete.prize_reduces_to_BCHKS) is vacuous because |Σ_r|≤budget is false. Prove the CORRECTED version: δ* ≥ (window interior) ⟸ Sumset-Extremality (#bad ≤ poly(n)·|H^{(+r)}|), with #bad the distinct-γ count D*(m) and |H^{(+r)}| the sumset. The dedup D ≤ |H^{(+r)}| is TRUE (in-tree _CoreA3 dedup domination); but the floor needs #bad ≤ poly·(sumset), NOT sumset≤budget. State and prove the corrected reduction skeleton axiom-clean with Sumset-Extremality as the single named hypothesis. Refute/deprecate the |Σ_r|≤budget form with the computed growth (probe_subsetsum_grows_refutes_bchks.py).`},
  {id:'F4-LinnikGoodPrime', file:'_BchksF4_GoodPrimeLinnik', task:`Prove the GOOD-PRIME existence residual: a prime p where the r-fold sums of μ_s are DISTINCT mod p exists, with the bad-prime set = {p : p | Res(Φ_s, ΣXⁱ−ΣXʲ)} bounded by ≤ log₄ s per pair (in-tree E2W4CyclotomicNonCollision / KKH26CharZeroCollisionLaw). Prove the per-pair bad-prime norm bound axiom-clean (the resultant/norm is bounded ⟹ ≤ log₄ s prime divisors), and REDUCE the existence of a good prime in the prize range to quantitative Linnik / effective Chebotarev (the named analytic input). Land the combinatorial half axiom-clean.`},
  {id:'F5-AnomalyExp0', file:'_BchksF5_CharPAnomalyExpZero', task:`Prove the char-p anomaly is EXPONENT-0 (does NOT move the leading δ*). The char-p energy excess W_r = E_r(F_p) − E_r(char-0) is governed by an ONSET THRESHOLD (verified: W_r=0 for p > threshold(r); W_2=W_3=W_4=0 at prize scale). Prove that the char-p anomaly contributes only a sub-leading (exponent-0) correction to #bad, so the LEADING δ* is char-free-pinned (F1/F2). Formalize: the anomaly count ≤ (good count)·(1 + o(1)) at the prize prime, or REDUCE the exponent-0 claim to the deep-r onset (W_r=0 to r≈log q) — the genuine residual. Land what is provable (the W_r onset law, probe_wr_onset_threshold.py) + the exponent-0 reduction.`},
  {id:'F6-ExplicitLowerBound', file:'_BchksF6_ExplicitDeltaStarLower', task:`ASSEMBLE the explicit δ* LOWER BOUND from F1-F5. Combine: #bad ≤ poly·C(s+r−1,r) (F1) + the crossing (F2) + good-prime (F4) + anomaly exponent-0 (F5) into a single axiom-clean theorem: δ* ≥ 1−ρ−<explicit leading term>, with the residuals (Sumset-Extremality, Linnik, deep-r W_r=0) as the explicit named hypotheses — everything char-free discharged. This is the exact δ* lower bound modulo the named residuals. Do NOT discharge the residuals; state them precisely. The deliverable for the goal: the pinned lower bound.`},
]

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, label){
  let acc=[]
  for (const [i,w] of chunk(items,3).entries()){ log(`${label} wave ${i+1}/${Math.ceil(items.length/3)} (${w.map(s=>s.id||s).join(',')})`); acc=acc.concat(await pipeline(w, mk)) }
  return acc
}

phase('Prove')
const results = await waved(TARGETS, (T) => agent(
  `${COMMON}

TARGET ${T.id}. File: ${DIR}/${T.file}.lean.
${T.task}
Return the structured verdict with the precise proven statement / the explicit lower-bound formula / the named residual in 'finding'.`,
  {label:`prove:${T.id}`, phase:'Prove', schema:SCHEMA}
), 'Prove')

phase('Verify')
const claimed = results.filter(r => r && (r.outcome==='LANDED'||r.outcome==='PARTIAL'||r.outcome==='REFUTED') && (r.axiomsClean!==false))
const verified = await waved(claimed, (r) => agent(
  `${COMMON}

ADVERSARIALLY VERIFY ${r.outcome} for ${r.id}. File: ${r.file||'(find it)'} Key thm: ${r.keyTheorem||'(find it)'}.
Re-run pg-iterate; check for real sorry/admit/native_decide/axiom; #print axioms ⊆ ${ALLOWED}.
Judge FAITHFULNESS HARD: does it prove the claimed floor piece (not a tautology / vacuous-False hyp /
a value laundered)? For the explicit lower bound, confirm the formula is non-vacuous and the residual
hypotheses are genuinely the open part, not the whole content hidden. Re-run any cited probe. Return the (re)verdict.`,
  {label:`verify:${r.id}`, phase:'Verify', schema:SCHEMA}
), 'Verify')

phase('Synthesize')
const vmap = new Map(verified.filter(Boolean).map(v=>[v.id,v]))
const fin = results.filter(Boolean).map(r=>vmap.get(r.id)||r)
const tally={}; for(const r of fin) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`prove-bchks-floor done: ${JSON.stringify(tally)}`)
return {
  tally,
  landed: fin.filter(r=>r.outcome==='LANDED'||r.outcome==='PARTIAL').map(r=>({id:r.id,file:r.file,keyTheorem:r.keyTheorem,finding:r.finding})),
  reduced: fin.filter(r=>r.outcome==='REDUCED').map(r=>({id:r.id,finding:r.finding})),
  all: fin.map(r=>({id:r.id,outcome:r.outcome,finding:(r.finding||'').slice(0,400)})),
}
