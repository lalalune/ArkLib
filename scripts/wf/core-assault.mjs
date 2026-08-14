export const meta = {
  name: 'deltastar-core-assault',
  description: 'Exhaustively attack the m*-growth / BCHKS 1.12 core + assemble the complete reduction theorem (#444)',
  phases: [
    { title: 'Angles', detail: 'distinct independent angles on the m*-growth core: prove a partial bound, refute, or classify reduces-to-BCHKS' },
    { title: 'Assemble', detail: 'the complete reduction theorem: δ* window-interior ⟺ BCHKS 1.12, from the landed bricks' },
    { title: 'Critic', detail: 'completeness critic — what angle is unattacked, what is the sharpest irreducible statement' },
    { title: 'Synthesize', detail: 'the honest closure map' },
  ],
}

const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const ALLOWED = '{propext, Classical.choice, Quot.sound}'

const COMMON = `ArkLib Lean 4 Proximity-Gap cone (#444), dir
/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib.
Read FIRST: docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md (E1..E7, §D
corrections incl. the cf≠D and refutation notes, §E ledger), ArkLib/Data/CodingTheory/ProximityGap/
CLAUDE.md §6 (honesty). The whole 50-bridge program already reduced the prize to ONE open input:
the m*-growth / plateau-width bound = BCHKS Conjecture 1.12 (distinct r-fold subset-sum count
|Σ_r(μ_s)| ≤ q·ε* at r≈log m). This is a p-INDEPENDENT COMBINATORIAL conjecture (off the analytic
BGK char-sum wall), but OPEN (the framework authors' own conjecture). My memory has 100+ attempts
all reducing to it.
BUILD: scripts/pg-iterate.sh <file> (lock-free; sorry is a WARNING — READ #print axioms for sorryAx).
HONESTY (paramount): do NOT fabricate a closure of BCHKS/the prize. A partial one-sided bound, an
honest reduction (modulo a named Prop), or a rigorous "reduces to BCHKS 1.12 because X" are all
valuable. CLEAN_LANDED requires real axiom-clean build (⊆ ${ALLOWED}, no sorry/native_decide/fake
axiom; paste #print axioms). Never claim the prize is closed.`

const SCHEMA = {
  type:'object', additionalProperties:false,
  required:['id','status','summary'],
  properties:{
    id:{type:'string'},
    status:{type:'string', enum:['CLEAN_LANDED','PARTIAL_BOUND','REDUCES_TO_BCHKS','REFUTED','REDUCED','FAILED']},
    axiomsClean:{type:'boolean'}, file:{type:'string'}, keyTheorem:{type:'string'}, axioms:{type:'string'},
    finding:{type:'string', description:'the precise result: the bound proven, or the exact reason it reduces to BCHKS, or the countermodel'},
    summary:{type:'string'},
  },
}

// distinct angles — chosen to NOT repeat the memory's dead ends; each is a genuinely different lens
const ANGLES = [
  {id:'A1', file:'_CoreA1_LowerBound', task:`Prove a PROVABLE one-sided bound on m* (the binding over-det depth). Candidate: m* ≥ 3 for ρ=1/4 at n≥8 (the cascade D does NOT cross budget before depth 3 because D(k+1)~n³ ≫ n and D(k+2)~n² ≫ n for the worst monomial direction). Formalize a lower bound m* ≥ c via D(k+1) > budget and D(k+2) > budget (the over-det edge values exceed n). This is the EASY side (lower bound on m* = upper bound on δ*, consistent with P5). Land it axiom-clean or REDUCE.`},
  {id:'A2', file:'_CoreA2_OrbitDecay', task:`Attack the m* UPPER bound (the prize side) via the orbit-count O decay. From OrbitCountCrossingLaw (D=z+S·O, crossing ⟺ O≤gcd(b-a,n)), the binding is where the orbit count O(a,b;m) drops to ≤ d. Prove ANY upper bound on O(a,b;m) as a function of m for the worst (primitive) direction — even a weak poly(n) bound at m=O(log n) would crack the prize. Honestly: this O-bound IS BCHKS 1.12; if you cannot prove it, state PRECISELY why O's bound = BCHKS (the reduction), and land any partial monotonicity/structure of O. REDUCES_TO_BCHKS with the exact mechanism, or a real partial bound.`},
  {id:'A3', file:'_CoreA3_BackwardProof', task:`BACKWARD-PROOF: assume the target m* = O(log n) (equivalently δ* → capacity − c_ρ) as a hypothesis, and derive the WEAKEST combinatorial statement that would suffice. Is that weakest sufficient statement strictly WEAKER than BCHKS 1.12 (a possible escape), or equal to it (the wall)? Formalize the implication 'weakest-suff ⟹ m*=O(log n)' and characterize weakest-suff precisely. My memory tried this and it "converged to single-saddle MGF = wall" — RE-CHECK with the p-independent combinatorial framing (NOT the char-sum MGF), since the object is now known p-independent. Land the implication + the honest verdict on whether weakest-suff < BCHKS.`},
  {id:'A4', file:'_CoreA4_PlateauWidth', task:`The PLATEAU-WIDTH angle (this session's freshest lever). The cascade recursion D*_{2n}(m)=D*_n(m-1) is exact EXCEPT a plateau-doubling at imprimitive directions (n=32 gets a doubled 89-rung, pushing m* 3→5). PROVE a bound on the plateau width w per tower level. If w=O(1) per level then m*=O(log n) (prize). Formalize: define plateauWidth, and either (a) prove w ≤ c from the orbit structure (B27 dichotomy: doubling only at even b-a), or (b) reduce 'w bounded' to a precise named combinatorial Prop and compare it to BCHKS. The B27/B30 bricks are substrate. Honest PARTIAL_BOUND or REDUCES_TO_BCHKS.`},
  {id:'A5', file:'_CoreA5_MonomialWorst', task:`Prove the binding is MONOMIAL-CONTROLLED: at the binding crossing depth m*, the worst far direction achieving the max incidence is a MONOMIAL (x^a, x^b) (dirworst empirically confirmed: non-monomial directions exceed monomials at the over-det EDGE but decay below by the crossing). B34 (monomial_dir_maximizes) landed the exact-agreement case; extend to the over-det binding. If proven, the prize reduces to the MONOMIAL cascade (the p-independent orbit object), tightening the reduction. Land axiom-clean or REDUCE precisely.`},
  {id:'A6', file:'_CoreA6_NovelInvariant', task:`Seek a NOVEL p-independent invariant that bounds m* and is NOT BCHKS 1.12. The cascade D, orbit count O, graded cf, subset-sum count are all known. Is there a DIFFERENT computable invariant (e.g. a resultant/discriminant degree count, a Newton-polygon/valuation bound, a matroid/rank invariant of the divided-difference system, a Schur-positivity argument) that upper-bounds the binding depth WITHOUT going through the subset-sum count? Be creative (CLAUDE.md §6A: bold exploration encouraged). If you find one, formalize the bound; if it collapses to BCHKS, say so with the reduction. This is the genuine 'new angle' search.`},
  {id:'A7', file:'_CoreA7_NecessityTight', task:`Prove the reduction is TIGHT / BCHKS is NECESSARY (not just sufficient): construct/justify that IF BCHKS 1.12 FAILS then m* is large (δ* fails to beat Johnson), making prize ⟺ BCHKS a genuine equivalence rather than one-way. Formalize the converse direction 'm*=O(log n) ⟹ BCHKS-type budget holds' or a precise obstruction. Combined with B31 (forward), this yields the COMPLETE EQUIVALENCE. Land the converse axiom-clean or REDUCE with the exact named gap.`},
]

const REDUCTION = {
  type:'object', additionalProperties:false,
  required:['status','summary'],
  properties:{
    status:{type:'string', enum:['CLEAN_LANDED','REDUCED','FAILED']},
    axiomsClean:{type:'boolean'}, file:{type:'string'}, keyTheorem:{type:'string'}, axioms:{type:'string'},
    summary:{type:'string'}, remainingHypotheses:{type:'string'},
  },
}

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, label){
  let acc=[]
  for (const [i,w] of chunk(items,6).entries()){ log(`${label} wave ${i+1} (${w.map(s=>s.id||s).join(',')})`); acc=acc.concat(await pipeline(w, mk)) }
  return acc
}

phase('Angles')
const angleResults = await waved(ANGLES, (A) => agent(
  `${COMMON}

ATTACK a distinct angle on the m*-growth core. Write ${DIR}/${A.file}.lean (minimal imports).
ANGLE ${A.id}:
${A.task}
Reuse the landed bricks as substrate (_BridgeB*, especially B27/B29/B30/B31/B34/B48). Return the verdict.`,
  {label:`angle:${A.id}`, phase:'Angles', schema:SCHEMA}
), 'Angles')

phase('Assemble')
const assembly = await agent(
  `${COMMON}

ASSEMBLE THE COMPLETE REDUCTION THEOREM. Write ${DIR}/_CoreReductionComplete.lean.
GOAL: a single axiom-clean theorem chaining the landed bricks into
  'δ* lies in the window interior (Johnson, capacity)  ⟸  [the explicit named BCHKS-type Prop]'
using: B48 (D* monotone), B47 (cascade tail), B29 (mStar_tower_shift), B31 (mStar_le_iff_BCHKS),
B01/B02/B04 (master identity + Johnson crossing), B50 (assembly skeleton). The ONLY remaining
hypothesis must be the single named BCHKS/m*-growth Prop — everything else discharged by the bricks.
This proves the bridge program is a COMPLETE REDUCTION (the prize is EXACTLY this one combinatorial
Prop). Do NOT discharge that Prop (it is the open prize). Land the reduction chain axiom-clean with
the one named hypothesis. Return status + the remaining hypothesis stated precisely.`,
  {label:'assemble:complete-reduction', phase:'Assemble', schema:REDUCTION}
)

phase('Critic')
const critic = await agent(
  `${COMMON}

COMPLETENESS CRITIC. Given the angle results and the assembled reduction, answer rigorously:
(1) Is there any p-independent angle on m*-growth NOT yet attacked (a modality/invariant/reduction
not in {cascade D, orbit count O, graded cf, subset-sum, the 7 angles A1-A7})? Name it concretely.
(2) Is the reduction prize ⟺ BCHKS 1.12 now COMPLETE and TIGHT, or is a direction still open?
(3) What is the single SHARPEST irreducible statement the whole program leaves open, stated as one
precise sentence? (4) Honestly: is there any realistic in-tree path to the prize, or is it now
strictly external (proving BCHKS 1.12 itself)? Be skeptical and precise; cite the brick/angle files.
Return your assessment in the 'summary' field; set status='CLEAN_LANDED' only if you actually built
something, else 'FAILED' with the assessment in summary.`,
  {label:'critic:completeness', phase:'Critic', schema:SCHEMA}
)

phase('Synthesize')
const angles = angleResults.filter(Boolean)
const landed = angles.filter(a=>a.status==='CLEAN_LANDED'||a.status==='PARTIAL_BOUND')
const reduces = angles.filter(a=>a.status==='REDUCES_TO_BCHKS')
const refuted = angles.filter(a=>a.status==='REFUTED')
log(`core-assault: ${landed.length} partial/landed bounds, ${reduces.length} reduce-to-BCHKS, ${refuted.length} refuted; reduction=${assembly?.status}`)
return {
  angles: angles.map(a=>({id:a.id,status:a.status,finding:a.finding,file:a.file})),
  partialBounds: landed.map(a=>({id:a.id,file:a.file,keyTheorem:a.keyTheorem,finding:a.finding})),
  reducesToBCHKS: reduces.map(a=>({id:a.id,finding:a.finding})),
  completeReduction: assembly ? {status:assembly.status,file:assembly.file,key:assembly.keyTheorem,remaining:assembly.remainingHypotheses,summary:assembly.summary} : null,
  criticAssessment: critic?.summary || critic?.finding,
}
