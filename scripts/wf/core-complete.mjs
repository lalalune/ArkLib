export const meta = {
  name: 'deltastar-core-complete',
  description: 'Finish the core assault: A4/A7 + complete reduction + deepen A6/A3 + completeness critic (#444)',
  phases: [
    { title: 'Finish', detail: 'A4 plateau-width, A7 necessity, complete reduction theorem, deepen A6/A3' },
    { title: 'Verify', detail: 'adversarial axiom + faithfulness audit' },
    { title: 'Critic', detail: 'completeness critic synthesis' },
  ],
}

const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const ALLOWED = '{propext, Classical.choice, Quot.sound}'

const COMMON = `ArkLib Lean 4 Proximity-Gap cone (#444), dir
/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib.
Read FIRST: docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md (E1..E7, §D, §E),
ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md §6. The 50-bridge grind + 5 core angles already
reduced the prize to the m*-growth / BCHKS 1.12 core. Landed substrate to build on: _BridgeB* and
_CoreA1 (mStar_ge_three, deltaStar_le_capacity_sub_two_over_n), _CoreA2 (orbit_bound_iff_BCHKS_budget),
_CoreA3 (weakestSuff_iff_mStarOLog, weakestSuff_le_BCHKS, weakestSuff_imp_BCHKS_needs_reverse),
_CoreA5 (binding_is_monomial_controlled), _CoreA6 (Dstar_le_minorImage_card, plueckerMinor_ne_subsetSum
— a NOVEL Plücker-minor invariant certified different from BCHKS subset-sum).
BUILD: scripts/pg-iterate.sh <file> (lock-free; sorry is a WARNING — READ #print axioms for sorryAx).
HONESTY (paramount): do NOT fabricate a closure of BCHKS / the prize. Axiom-clean (⊆ ${ALLOWED}, no
sorry/native_decide/fake-axiom; paste #print axioms) or honest REDUCED (named Prop) or REFUTED
(countermodel). Never claim the prize closed.`

const SCHEMA = {
  type:'object', additionalProperties:false,
  required:['id','status','summary'],
  properties:{
    id:{type:'string'},
    status:{type:'string', enum:['CLEAN_LANDED','PARTIAL_BOUND','REDUCES_TO_BCHKS','ESCAPE_CANDIDATE','REFUTED','REDUCED','FAILED']},
    axiomsClean:{type:'boolean'}, file:{type:'string'}, keyTheorem:{type:'string'}, axioms:{type:'string'},
    finding:{type:'string'}, summary:{type:'string'},
  },
}

const TARGETS = [
  {id:'A4', file:'_CoreA4_PlateauWidth', task:`The PLATEAU-WIDTH angle. The cascade recursion D*_{2n}(m)=D*_n(m-1) is exact except plateau-doubling at imprimitive directions (n=32 doubled 89-rung pushed m* 3→5). Using _BridgeB27 (plateau only at even b-a) + _CoreA2 orbit structure + _BridgeB30 (mStar_increment_le_plateauWidth), PROVE a bound on the plateau width w per tower level, OR reduce 'w ≤ c' to a precise named combinatorial Prop and compare it to BCHKS. If w=O(1) ⟹ m*=O(log n) (prize). Honest PARTIAL_BOUND / REDUCES_TO_BCHKS.`},
  {id:'A7', file:'_CoreA7_NecessityTight', task:`Prove the reduction is TIGHT (BCHKS NECESSARY, not just sufficient): the CONVERSE 'm*=O(log n) ⟹ a BCHKS-type budget holds'. _CoreA3 already has weakestSuff_iff_mStarOLog and BCHKS_imp_weakestSuff but the reverse weakestSuff⟹BCHKS is flagged open (weakestSuff_imp_BCHKS_needs_reverse). RESOLVE that reverse: either PROVE weakestSuff⟹BCHKS (making prize⟺BCHKS a genuine equivalence = the wall is unavoidable), or show it CANNOT hold / find the gap object (weakestSuff strictly weaker = a real ESCAPE_CANDIDATE worth pursuing). This is the decisive question. Axiom-clean theorem either way, or sharp REDUCED.`},
  {id:'A6deep', file:'_CoreA6deep_MinorTractability', task:`DEEPEN A6 (the novel Plücker-minor invariant). _CoreA6 bounds D*(m) ≤ |forcedGammaImage over minor-locus| and certifies this minor object ≠ BCHKS subset-sum. The KEY question: is the minor-image count ACTUALLY more tractable than the subset-sum count? The minor-locus is a DETERMINANTAL VARIETY (Plücker minor = 0); its point-count has Lang-Weil / Weil-bound theory. PROVE any nontrivial bound on |forcedGammaImage| via the determinantal structure (e.g. the minor is degree-2, so the variety has bounded degree → Lang-Weil gives O(p^{dim}) points → distinct ratios bound). If you can bound it BETTER than the trivial C(n,k+2), that is genuine progress toward the prize via a NON-BCHKS route. Honest PARTIAL_BOUND or REDUCES (name what determinantal input is needed). This is the most promising new angle — push hard.`},
  {id:'A3deep', file:'_CoreA3deep_EscapeCheck', task:`DEEPEN A3 (backward-proof escape check). _CoreA3 proved weakestSuff ≤ BCHKS with the reverse open. CONCRETELY characterize the GAP: is there a specific cascade/orbit configuration where weakestSuff holds but BCHKS fails (a witness that the m*=O(log n) target needs STRICTLY LESS than full BCHKS 1.12)? If yes, formalize that gap object as the SHARPER target (a real escape — the prize needs less than BCHKS). If the gap is empty (every weakestSuff config forces BCHKS), prove weakestSuff⟹BCHKS, confirming the wall. Use the monomial-controlled reduction (_CoreA5) to restrict to the monomial cascade. Axiom-clean theorem + honest verdict ESCAPE_CANDIDATE or wall-confirmation.`},
  {id:'RED', file:'_CoreReductionComplete', task:`ASSEMBLE THE COMPLETE REDUCTION THEOREM. A single axiom-clean theorem chaining the landed bricks:
'δ* lies in the window interior (Johnson, capacity) ⟸ [one explicit named BCHKS-type Prop]', using
_BridgeB48 (D* monotone), B47 (tail), B29 (mStar_tower_shift), B31 (mStar_le_iff_BCHKS), B01/B02/B04
(master identity + Johnson crossing), B50 (assembly), _CoreA1 (mStar_ge_three / δ* upper bound),
_CoreA5 (monomial-controlled). The ONLY remaining hypothesis = the single named BCHKS/m*-growth Prop;
everything else discharged. Do NOT discharge that Prop (it is the open prize). This PROVES the bridge
program is a COMPLETE REDUCTION: the prize is EXACTLY this one combinatorial Prop. Land axiom-clean
with the one named hypothesis stated precisely.`},
]

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, label){
  let acc=[]
  for (const [i,w] of chunk(items,5).entries()){ log(`${label} wave ${i+1} (${w.map(s=>s.id||s).join(',')})`); acc=acc.concat(await pipeline(w, mk)) }
  return acc
}

phase('Finish')
const results = await waved(TARGETS, (T) => agent(
  `${COMMON}

Write/extend ${DIR}/${T.file}.lean (minimal imports). TARGET ${T.id}:
${T.task}
Return the verdict.`,
  {label:`finish:${T.id}`, phase:'Finish', schema:SCHEMA}
), 'Finish')

phase('Verify')
const claimed = results.filter(r => r && (r.status==='CLEAN_LANDED'||r.status==='ESCAPE_CANDIDATE') && r.axiomsClean)
const verified = await waved(claimed, (r) => agent(
  `${COMMON}

ADVERSARIALLY VERIFY ${r.id}. File: ${r.file||'(find it)'}  Key thm: ${r.keyTheorem||'(find it)'}.
Re-run pg-iterate; check for real sorry/admit/native_decide/axiom; run #print axioms; confirm ⊆
${ALLOWED}. Judge FAITHFULNESS HARD: does the theorem express the claimed fact, no vacuous/False
hypothesis, not secretly assuming its conclusion, not a 0=0 dodge? For an ESCAPE_CANDIDATE, confirm
the gap object is GENUINELY weaker than BCHKS (not a renaming). Return the (re)verdict.`,
  {label:`verify:${r.id}`, phase:'Verify', schema:SCHEMA}
), 'Verify')

phase('Critic')
const vmap = new Map(verified.filter(Boolean).map(v=>[v.id,v]))
const fin = results.filter(Boolean).map(r=>vmap.get(r.id)||r)
const critic = await agent(
  `${COMMON}

COMPLETENESS CRITIC — final synthesis of the entire #444 bridge program (50 bridges + 6 structural
closures + 7 core angles A1-A7 + the complete reduction). Answer rigorously, citing brick/angle files:
(1) Is the reduction 'prize ⟺ BCHKS 1.12' now COMPLETE and TIGHT, or does A7/A3deep reveal a genuine
ESCAPE (weakest-suff strictly weaker than BCHKS)? State which.
(2) Is the A6 Plücker-minor invariant a genuinely more-tractable NON-BCHKS route, or does its
determinantal point-count collapse back to the same wall? Verdict with the reason.
(3) What is the SINGLE sharpest irreducible open statement the whole program leaves? One precise sentence.
(4) Honestly: is there ANY realistic in-tree path to the prize, or is it strictly external (proving
BCHKS / the determinantal bound itself)? Name the most promising remaining lever.
(5) List every angle/modality NOT yet attacked that a future agent should try.
Put the full assessment in 'summary'. status='FAILED' (you build nothing) with the assessment in summary,
unless you actually land a Lean artifact.`,
  {label:'critic:final', phase:'Critic', schema:SCHEMA}
)

const landed = fin.filter(r=>['CLEAN_LANDED','PARTIAL_BOUND','ESCAPE_CANDIDATE'].includes(r.status))
const reduces = fin.filter(r=>r.status==='REDUCES_TO_BCHKS')
log(`core-complete: ${landed.length} landed/partial/escape, ${reduces.length} reduce-to-BCHKS`)
return {
  results: fin.map(r=>({id:r.id,status:r.status,file:r.file,keyTheorem:r.keyTheorem,finding:r.finding})),
  escapeCandidates: fin.filter(r=>r.status==='ESCAPE_CANDIDATE').map(r=>({id:r.id,finding:r.finding})),
  criticAssessment: critic?.summary || critic?.finding,
}
