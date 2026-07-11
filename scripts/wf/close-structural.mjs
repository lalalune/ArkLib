export const meta = {
  name: 'deltastar-close-structural',
  description: 'Close every CLOSEABLE structural thread of the δ* bridge program (E6 bijection, E5 recursion) (#444)',
  phases: [
    { title: 'Close', detail: 'deep multi-approach proof attempts on the off-wall structural obligations' },
    { title: 'Verify', detail: 'adversarial axiom + faithfulness audit of every CLOSED claim' },
    { title: 'Synthesize', detail: 'what closed, what remains the wall' },
  ],
}

const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const ALLOWED = '{propext, Classical.choice, Quot.sound}'

const COMMON = `ArkLib Lean 4 Proximity-Gap cone (#444), dir
/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib.
Read FIRST: docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md (E1..E7,P1..P6 + §D
corrections + §E ledger), ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md §6 (honesty), and your
substrate + the existing brick you are extending.
BUILD: scripts/pg-iterate.sh <file> (lock-free; non-quiet prints #print axioms; sorry is only a
WARNING so READ the axiom output to detect sorryAx).
HONESTY (paramount): CLEAN_LANDED only if it elaborates with NO error, NO real sorry/admit/
native_decide/fake-axiom, and #print axioms ⊆ ${ALLOWED}. Paste the axiom output. A genuine
reduction modulo an explicitly-named Prop is REDUCED (name it). A tautology / vacuous-False-
hypothesis is VACUOUS. NEVER fake LANDED. Iterate persistently — these are hard; budget is not a
constraint. If after real effort it resists, REDUCE to the sharpest named residual.`

const SCHEMA = {
  type:'object', additionalProperties:false,
  required:['id','status','axiomsClean','summary'],
  properties:{
    id:{type:'string'}, status:{type:'string', enum:['CLEAN_LANDED','REDUCED','VACUOUS','FAILED']},
    axiomsClean:{type:'boolean'}, file:{type:'string'}, keyTheorem:{type:'string'},
    axioms:{type:'string'}, gap:{type:'string'}, summary:{type:'string'},
  },
}

// The closeable structural targets — each is OFF the analytic BGK wall (pure combinatorics / orbit
// structure), so genuinely provable. Several independent approaches per hard target.
const TARGETS = [
  {id:'C07a', file:'_Close07a_DoublingFoldMap', t:'E6',
   task:`PROVE the E6 even-fold bijection (B07 'DoublingBijection'): #bad_{2n}(k,2m') = #bad_n(k/2,m').
APPROACH A (explicit fold map). Define the graded obstruction count #bad_N(k,m) in Lean as the
Finset.card of distinct nonzero graded frequency vectors fhat(A,m) over (k+m)-subsets A ⊆ ZMod N
with fhat(A,j)=0 for 1≤j<m, where fhat(A,j)[bin] = Σ_{a∈A, j*a≡bin mod (N/2)} sign. Construct the
explicit doubling fold Φ : (subsets of ZMod 2n) → (subsets of ZMod n) and prove it induces a
BIJECTION on the relevant graded loci preserving the m↦2m' grading and k↦k/2. This is pure
combinatorics (p-INDEPENDENT, off the BGK wall). It is hard to formalize; if the full bijection
resists, land the explicit fold map + the injectivity/surjectivity HALF you can prove, and REDUCE
the remainder to a precisely-named Prop. Verified exactly all-cases at 16↔8 (probe
scripts/probes/probe_2adic_tower_recursion.py) so it is TRUE — find the proof.`,
   sub:'DyadicTowerRecursion'},
  {id:'C07b', file:'_Close07b_DoublingInduction', t:'E6',
   task:`PROVE the same E6 even-fold recursion #bad_{2n}(k,2m')=#bad_n(k/2,m'), APPROACH B
(induction / generating function). Instead of an explicit set bijection, prove it by induction on
the 2-adic descent: the graded frequency vector fhat at level 2n, grade 2m', relates to level n,
grade m' via the antipodal folding (x and -x=ω^n·x bin to opposite signs). Use the η-parallelogram
(DyadicTowerRecursion.sum_tower_split / B09.tower_period_recursion) to split level-2n into level-n +
ω-shift, and show the EVEN grade is preserved while the ODD grade vanishes (B05/B06/B09 core). The
combination gives the count recursion. Land what is axiom-clean; name the residual precisely.`,
   sub:'DyadicTowerRecursion'},
  {id:'C07c', file:'_Close07c_OddGradeVanishesFull', t:'E6',
   task:`PROVE B07's 'OddGradeVanishes' obligation FULLY (not just the abstract antipodal core that
B05/B06/B09 already landed): that the actual graded COUNT #bad_{2n}(k, m)=0 for ODD m. Wire the
proven antipodal-involution vanishing (B05.antipodal_odd_count_zero / B09.antipodal_odd_sum_eq_zero)
to the concrete fhat odd-graded weight by PROVING the missing link 'odd-graded fhat is
anti-invariant under x↦-x on ZMod 2n'. Define fhat in Lean and prove this anti-invariance, then
conclude #bad odd = 0. This closes the odd half of E6 completely. Axiom-clean or sharp REDUCE.`,
   sub:'DyadicTowerRecursion'},
  {id:'C26', file:'_Close26_PrimitiveCleanRecursion', t:'E5',
   task:`PROVE B26's 'hcover_exact' (B' = B.image φ): at a PRIMITIVE far direction (gcd(b-a,n)=1) the
level-2n bad set is EXACTLY the image of the level-n bad set under the doubling embedding φ — i.e.
the dyadic cascade recursion D*_{2n}(m)=D*_n(m-1) holds EXACTLY (no plateau) at primitive
directions. Use the Action-Orbit structure (OrbitCountCrossingLaw / ActionOrbitFRI): at gcd=1 the
orbit is the full group, the doubling map φ is injective on bad-γ orbits, and there is no extra
fixed sub-mu_2 rung (that only appears at even b-a, B27). Prove the exact-cover equality, discharging
B26's hypothesis. This closes the CLEAN (primitive) half of the E5 recursion. Axiom-clean or REDUCE.`,
   sub:'OrbitCountCrossingLaw'},
  {id:'C25', file:'_Close25_LiftOneSided', t:'E5',
   task:`DISCHARGE B25's 'hcover' (B' ⊆ B.image φ ∪ P): the one-sided lift D*_{2n}(m) ≤ D*_n(m-1) +
|P| (plateau term P). Prove the doubling embedding φ maps level-n bad-γ into level-2n bad-γ
(monotone embedding), so every level-2n bad-γ either comes from a level-n one (in B.image φ) or is
a genuinely-new plateau element (in P). This is a covering/counting inequality (Finset.card_le_card
on a union), pure combinatorics. Land it axiom-clean, leaving |P|'s SIZE (the plateau width) as the
named open quantity (= the wall, B28). Axiom-clean or sharp REDUCE.`,
   sub:'OrbitCountCrossingLaw'},
  {id:'C43', file:'_Close43_BaseCasesDecide', t:'E6',
   task:`Define the fhat graded obstruction count in Lean over small ZMod N (N=4,8) and PROVE the
base cases by decide/Finset.card computation: #bad_4(1,1), #bad_4(1,2), #bad_8(2,1)=24 (matches the
probe), #bad_8(2,2)=4, and the recursion instance #bad_16(4,2)=#bad_8(2,1)=40. These concrete
decidable values ANCHOR the E6 recursion (proving the base + one recursion step rigorously). Use
Finset over ZMod N and the decide tactic (NOT native_decide — that adds Lean.ofReduceBool, which is
forbidden). If decide is too slow for N=16, land N=4,8 and the recursion-step CHECK at N=8 vs 4.
Axiom-clean.`,
   sub:'DyadicTowerRecursion'},
]

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, label){
  let acc=[]
  for (const [i,w] of chunk(items,6).entries()){ log(`${label} wave ${i+1} (${w.map(s=>s.id).join(',')})`); acc=acc.concat(await pipeline(w, mk)) }
  return acc
}

phase('Close')
const closed = await waved(TARGETS, (T) => agent(
  `${COMMON}

CLOSE a structural obligation. Write/extend ${DIR}/${T.file}.lean (minimal imports).
TARGET ${T.id} [${T.t}]:
${T.task}
SUBSTRATE: ${T.sub}.lean (read it, reuse its lemmas — do NOT re-derive). Return the verdict.`,
  {label:`close:${T.id}`, phase:'Close', schema:SCHEMA}
), 'Close')

phase('Verify')
const claimed = closed.filter(r => r && r.status==='CLEAN_LANDED' && r.axiomsClean)
const verified = await waved(claimed, (r) => agent(
  `${COMMON}

ADVERSARIALLY VERIFY claimed CLEAN_LANDED structural closure ${r.id}.
File: ${r.file||'(find it)'}  Key thm: ${r.keyTheorem||'(find it)'}.
Re-run pg-iterate; open the file; look for a real sorry/admit/native_decide/axiom; run #print
axioms; confirm ⊆ ${ALLOWED}. Judge FAITHFULNESS HARD: does the theorem actually express the
claimed structural fact (the bijection / the exact cover / the base value), with NO vacuous or
False hypothesis, NO 0=0 dodge, and NOT secretly assuming the very thing it claims to prove? For a
'#bad' count, confirm the fhat definition is the GENUINE graded-frequency count (matches the probe),
not a degenerate stand-in. Return the (re)verdict, downgrading if not genuinely confirmed.`,
  {label:`verify:${r.id}`, phase:'Verify', schema:SCHEMA}
), 'Verify')

phase('Synthesize')
const vmap = new Map(verified.filter(Boolean).map(v=>[v.id,v]))
const final = closed.filter(Boolean).map(r => vmap.get(r.id)||r)
const landed = final.filter(r=>r.status==='CLEAN_LANDED'&&r.axiomsClean)
const reduced = final.filter(r=>r.status==='REDUCED')
const other = final.filter(r=>!['CLEAN_LANDED','REDUCED'].includes(r.status))
log(`close-structural: ${landed.length} CLOSED, ${reduced.length} REDUCED, ${other.length} other of ${final.length}`)
return {
  counts:{closed:landed.length, reduced:reduced.length, other:other.length, total:final.length},
  closed: landed.map(r=>({id:r.id,file:r.file,keyTheorem:r.keyTheorem,summary:r.summary})),
  reduced: reduced.map(r=>({id:r.id,gap:r.gap,summary:r.summary})),
  other: other.map(r=>({id:r.id,status:r.status,gap:r.gap})),
}
