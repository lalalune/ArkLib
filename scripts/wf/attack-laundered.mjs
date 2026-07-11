export const meta = {
  name: 'attack-laundered',
  description: 'Attack every laundered/larp/phantom/vacuous/overclaimed #444 item: land real proof, refute, or document',
  phases: [
    { title: 'Attack', detail: 'one agent per target — verify the claimed math; land axiom-clean, refute, or document absence' },
    { title: 'Verify', detail: 'adversarial axiom + faithfulness audit of every LANDED/REFUTED claim' },
    { title: 'Synthesize', detail: 'the resolution ledger' },
  ],
}

const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const ALLOWED = '{propext, Classical.choice, Quot.sound}'

const COMMON = `ArkLib Lean 4 Proximity-Gap cone (#444), dir
/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib.
Read FIRST: docs/kb/deltastar-444-audit-corrections-2026-06-16.md (the audit of laundered/phantom
items), docs/kb/deltastar-444-prize-regime-established-2026-06-16.md, ArkLib/Data/CodingTheory/
ProximityGap/CLAUDE.md §6 (honesty).
BUILD: scripts/pg-iterate.sh <file> (lock-free; sorry is a WARNING — READ #print axioms for sorryAx).
For exact small-n computation use scripts/probes/probe_*.py or scripts/rust-pg binaries.
HONESTY (paramount): your job is to DESTROY a laundered/larp/phantom/vacuous claim by replacing it
with the TRUTH. Three honest outcomes:
 (a) LANDED_REAL — the claimed math is TRUE: write a NEW axiom-clean Lean brick that actually proves
     it (⊆ ${ALLOWED}, no sorry/native_decide/fake-axiom; paste #print axioms). Make the phantom real.
 (b) REFUTED — the claim is FALSE: prove a machine-checked countermodel (decide / exact probe) and
     write it as a *_REFUTED brick or a documented disproof.
 (c) DOCUMENTED_ABSENT/VACUOUS — the cited file does not exist, or exists but is a trivial tautology
     proving nothing: confirm by find/grep/build and state precisely what is and isn't there.
NEVER fabricate a closure or cite a file you did not build. Return the structured verdict.`

const SCHEMA = {
  type:'object', additionalProperties:false,
  required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['LANDED_REAL','REFUTED','DOCUMENTED_ABSENT','DOCUMENTED_VACUOUS','REDUCED','FAILED']},
    file:{type:'string'}, keyTheorem:{type:'string'}, axioms:{type:'string'},
    finding:{type:'string', description:'the precise truth: what was proven/refuted/found-absent, with the computed values'},
    summary:{type:'string'},
  },
}

const TARGETS = [
  {id:'PHANTOM-SweepA4x', file:'_AttackSweepA4x_DyadicRigidity', task:`The comments cite a "char-0 rigidity chain" Sweep_A41..A48 (theorems dyadic_vanishing_sum_paired, multiscale_dvd, lacunary_coset_rigidity, general_dyadic_rigidity) as "landed axiom-clean" — but NONE of these files exist in the tree or any branch (audit §C). ATTACK: (1) confirm absence (find/grep/git ls-tree fork/main). (2) Then judge the MATH: is "char-0 dyadic vanishing rigidity" (a vanishing sum of 2^m-th roots of unity over a paired/antipodal-closed set forces dyadic coset structure, Lam-Leung style) actually TRUE? If a clean small case is true and provable, LAND a real axiom-clean brick proving the depth-2 antipodal/paired vanishing rigidity (you already have _Close07c/B05 antipodal machinery to build on). If the general claim is the trinomial-only special case the comments later admitted, document that limitation. Outcome: DOCUMENTED_ABSENT + (LANDED_REAL for the true core, or note the limitation).`},
  {id:'PHANTOM-DefectOnset', file:'_AttackDefectOnset_EnergySandwich', task:`The comment cites _DefectOnsetOvershoot.lean ("9 thms, axiom-clean, real green build") proving an "exact energy sandwich" — the file DOES NOT EXIST (audit §C). ATTACK: confirm absence. Then judge: is the claimed energy sandwich (some 2*E(mu_n) <= (n+2)|G|^2 even-n bound, or an E_r two-sided bracket) TRUE and provable? If yes, LAND a real axiom-clean brick (the exact E_2=3n^2-3n identity is in-tree; build a real bracket). Outcome: DOCUMENTED_ABSENT + LANDED_REAL or REFUTED.`},
  {id:'PHANTOM-ThreePow', file:'_AttackThreePow_SubsetSumExact', task:`The comment cites SubsetSumThreePowExact.lean (the "3^{n/2} exact subset-sum count, axiom-clean spine anchor") — the file DOES NOT EXIST (audit §C; a comment admits it was "wiped"). ATTACK: confirm absence. Then VERIFY THE MATH by exact computation: is the count of distinct r-fold subset-sums (or some specific subset-sum spectrum) of mu_{2^m} actually 3^{n/2}, or related? Compute the exact value for small n (n=4,8,16) with a probe. If a clean closed form is TRUE, LAND a real axiom-clean Lean brick proving the small cases by decide + the closed form. If 3^{n/2} is wrong, REFUTE with the computed value. Outcome: DOCUMENTED_ABSENT + LANDED_REAL or REFUTED.`},
  {id:'LARP-PlotkinHalfCap', file:'_AntipodalPlotkinHalfCap', task:`_AntipodalPlotkinHalfCap.lean EXISTS but its headline claim ("antipodal/odd far-line route caps at delta* >= 1/2") was RETRACTED by the author (far-line delta* actually RISES toward... actually per the 2026-06-16 audit, the over-det far-line is a JOHNSON-LOCKED PROXY delta*=1/2+1/n -> 1/2, NOT a >= 1/2 cap and NOT a climb). ATTACK: read the existing file; determine what it actually proves vs claims. CORRECT it: either (a) if its theorems are about the antipodal/odd structure and are sound, fix the DOCSTRING to state the correct Johnson-lock conclusion (delta*_farline=1/2+1/n, a proxy, NOT a cap isolating a residual), or (b) if the theorems themselves encode the false cap, mark them REFUTED with the countermodel. Keep it axiom-clean. Outcome: REDUCED (docstring corrected) or REFUTED.`},
  {id:'VACUOUS-Close27', file:'_AttackClose27_Plateau', task:`_Close27_PlateauWidthDecision.lean and _Close27_ImprimitivePlateauExcess.lean both "landed axiom-clean deciding OPPOSITE horns" — self-flagged as trivial tautologies (omega/decide/rfl) where the "decision" is prose-only (audit §E). ATTACK: read both files; confirm whether every theorem is a content-free tautology. If vacuous, DOCUMENT_VACUOUS precisely (list the trivial statements). Then ATTEMPT the REAL content: the plateau-width decision is "is the plateau excess w bounded (<=c) per tower level" — using the in-tree B27 dichotomy (plateau only at even b-a) + _Close26 (primitive clean recursion) + the verified m*=n/4-1 LINEAR law, prove a REAL non-trivial statement about the imprimitive plateau excess (e.g. w = |oddPart| exactly, axiom-clean) OR document that the real decision reduces to the open growth law. Outcome: DOCUMENTED_VACUOUS + LANDED_REAL or REDUCED.`},
  {id:'OVERCLAIM-Mu6Pin', file:'_AttackMu6Pin_Audit', task:`Mu6ConditionalPin.lean has deltaStar_pin_mu6_dim4: delta*=59/64=0.922 "axiom-clean at literal prize eps*=2^-128" — flagged overclaimed (n=6 is not the prize regime; landauSqEnvelope toy bound) (audit §E). ATTACK: read the file, run its #print axioms, and judge HONESTLY: is the theorem TRUE as stated (a real pin for that tiny instance) but MIS-FRAMED as prize-relevant, or is it vacuous/laundered? Do NOT edit unless needed; produce an honest audit verdict (the theorem may be a fine tiny-instance pin that should simply not be cited as prize-regime). Outcome: REDUCED (audit verdict, note in finding) or REFUTED.`},
  {id:'OVERCLAIM-NotRamanujan', file:'_AttackNotRamanujan_Audit', task:`NotRamanujanLowerBound.lean's not_ramanujan_of_energy_lb docstring asserts a "PROVEN char-0 energy LOWER bound E_r(mu_n) >= (2r-1)!!*(n/2)_r*2^r" but the lower bound it cites may not be the proven object (audit §E). ATTACK: read the file + CharZeroEnergyLowerBound.lean + GenericSuperDiagonalLower.lean; run #print axioms; determine whether the cited lower bound is actually PROVEN axiom-clean and whether the docstring faithfully describes it. If the docstring overclaims, state the precise gap. Outcome: REDUCED (honest audit + corrected docstring if you can) or note the discrepancy.`},
  {id:'AUDIT-LamLeung', file:'_AttackLamLeung_Audit', task:`LamLeungUnconditionalQ.lean is cited for the "char-0 Wick energy bound E_r(mu_n) <= (2r-1)!!*n^r PROVEN axiom-clean via Lam-Leung", but memory warns Mathlib LACKS Lam-Leung so the full bound may not be formalized. ATTACK: read LamLeungUnconditionalQ.lean, run #print axioms on its main theorems, and determine EXACTLY what is proven (the full E_r <= Wick for all r? a restricted r<=3? a conditional?). Report the precise theorem statements + axioms. If it proves less than the headline, document the gap. Do NOT overclaim. Outcome: REDUCED (precise audit of what is/isn't proven).`},
  {id:'BUG-B02B03', file:'_AttackB02B03_OffByOne', task:`_BridgeB02.lean and _BridgeB03.lean inherit the off-by-one (B02 uses delta* = 1 - rho - (mstar-1)/n; the corrected form is 1 - rho - mstar/n, capacity-delta*=mstar/n; B01/B04 already fixed). ATTACK: fix B02 and B03 to the corrected convention (Johnson-crossing should use the corrected master gap; binding-depth m*>=1 anchor should use 1-s/n). Rebuild both axiom-clean. Outcome: LANDED_REAL (both rebuilt with corrected convention, axioms pasted).`},
  {id:'LAUNDER-Dstar1Pdep', file:'_AttackDstar1_PDependence', task:`The comments laundered "D*(1) exact p-independent" — but D*(1) (the m=1 / under-det edge) is p-DEPENDENT (3936@p=65537 vs 3984@p=1048609, audit §B); only the over-det m>=2 count is p-independent. ATTACK: write a probe (or extend an existing one) that COMPUTES D*(m) at two primes for n=16 and CONFIRMS m=1 differs (p-dep) while m>=2 is identical (p-indep), printing the exact values. Save it as scripts/probes/probe_dstar_pdependence_cliff.py with a clear header. Then LAND a small axiom-clean Lean note IF there is a clean field-cardinality-independence statement for the over-det count (ResolveFieldIndependent.lean already has one — verify and cite it). Outcome: LANDED_REAL (probe + cite the p-indep brick) documenting the cliff precisely.`},
]

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, label){
  let acc=[]
  for (const [i,w] of chunk(items,5).entries()){ log(`${label} wave ${i+1} (${w.map(s=>s.id||s).join(',')})`); acc=acc.concat(await pipeline(w, mk)) }
  return acc
}

phase('Attack')
const results = await waved(TARGETS, (T) => agent(
  `${COMMON}

TARGET ${T.id}. Suggested new file (if you land/refute): ${DIR}/${T.file}.lean.
${T.task}
Return the structured verdict with the precise computed values in 'finding'.`,
  {label:`attack:${T.id}`, phase:'Attack', schema:SCHEMA}
), 'Attack')

phase('Verify')
const claimed = results.filter(r => r && (r.outcome==='LANDED_REAL' || r.outcome==='REFUTED'))
const verified = await waved(claimed, (r) => agent(
  `${COMMON}

ADVERSARIALLY VERIFY a claimed ${r.outcome} for target ${r.id}.
File: ${r.file||'(find it)'}  Key thm: ${r.keyTheorem||'(find it)'}.
Re-run pg-iterate; open the file; look for real sorry/admit/native_decide/axiom; run #print axioms;
confirm ⊆ ${ALLOWED}. Judge FAITHFULNESS HARD: for LANDED_REAL, does it genuinely prove the claimed
math (not a tautology / vacuous hypothesis)? For REFUTED, is the countermodel real (decide/exact)?
Confirm the computed values in the finding by re-running the probe if cited. Return the (re)verdict.`,
  {label:`verify:${r.id}`, phase:'Verify', schema:SCHEMA}
), 'Verify')

phase('Synthesize')
const vmap = new Map(verified.filter(Boolean).map(v=>[v.id,v]))
const fin = results.filter(Boolean).map(r=>vmap.get(r.id)||r)
const tally = {}
for (const r of fin) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`attack-laundered done: ${JSON.stringify(tally)}`)
return {
  tally,
  results: fin.map(r=>({id:r.id, outcome:r.outcome, file:r.file, keyTheorem:r.keyTheorem, finding:r.finding})),
}
