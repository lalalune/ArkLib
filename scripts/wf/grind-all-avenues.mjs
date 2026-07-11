export const meta = {
  name: 'grind-all-avenues',
  description: 'Exhaustively grind every remaining #444 open avenue: land real bricks, refute, classify-to-wall, prize-test',
  phases: [
    { title: 'Grind', detail: 'one agent per avenue: axiom-clean brick / refutation / rigorous reduce-to-wall / prize-regime test' },
    { title: 'Verify', detail: 'adversarial axiom + faithfulness audit of every LANDED/REFUTED claim' },
    { title: 'Synthesize', detail: 'the avenue resolution ledger' },
  ],
}

const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const ALLOWED = '{propext, Classical.choice, Quot.sound}'

const COMMON = `ArkLib Lean 4 Proximity-Gap cone (#444), dir
/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib.
Read FIRST: docs/kb/deltastar-444-prize-regime-established-2026-06-16.md (what holds),
docs/kb/deltastar-444-audit-corrections-2026-06-16.md (the artifact/laundered corrections — ESPECIALLY
§A0: the far-line δ* is a Johnson-LOCKED PROXY δ*=1/2+1/n, m*=n/4-1 LINEAR; the "climb to capacity"
was an artifact, RETRACTED), docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md (the
bridge ledger + the complete reduction prize⟺BCHKS-1.12), ArkLib/Data/CodingTheory/ProximityGap/CLAUDE.md.
BUILD: scripts/pg-iterate.sh <file> (lock-free; sorry is a WARNING — READ #print axioms for sorryAx).
Exact computation: scripts/probes/probe_*.py or scripts/rust-pg binaries. External-paper claims:
WebSearch/WebFetch are available — use them to check what a cited arXiv result actually states.
CONTEXT: the prize = prove the worst-case MCA floor (NOT the far-line proxy) beyond Johnson =
BCHKS Conjecture 1.12 (distinct r-fold subset-sum |Σ_r(μ_s)| ≤ q·ε* at r≈log m) = the char-p
deep-moment Wick bound. My memory: nearly every analytic route REDUCES to this wall. Genuinely
landable in-tree: exact energy closed forms, orbit/determinantal structure, p-independent counts.
HONESTY (paramount): NEVER fabricate a closure of the prize. Honest outcomes:
 - LANDED: a NEW axiom-clean Lean brick (⊆ ${ALLOWED}, no sorry/native_decide/fake-axiom; paste
   #print axioms) proving a real (possibly partial / conditional-with-named-hyp) result.
 - REFUTED: machine-checked countermodel (decide / exact probe).
 - REDUCES_TO_WALL: a rigorous argument (ideally a Lean reduction) that this avenue is equivalent to
   / implied by BCHKS-1.12 / the char-p Wick bound — state the EXACT reduction, don't just assert.
 - PRIZE_TEST: for an external tool, the precise prize-regime verdict (does it give M(n)≤C√(n log m)
   in the thin regime n=2^μ, q=n^β? or vanish / give a weaker bound? with the computed constant).`

const SCHEMA = {
  type:'object', additionalProperties:false,
  required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['LANDED','REFUTED','REDUCES_TO_WALL','PARTIAL_BOUND','PRIZE_TEST','REDUCED','FAILED']},
    axiomsClean:{type:'boolean'}, file:{type:'string'}, keyTheorem:{type:'string'}, axioms:{type:'string'},
    finding:{type:'string', description:'the precise result with computed values / the exact reduction / the prize-regime constant'},
    summary:{type:'string'},
  },
}

const AVENUES = [
  // ---- LANDABLE in-tree (real brick likely) ----
  {id:'L1-E6closed', file:'_AvL1_E6ClosedForm', task:`Determine and PROVE the exact char-0-faithful additive-energy closed form E_6(μ_n) extending the ladder E_2=3n²−3n, E_3=15n³−45n²+40n, E_4=105n⁴−630n³+1435n²−1155n, E_5=945n⁵−9450n⁴+39375n³−77175n²+57456n. Compute E_6 exactly by enumeration (probe) at n=4,8,16,32, fit the degree-6 polynomial, and LAND an axiom-clean Lean brick proving E_6(μ_n) = <closed form> for the small cases by decide + state the closed form (as the in-tree E_4/E_5 bricks do). Cite the leading coeff (2·6−1)‼=10395.`},
  {id:'L2-E7closed', file:'_AvL2_E7ClosedForm', task:`Same as L1 for E_7(μ_n) (leading coeff (2·7−1)‼=135135). Compute exactly at n=4,8,16, fit degree 7, land axiom-clean small-case bricks + the closed form.`},
  {id:'L3-StepLaw', file:'_AvL3_GaussianStepLaw', task:`PROVE the per-step energy bound E_{r+1}(μ_n) ≤ (2r+1)·n·E_r(μ_n) (GaussianStepLaw) — iterating it from E_1=n gives the Wick ceiling E_r ≤ (2r−1)‼·n^r in char-0. Use the exact closed forms (E_2..E_5 in-tree, E_6/E_7 from L1/L2) to verify it for r≤6 by decide, and attempt the general char-0 proof via the nonprincipal_crossstep_recursion (in-tree: S_{r+1}=n·S_r+crossNP_r). Land axiom-clean small cases + the general step IF provable, else REDUCE to the cross-step bound.`},
  {id:'L4-MinorDeg', file:'_AvL4_MinorDegreeUniform', task:`DEEPEN the determinantal lever (_CoreA6deep). The bound D*(2)≤2·span needs the single-parameter minor factorization to be DIRECTION-UNIFORM at the binding. PROVE: for the worst monomial direction (a,b) at the binding radius, the Plücker minor polynomial minorPoly has degree ≤ 2 in the relevant parameter, UNIFORMLY (independent of (a,b)). If provable, the determinantal bound becomes unconditional for depth 2. Use SchurLagrangeBridge (γ_R=−h_{a−k}(R)/h_{b−k}(R)). Land axiom-clean or REDUCE to the precise uniformity Prop.`},
  {id:'L5-DedupStrict', file:'_AvL5_DedupStrictness', task:`The A3 gap: is the dedup D*(m) ≤ Σ_r(μ_s) STRICT at log depth? Compute, EXACTLY at small n, both D*(m) (distinct forced-γ count) and Σ_r=|{r-fold subset sums}| at matched (s,r), and measure the dedup slack Σ−D as a function of depth. Determine whether the slack VANISHES at the binding depth (⟹ wall) or stays positive (⟹ prize needs strictly less than BCHKS). LAND a Lean brick with the exact small-n slack values (decide) + the honest verdict.`},
  {id:'L6-W3bound', file:'_AvL6_W3CubicBound', task:`The di Benedetto conditional needs T_3(μ_n)=O(n³), i.e. W_3 ≤ Cn³ where W_3 is the fixed-weight-6 (r=3) char-p bad-prime wraparound count / the depth-3 additive energy excess. Compute W_3 exactly at n=4,8,16,32 across multiple primes; determine the exact constant C and whether W_3 ≤ Cn³ holds with C absolute. The in-tree E_3=15n³−45n²+40n is the char-0 value; W_3 is the char-p excess (=0 generically per the audit, nonzero only at Fermat primes). LAND a brick proving W_3=0 for generic prize primes (the No-Excess r=3) by exact computation + the cubic char-0 bound, or REDUCE precisely.`},
  {id:'L7-OrbitBinder', file:'_AvL7_OrbitSizeAtBinder', task:`Formalize the now-VERIFIED orbit-size-at-binder growth law: the binding far direction (a,b) at radius s*=n/2−1 has orbit size S=n/gcd(b−a,n) and m*=n/4−1 (LINEAR, the Johnson-lock — see audit §A0). Land an axiom-clean brick stating: for the far-line proxy, s*=n/2−1, m*=n/4−1, δ*=1/2+1/n (the Johnson-lock law), with the orbit-count crossing (O≤d) at the binder. Use OrbitCountCrossingLaw. This formalizes the corrected (non-artifact) law.`},
  {id:'L8-PlateauE3', file:'_AvL8_PlateauExcessE3', task:`Attack the plateau-excess at the primitive binding radius via the E3 monomial partial-orbit count. The plateau (where D stays constant before crossing) is governed by the orbit structure (B27: doubling only at even b−a). With the corrected m*=n/4−1 linear law, the "plateau width" per tower level is now computable. Prove the exact plateau-excess = |oddPart| relation (in-tree _Close20 cited it) axiom-clean, or document precisely what the plateau width is for the far-line proxy.`},
  {id:'L9-SubsetSpec', file:'_AvL9_SubsetSumSpectrum', task:`The BCHKS object directly: |Σ_r(μ_s)| = #distinct r-fold subset sums of μ_s. Compute exactly at small (s,r), establish the growth-law structure (is it ~3^{s/2}? polynomial? — relate to _AttackThreePow which found 3^{n/2} is an UPPER bound), and land axiom-clean small-case counts (decide) + the exact upper bound |Σ_r(μ_{2N})| ≤ 3^N (the ζ^N=−1 collapse). State the gap to the BCHKS budget.`},
  {id:'L10-Staircase', file:'_AvL10_SchurMinorStaircase', task:`O=1 / j*=2 persistence as n→∞ (SchurMinorStaircase): the over-determination codimension at the binder. With m*=n/4−1 (corrected), characterize the binding-codim j* and whether the orbit count O at the binder stays =1. Land an axiom-clean brick on the codim/orbit-count structure at the corrected binder, or document.`},
  // ---- WALL-CLASSIFICATION (rigorous reduce-to-wall + partials) ----
  {id:'W1-DCWick', file:'_AvW1_DCWickClassify', task:`The DC-subtracted Wick bound A_r=E_r−n^{2r}/q ≤ (2r−1)‼·n^r at depth r≈log q is THE wall. The char-0 bound A_r≤Wick is proven (Lam-Leung); the open part is the char-p transfer at r≈89. Produce a RIGOROUS reduction: state precisely (ideally as a Lean Prop) the exact char-p inequality needed, why r≈log q is forced, and that it is equivalent to BCHKS-1.12 / the Paley sup-norm. Land the reduction Lean brick (the conditional bridge: A_r-bound ⟹ prize) axiom-clean if not already in-tree; do NOT discharge the open input.`},
  {id:'W2-Spur', file:'_AvW2_SpurChebotarev', task:`Spur_r(p) = #{bad primes p | N(σ_T)} (spurious mod-p vanishing count). The surviving prime class is p≡1 mod 8 (m≥3), density 1/4 (in-tree Chebotarev cut). Compute Spur_r(p) structure at small r; determine whether an effective-Chebotarev (Lagarias-Odlyzko) bound gives Spur_r(p) small UNIFORMLY at depth r~log q. Land what is provable (the Chebotarev density / the per-relation norm bound p≤w^{2^{m-1}}) axiom-clean, REDUCE the uniform bound to the effective-PNT input.`},
  {id:'W3-NonprincEnergy', file:'_AvW3_NonprincipalEnergy', task:`The nonprincipal energy crux (S-M1'): E_r'=A_r ≤ K^r(2r−1)‼·n^r to depth r≈ln q with K=O(1) absolute. The exact identity Σ_{b≠0}‖η_b‖^{2r}=q·E_r−n^{2r} is in-tree (nonprincipal_energy_eq). Classify: prove the K=1 case holds at clean rungs (small r) by exact computation, and REDUCE the depth-r≈89 absolute-K bound to the wall, stating the precise open Prop. Do not overclaim K=1 (memory: the c_r tick-up at r~log p is the DC/wraparound, the absolute bound is open).`},
  {id:'W4-CliqueOrbits', file:'_AvW4_CliqueOrbitCount', task:`#clique-orbits(m) / #K-orbits = the irreducible cyclotomic-collision content (the clique reformulation of D*(m)). Compute the clique-orbit count exactly at small n; determine whether it is O(1) or grows. Bridge NubsCarson's proven shallow #bad-scalar counts (r=3,4) to 0xSolace's #clique-orbits if they coincide. Land axiom-clean small-case counts + the honest growth verdict.`},
  {id:'W5-AutocorrRec', file:'_AvW5_AutocorrRecursion', task:`char-p autocorrelation recursion (wf-M3): does the period autocorrelation recursion give a deep-moment bound? The exact identity Cov(η_a,η_b)=−Var/(m−1) (exchangeable white-noise, in-tree) is the 2nd-order content. Determine whether any higher-order autocorrelation recursion yields a bound BEYOND the 2nd-moment Johnson level, or whether it reduces (memory: periods are exchangeable, 2nd-order = Johnson). Land the recursion brick or REDUCE.`},
  // ---- EXTERNAL-TOOL PRIZE-REGIME TESTS ----
  {id:'X1-SumProduct', file:'_AvX1_SumProductTest', task:`PRIZE-REGIME TEST: effective sum-product with QUANTIFIED constants (the Lens-1 avenue). Does a current effective sum-product / Burgess-type bound (check the literature via WebSearch — Murphy-Rudnev-Shkredov, Shkredov sumsets) give M(n)=max_b|η_b| ≤ C√(n log m) for the thin subgroup μ_n at n=2^μ, q=n^β, β≈4? Compute the exponent it yields at β=4 and compare to the needed 1/2. Verdict: does it cross the Burgess barrier or vanish? Be precise with the exponent.`},
  {id:'X2-OSV', file:'_AvX2_OSVCurveBlend', task:`PRIZE-REGIME TEST: OSV short-Weil curve-blend (arXiv:2211.07739) for the dilation family. WebFetch/search the paper. Does attaching a bounded-degree curve to μ_n revive a Weil-type bound below the √q threshold in the thin regime? The memory caveat: V_r is 0-dimensional ⟹ standard Weil vacuous. Determine if OSV's blend escapes the 0-dim obstruction. Precise verdict.`},
  {id:'X3-ThetaFE', file:'_AvX3_ThetaFEQuadratic', task:`PRIZE-REGIME TEST: theta functional equation for the quadratic reparametrization x↦x² (metaplectic self-similarity on μ_n). Does the metaplectic/theta self-similarity of the squaring map on the 2-power subgroup give a sup-norm bound on η_b? Test the mechanism at small n (does |η_b| under the theta-FE recursion stay √n-controlled?). Verdict + any computation.`},
  {id:'X4-LiuZhou', file:'_AvX4_LiuZhouTower', task:`PRIZE-REGIME TEST: Liu-Zhou subgroup-restriction eigenvalue recursion up the dyadic tower (generalized Paley graph eigenvalue). WebSearch the Liu-Zhou subgroup-restriction inequality. Does iterating it up the μ_{2^μ} tower give M(2^μ) ≤ C√(n log m)? The in-tree η_b^{(μ)}=η_b^{(μ-1)}+η_{bω}^{(μ-1)} parallelogram is the tower step. Test whether the recursion is bounded (memory: M²/n plateaus at log p ⟹ C≈1) or grows. Precise verdict.`},
  {id:'X5-FKMS', file:'_AvX5_FKMSBilinear', task:`PRIZE-REGIME TEST: FKMS bilinear-below-Polya-Vinogradov (arXiv:2511.094xx if real — VERIFY the cite via WebSearch; if fabricated, say so) via the m-fixed 2-power coset structure. Does a bilinear-form bound exploit the coset structure to beat √q? The in-tree bilinear lane gives unconditional n^{2/3}. Determine if FKMS improves it in-regime. Precise verdict + check the citation is real.`},
  {id:'X6-MRS', file:'_AvX6_MurphyRudnevShkredov', task:`PRIZE-REGIME TEST: Murphy-Rudnev-Shkredov 49/20 energy refinement (arXiv:1712.00410) fed into the entropy/Kesten route. WebFetch the paper; verify the 49/20 additive-energy exponent. Does it improve the di Benedetto T_2/T_3 energy inputs (currently Sidon-floor T_2=2)? Note: the audit flagged a "proven t_2=49/20" claim that CONTRADICTS the Sidon t_2=2 — resolve which is correct for μ_n. Precise verdict.`},
  {id:'X7-Stepanov', file:'_AvX7_StepanovDirect', task:`PRIZE-REGIME TEST: Stepanov/Rédei auxiliary-polynomial method applied DIRECTLY to the eigenvalue M(n)=max_b|η_b| (not via additive energy). Does an auxiliary-polynomial construction bound the number of large-|η_b| frequencies or |η_b| itself below √(n log m)? The in-tree _DepthRStepanovNoGo and confluent-Stepanov no-gos suggest it reduces — confirm or find the gap. Precise verdict + cite the in-tree no-go.`},
]

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, label){
  let acc=[]
  for (const [i,w] of chunk(items,6).entries()){ log(`${label} wave ${i+1}/${Math.ceil(items.length/6)} (${w.map(s=>s.id||s).join(',')})`); acc=acc.concat(await pipeline(w, mk)) }
  return acc
}

phase('Grind')
const results = await waved(AVENUES, (A) => agent(
  `${COMMON}

AVENUE ${A.id}. Suggested file (if you land/refute): ${DIR}/${A.file}.lean.
${A.task}
Return the structured verdict with precise computed values / the exact reduction / the prize-regime constant in 'finding'.`,
  {label:`grind:${A.id}`, phase:'Grind', schema:SCHEMA}
), 'Grind')

phase('Verify')
const claimed = results.filter(r => r && (r.outcome==='LANDED'||r.outcome==='REFUTED'||r.outcome==='PARTIAL_BOUND') && (r.axiomsClean!==false))
const verified = await waved(claimed, (r) => agent(
  `${COMMON}

ADVERSARIALLY VERIFY a claimed ${r.outcome} for avenue ${r.id}.
File: ${r.file||'(find it)'}  Key thm: ${r.keyTheorem||'(find it)'}.
Re-run pg-iterate; open the file; look for real sorry/admit/native_decide/axiom; run #print axioms;
confirm ⊆ ${ALLOWED}. Judge FAITHFULNESS HARD: does it genuinely prove the claimed math (not a
tautology / vacuous hypothesis / a value laundered without computation)? Re-run any cited probe to
confirm the numbers. For PARTIAL_BOUND/conditional, confirm the named hypothesis is explicit, not
hidden. Return the (re)verdict, downgrading if not genuine.`,
  {label:`verify:${r.id}`, phase:'Verify', schema:SCHEMA}
), 'Verify')

phase('Synthesize')
const vmap = new Map(verified.filter(Boolean).map(v=>[v.id,v]))
const fin = results.filter(Boolean).map(r=>vmap.get(r.id)||r)
const tally = {}
for (const r of fin) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`grind-all-avenues done: ${JSON.stringify(tally)}`)
return {
  tally,
  landed: fin.filter(r=>r.outcome==='LANDED'||r.outcome==='PARTIAL_BOUND').map(r=>({id:r.id,file:r.file,keyTheorem:r.keyTheorem,finding:r.finding})),
  refuted: fin.filter(r=>r.outcome==='REFUTED').map(r=>({id:r.id,finding:r.finding})),
  wall: fin.filter(r=>r.outcome==='REDUCES_TO_WALL').map(r=>({id:r.id,finding:r.finding})),
  prizeTests: fin.filter(r=>r.outcome==='PRIZE_TEST').map(r=>({id:r.id,finding:r.finding})),
  all: fin.map(r=>({id:r.id,outcome:r.outcome,finding:(r.finding||'').slice(0,300)})),
}
