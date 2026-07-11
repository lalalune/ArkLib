export const meta = {
  name: 'lambdaq-assault',
  description: 'Attack the Λ(q) face of the prize from every angle: finite-q/local theory, B_h[g]/dissociativity/flatness sufficient conditions, tower/tensor recursion, interpolation, AND the disproof direction (#444)',
  phases: [
    { title: 'Attack',     detail: '14 Λ(q) angles: Lean bricks, refutations, derivations, disproof attempts' },
    { title: 'Verify',     detail: 'adversarial audit of every claimed landing/refutation' },
    { title: 'Synthesize', detail: 'the Λ(q) ledger' },
  ],
}
const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444 (Ethereum Proximity Prize, ABF26 ePrint 2026/680). Attack the **Λ(q) face**.
THE OBJECT: η : Z_p → C, η(b) = Σ_{x∈μ_n} e_p(b·x) (μ_n = n-th roots of unity, n=2^μ). Its Fourier
support is μ_n with all-ones coefficients. The prize floor M = ‖η‖_∞ = max_{b≠0}|η(b)| ≤ C√(n·log m)
is, in harmonic-analysis language, the **Λ(q) inequality** ‖η‖_{L^q(Z_p)} ≤ C·√q·√n at q ≈ 2 log m
(via M ≤ m^{1/q}‖η‖_q optimized at q≈2 log m; m=(p−1)/n).
PRIZE PARAMS (exact): n=2^30; p≈2^158 so n≈p^{1/5.27} (THIN); m≈2^128; ln m≈88.7; saddle k*≈ln p≈110.
GOAL: EXPONENT 1/2. SOTA: BGK exp 1−o(1). Gap = full half-power.

CRUCIAL STRUCTURE (machine-verified this session — build on it, don't re-derive):
• **Even-q Λ(q) = energy moment.** ‖η‖_{2k}^{2k} = E_k(μ_n) := #{x₁+..+x_k=y₁+..+y_k : xᵢ,yᵢ∈μ_n}. The
  WORST-CASE M sees only the **mean-zero / b≠0** object μ_{2k} := (p·E_k − n^{2k})/(p−1) — the DC term
  n^{2k}/p is SUBTRACTED. The prize ⟺ μ_{2k} ≤ Wick_k := (2k−1)‼·n^k for k up to ≈ln p.
• **For a RANDOM set, μ_{2k} ≈ Wick_k for ALL k** (Khintchine; DC subtracted away). So the ENTIRE Λ(q)
  wall is: does μ_n's MULTIPLICATIVE (rank-1: phases b·x are rank-1 linear in b) structure DEVIATE from
  Gaussian/Wick at deep k≈ln p, before the union-bound saddle? That deviation = the BGK resonance.
• **Pisier iff (arXiv:1704.02969):** Λ(q)-const ≤ A√q with A p-INDEPENDENT for ALL q ⟺ Sidon. μ_n is
  NOT Sidon (E_2=3n²−3n, antipodal excess), so its all-q Λ(q)-const → ∞. BUT the prize needs Λ(q) only at
  a SINGLE FINITE q≈log m — strictly WEAKER than Sidon. The finite-q / LOCAL Λ(q) theory is the live target;
  the Pisier circularity is for the all-q version ONLY.
IN-TREE (axiom-clean, reuse): _LambdaQRudinEndToEnd (Λ(q) bound ⟹ prize floor, FORWARD direction proved);
_OpenCoreMonotoneReduction (μ_{2k}≤Wick via base case μ_2≤Wick_1 PROVEN + one monotone moment-ratio);
_ArcsineIIDFraming (per-phase sub-Gaussian + independence ⟹ floor); _PhaseHypercontractive,
_PhaseMartingaleConcentration. E_2=3n(n−1) EXACT; c_{r−1}=0 vanishing-coeff EXACT.
BUILD: scripts/pg-iterate.sh <file> (lock-free; sorry=WARNING — READ #print axioms). autoImplicit OFF —
declare ALL binders. Minimal imports.
HONESTY (paramount): NEVER fabricate closure. LANDED = axiom-clean (#print axioms ⊆ {propext,
Classical.choice, Quot.sound}, NO sorryAx/native_decide; paste it). A conditional brick with a NAMED open
hyp is LANDED+REDUCED — name the GENUINE open part (the deep-k multiplicative deviation = BGK), don't
silently discharge it. REFUTED = machine countermodel (probe + exact F_p compute). DERIVED = the precise
derivation in 'finding'. Bold in exploration; strict on "proven". Clobber-proof: RETURN full fileContent.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['LANDED','REDUCED','REFUTED','DERIVED','PARTIAL','FAILED']},
    axiomsClean:{type:'boolean'}, file:{type:'string'}, keyTheorem:{type:'string'}, axioms:{type:'string'},
    fileContent:{type:'string'}, finding:{type:'string'}, summary:{type:'string'} },
}

const ANGLES = [
  // --- Λ(q) ↔ energy bridge identities (clean Lean bricks) ---
  {id:'L1-meanzero-identity', file:'_LambdaQMeanZeroEnergy', t:`Land the EXACT identity ‖η−mean‖_{L^{2k}(Z_p)}^{2k} = μ_{2k} = (p·E_k − n^{2k})/(p−1) (the mean-zero L^{2k} norm IS the DC-subtracted energy moment). This is the precise Λ(q)↔energy bridge for the worst-case object. Land it axiom-clean as an abstract Parseval/moment identity (you may state E_k, μ_{2k} as given reals satisfying the relation, and prove the L^∞-from-L^{2k} consequence M^{2k}≤(p−1)μ_{2k}). Connects _LambdaQRudinEndToEnd to _OpenCoreMonotoneReduction.`},
  {id:'L2-spectral-moment', file:'_LambdaQSpectralMoment', t:`Land the identity Λ(2k) = spectral moment: ‖η‖_{2k}^{2k} = (1/p)·tr(A^{2k}) where A is the adjacency of the generalized Paley graph Cay(F_p,μ_n) (η_b are its eigenvalues). So the Λ(q) bound = a bound on the spectral moments of A, and M = ‖A‖ (non-principal). Land the eigenvalue-moment ↔ L^q identity axiom-clean (abstract: for a real symmetric matrix with eigenvalues η_b, Σ|η_b|^{2k} = tr(A^{2k}) and max ≤ (Σ)^{1/2k}).`},
  // --- structural sufficient conditions for finite-q Λ(q) ---
  {id:'L3-Bhg', file:'_LambdaQBhgSufficient', t:`B_h[g] SUFFICIENT CONDITION. A set is B_h[g] if every element has ≤ g representations as an h-fold sum. B_h[g] ⟹ Λ(2h) with constant ≤ g^{1/2h}·(2h−1)‼^{1/2h}. Land the implication "μ_n is B_h[g] ⟹ μ_{2h} ≤ g·(2h−1)‼·n^h ⟹ prize-at-depth-h" axiom-clean (abstract: a representation-multiplicity bound on h-fold sums bounds the 2h-th moment). NAME the open residual: the max h-fold representation multiplicity of μ_n at h≈log m (= the deep-k energy = BGK). This is the cleanest structural packaging.`},
  {id:'L4-dissociativity', file:'_LambdaQDissociativity', t:`DISSOCIATIVITY / QUASI-INDEPENDENCE. A dissociated set (no nontrivial ±1 sub-sum relations) is Λ(q) with constant √q for ALL q (Rudin). μ_n is FAR from dissociated (it's a group: x·(group relations)), but measure the DISSOCIATIVITY DEFECT — the largest dissociated subset / the number of ±1 relations among k elements of μ_n. Land "dissociated ⟹ Λ(q) const √q" skeleton axiom-clean, and DERIVE (probe + analysis) how the group structure obstructs it and what defect-bounded version would suffice. Honest: this likely REDUCES (the defect = the relations = energy), name it.`},
  {id:'L5-flatness', file:'_LambdaQFlatCoefficients', t:`FLAT-COEFFICIENT / LITTLEWOOD FLATNESS. η has ALL-ONES coefficients = a flat exponential sum over μ_n. Littlewood/Rudin–Shapiro flat polynomials have ‖p‖_q ≍ ‖p‖_2 = √(deg). DERIVE whether a flatness principle bounds ‖η‖_q for the specific flat μ_n sum, or REFUTE (machine: compute ‖η‖_q/√(qn) for the flat μ_n sum vs a Rudin–Shapiro flat sum; is μ_n flatter or worse?). Land a brick or a refutation with countermodel. KEY question: does flatness of the COEFFICIENTS transfer to L^q control given the multiplicative SUPPORT?`},
  // --- local / finite-q growth theory ---
  {id:'L6-growth-law', file:'_LambdaQGrowthLaw', t:`THE Λ(q)-CONSTANT GROWTH LAW. Define C(q) = ‖η‖_q/√(qn). DERIVE (exact F_p compute at n=16..128, multi-prime) C(q) as a function of q: where does it leave O(1)? The prize ⟺ C(q) = O(1) up to q≈log m. Fit the crossover q*(n). Is q*(n) ≥ log m (prize TRUE) or < log m (prize FALSE)? Land the monotonicity/log-convexity STRUCTURE of C(q) axiom-clean (q↦log‖η‖_q is convex — Lyapunov/Hölder) and report the numeric crossover. This is the prize-true-vs-false discriminator on the Λ(q) face.`},
  {id:'L7-interpolation', file:'_LambdaQLogConvexInterp', t:`LOG-CONVEX INTERPOLATION from KNOWN low moments. ‖η‖_2=√n EXACT (Parseval), ‖η‖_4=(E_2)^{1/4}=(3n²−3n)^{1/4} EXACT. q↦log‖η‖_q is CONVEX. Land the log-convexity (Lyapunov) interpolation inequality axiom-clean and DERIVE what it gives at q≈log m: the interpolant between (2,·) and (∞,M) is a LINE, so interpolation from below is circular (needs ‖η‖_∞); the CONTENT is the SLOPE/second-difference. Make precise exactly what extra finite datum (which ‖η‖_{q0}) would pin M, and that q0≈log m = the wall. Honest REDUCED with the named residual.`},
  // --- 2-power tower / tensor structure ---
  {id:'L8-tower-tensor', file:'_LambdaQTowerTensor', t:`2-POWER TOWER / TENSOR Λ(q) RECURSION. n=2^μ: μ_2⊂μ_4⊂…⊂μ_n. Λ(q) constants TENSORIZE (C_q(E×F)≤C_q(E)C_q(F)). Is there a tower recursion η_{μ_{2n}}(b) = η_{μ_n}(b) + η_{shifted}(b) (coset-doubling) that gives a Λ(q) recursion C(2n) vs C(n)? Land the coset-doubling identity + the resulting Λ(q) sub/super-multiplicativity axiom-clean, or REFUTE that it decouples (memory: TOWER-2 decoupling REFUTED for sup-norm — does the Λ(q)/moment version also fail? machine-check the moment recursion). Connects to in-tree QuartetTowerLaw.`},
  // --- refutations: Λ(q) shortcuts that DON'T work ---
  {id:'L9-trivial-interp-refute', file:'_LambdaQTrivialInterpRefuted', t:`REFUTE the trivial-interpolation shortcut. Hausdorff–Young / trivial bounds give ‖η‖_q ≤ ‖η‖_∞^{1−2/q}‖η‖_2^{2/q} ≤ n^{1−2/q}·n^{1/q}, which at q≈log m gives M ≤ n^{1−o(1)} = BGK (vacuous for the prize). Land the EXACT vacuity: prove the trivial interpolation gives only exponent 1−o(1), machine countermodel showing it cannot reach exponent 1/2. Documents why naive Λ(q) interpolation is the wall, not a route.`},
  {id:'L10-sidon-refute', file:'_LambdaQNotSidon', t:`QUANTIFY the non-Sidon obstruction (the Pisier onset). μ_n is NOT Sidon: REFUTE Sidonicity with the exact E_2=3n²−3n excess (n²−2n over the Sidon floor 2n²−n, from the n/2 antipodal pairs σ=0). Land the exact non-Sidon defect axiom-clean and DERIVE where the Λ(q)-const ONSET of growth is (the q at which the antipodal excess first dominates Wick): is it BELOW or ABOVE log m? This bounds the prize-true window from the Sidon side.`},
  {id:'L11-restriction-refute', file:'_LambdaQRestrictionRefuted', t:`REFUTE the restriction / Stein–Tomas Λ(q) route. Restriction estimates give Λ(q) for CURVED sets; μ_n is FLAT (0-dimensional, Σ|η_b|²=p·n trivial Plancherel — memory issue444-modern-tools-nogo). Land the exact statement that the restriction/Stein–Tomas exponent is VACUOUS for μ_n (the flat 0-dim set saturates the trivial bound), with the machine countermodel. Closes the restriction angle on the Λ(q) face cleanly.`},
  // --- the DISPROOF direction (prize is for EITHER resolution) ---
  {id:'L12-disprove', file:'_LambdaQDisproofAttempt', t:`THE DISPROOF DIRECTION (resolving δ* the OTHER way also wins the prize). ATTEMPT to PROVE the Λ(q)-const of μ_n is LARGE at q≈log m ⟹ M > C√(n log m) ⟹ δ* does NOT reach the window interior. Lever: a generic size-2^30 set's RAW Λ(q) breaks at q≈10 (DC term); does μ_n's multiplicative structure create a SPECIFIC bad b (a multiplicative resonance) where many ~log p-fold sums align, exceeding Wick? Machine-search (exact F_p, n=16..64, multi-prime) for the worst-case μ_{2k}/Wick_k at deep k: does it EXCEED 1 (disproof) or stay ≤1 (prize holds, numerics say 0.77–0.85)? Report the honest verdict: is disproof feasible, or does the mean-zero structure forbid it? Land any rigorous lower-bound brick or document the obstruction.`},
  {id:'L13-finiteq-vs-sidon', file:'_LambdaQFiniteVsSidon', t:`THE FINITE-q vs SIDON GAP (the Pisier escape). The prize needs Λ(q) at ONE q≈log m, NOT all q (Sidon). Make this precise: land the implication "Λ(q0) bound at the single q0≈2 log m ⟹ prize" (the finite-q sufficiency, sharpening _LambdaQRudinEndToEnd) and the OBSERVATION that this is strictly weaker than Sidon, so Pisier's circularity does NOT apply to it. Then DERIVE whether the finite-q statement is STILL equivalent to the deep-energy wall (μ_{2k}≤Wick at k≈log m) or genuinely weaker. Honest: it is the SAME wall (even-q Λ(q)=energy), but PROVE that equivalence cleanly — that closes whether the finite-q escape is real.`},
  {id:'L14-bourgain-machinery', file:null, t:`BOURGAIN's Λ(q) MACHINERY applicability. Bourgain's results (every set contains a large Λ(q) subset; Λ(q)-uniformizability; the selector/entropy method; Λ(p)-set of maximal dimension) are largely EXISTENTIAL. DERIVE precisely (no Lean needed — analysis in 'finding') whether ANY of Bourgain's Λ(q) techniques can PRODUCE a bound for the SPECIFIC explicit set μ_n (vs merely prove a large Λ(q) subset EXISTS). State the exact obstruction (explicit-vs-existential) and whether the maximal-Λ(q)-dimension count (size ~ p^{2/q} for bounded const) is CONSISTENT with |μ_n|=2^30 at q≈log m, or shows μ_n is too LARGE to be Λ(log m) generically (⟹ structure-essential, the disproof lever).`},
]

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, sz){
  let acc=[]
  for (const [i,w] of chunk(items,sz).entries()){
    log(`Attack wave ${i+1}/${Math.ceil(items.length/sz)} (${w.map(x=>x.id).join(', ')})`)
    acc=acc.concat(((await parallel(w.map(it=>()=>mk(it))))||[]).filter(Boolean))
  }
  return acc
}
const hardIds = new Set(['L6-growth-law','L12-disprove','L13-finiteq-vs-sidon','L14-bourgain-machinery'])
const mk = (T) => agent(
  `${FRAME}

TASK ${T.id}. ${T.file?`Create ${DIR}/${T.file}.lean. `:'(analysis only — no Lean file needed.) '}${T.t}
Return the structured verdict + ${T.file?'the COMPLETE fileContent (clobber-proof)':"the full derivation in 'finding'"}.`,
  {label:`atk:${T.id}`, phase:'Attack', effort: hardIds.has(T.id)?'high':'medium', schema:{...SCHEMA}})

phase('Attack')
const attacked = await waved(ANGLES, mk, 4)

phase('Verify')
const toV = attacked.filter(r=>(r.outcome==='LANDED'||r.outcome==='REFUTED'||r.outcome==='PARTIAL'||r.outcome==='REDUCED') && r.axiomsClean!==false && r.fileContent)
const verified = await waved(toV, (r)=>agent(
  `${FRAME}

ADVERSARIALLY VERIFY ${r.outcome} for ${r.id} (${DIR}/${(r.file||'').split('/').pop()}). key=${r.keyTheorem||'?'}.
Re-run pg-iterate; confirm no sorry/native_decide, #print axioms ⊆ {propext,Classical.choice,Quot.sound}. Judge
FAITHFULNESS HARD: a REAL theorem (not tautology / vacuous-hyp / laundered closure / energy-wall dressed as a
new Λ(q) result)? For a conditional, confirm the NAMED hypothesis IS the genuine open part (deep-k multiplicative
deviation = BGK), not silently discharged. For a refutation, confirm the countermodel is a real exact F_p compute.
Re-verdict + fileContent.`,
  {label:`vfy:${r.id}`, phase:'Verify', effort:'medium', schema:{...SCHEMA}}), 3)

phase('Synthesize')
const vmap=new Map(verified.filter(Boolean).map(v=>[v.id,v]))
const fin=attacked.map(r=>vmap.get(r.id)||r)
const tally={}; for(const r of fin) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`lambdaq-assault done: ${JSON.stringify(tally)}`)
return { tally, results: fin.map(r=>({id:r.id, outcome:r.outcome, axiomsClean:r.axiomsClean, file:r.file,
  keyTheorem:r.keyTheorem, finding:(r.finding||'').slice(0,600), fileContent:r.fileContent||''})) }
