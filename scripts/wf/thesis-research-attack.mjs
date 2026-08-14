export const meta = {
  name: 'thesis-research-attack',
  description: 'PhD thesis support: draft deep rigorous sections (6 equivalent forms, originating areas + unseen connections, tried-and-wall, empirical evidence, solution space, novel paths) AND make genuine fresh proof attempts on the most credible paths (#444)',
  phases: [
    { title: 'Sections', detail: 'parallel deep thesis-section drafts (scholarly, rigorous, drawing on established results)' },
    { title: 'Attacks',  detail: 'genuine fresh proof attempts on the most credible paths — refine toward a proof' },
  ],
}
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444 — PhD THESIS support. The prize (Ethereum Proximity Prize, $1M, ABF26 ePrint 2026/680):
prove the char-p energy bound E_r(μ_n;F_p) ≤ (2r−1)‼·n^r at r≈log p (n=2^30, p≈n·2^128, n≈p^{0.19}), equivalently
the BGK/Paley sup-norm M=max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| ≤ C√(n log m) at exponent 1/2 — a ~25-year-open analytic-NT
problem. Five names: Paley graph conjecture / BGK / explicit-RS list-decoding to capacity / Gauss additive
subgroup sum / char-p transfer of the (proven char-0) energy bound.
ESTABLISHED THIS CAMPAIGN (all axiom-clean in-tree, cite precisely; ~100 directions explored, ~28 new objects
created): the prize floor is formalized end-to-end MODULO the single energy inequality (_ProveAssemblyConcrete);
SIX EQUIVALENT FORMS (char-p energy / BGK-Paley / Λ(q)-set=Sidon by Pisier / sub-Gaussian / Jacobi-cocycle
dispersion / wraparound variance); the TWO-OBSTRUCTION PINCER (moment-necessity: must be cancellation not count,
proven moment_ladder_exceeds_prize; √p-vacuity: Weil gives √p≫n for thin μ_n); _BridgeOneWall (additive=
multiplicative, one object two dual bases); the √p-REMOVAL identity (_JacobiMomentIdentity: 2r-th moment is a
signed unit-phase Jacobi correlation); _JacobiFermatCohomology (√p re-enters at H^{2r-1}(V_corr) weight 2r-1);
the ONSET LAW r_0=Θ(p^{1/φ(n)}) (onset below saddle at prize scale ⟹ prize is quantitative W_r≤slack); GoN
CLOSED (cyclotomic lattice too round); the VARIANCE route (wraparound sub-random, random mean DC-cancelled,
DC-moment ratio 0.87→0.13 below 1 improving; CONVERGES on the 2nd-moment/PAIR equidistribution of Jacobi sums at
growing order; exact CrossCov_r=(−1)^r·Var_r, F4 bootstrap parity-split). EMPIRICAL: M/√(2n log m)=0.77-0.85<1
(prize believed TRUE); di Benedetto beat to exponent 0.9583 (saving 1/24); no disproof found; exact pins
δ*(RS[F5,4,2])=1/4 etc.
HONESTY (PARAMOUNT for a thesis): NEVER fabricate a proof of an open problem. CLOSED claims = axiom-clean Lean
(#print axioms ⊆ standard, no sorryAx) ONLY. A thesis that ADVANCES the problem + honestly delineates the open
core is the deliverable; do NOT claim the open core is closed. Sections must be scholarly, rigorous, precise,
citing the in-tree results + the literature (BGK 2006, di Benedetto arXiv:2003.06165, Kowalski 2401.04756, Pisier
1704.02969, Katz, Deligne, ABF26 2026/680, KKH26 2026/782). Repo ${REPO}. BUILD: scripts/pg-iterate.sh for any
Lean. RETURN the polished section text (or proof attempt) in 'finding' (long-form, thesis-quality prose), and
fileContent for any new Lean brick.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{ id:{type:'string'}, outcome:{type:'string', enum:['DRAFTED','PROVED','ADVANCED','REDUCES','PARTIAL','FAILED']},
    axiomsClean:{type:'boolean'}, finding:{type:'string'}, theNewResult:{type:'string'}, file:{type:'string'},
    fileContent:{type:'string'}, summary:{type:'string'} },
}

const SECTIONS = [
  {id:'S1-six-forms', t:`THESIS SECTION: "The Six Equivalent Forms." Write a rigorous, scholarly section presenting the six equivalent formulations of the prize (char-p energy E_r≤(2r−1)‼·n^r; BGK/Paley sup-norm M≤C√(n log m); Λ(q)-set bounded constant = Sidon by Pisier; sub-Gaussian antipodal phases; Jacobi-cocycle projective-character dispersion; wraparound variance W_r≤slack). For EACH: the precise statement, the parameters, and the PROOF of equivalence (cite the in-tree formalizations: _OpenCoreMonotoneReduction, _LambdaQMeanZeroEnergy, Pisier 1704.02969, _ArcsineIIDFraming, _JacobiCocycleDispersion, probe_wraparound_correction; and _BridgeOneWall showing additive=multiplicative). Make the equivalence web explicit and rigorous. Thesis-quality prose, ~1500-2500 words.`},
  {id:'S2-areas-connections', t:`THESIS SECTION: "Originating Areas and Unseen Connections." Write a scholarly section tracing the SIX areas of mathematics each form originates from (analytic NT: BGK/Burgess/di Benedetto; harmonic analysis: Rudin Λ(p) sets/Bourgain; coding theory: RS list-decoding/proximity gaps/ABF26; algebraic geometry: Gauss-Jacobi sums/Fermat varieties/Deligne Weil-II; additive combinatorics: sum-product; probability: sub-Gaussian/random multiplicative functions/Harper). Then the UNSEEN CONNECTIONS this campaign uncovered: the Jacobi-cocycle = Weil representation link; the additive-multiplicative Fourier duality (_BridgeOneWall); the onset law connecting to geometry of numbers; the wraparound variance connecting to second-moment Jacobi-pair equidistribution. Synthesize how these fields are ONE problem. ~1500-2500 words.`},
  {id:'S3-tried-wall', t:`THESIS SECTION: "What Has Been Tried and Why It Hit the Wall." Write a rigorous section presenting the TWO-OBSTRUCTION PINCER (moment-necessity + √p-vacuity) as the structural reason, then the dead-routes ledger (~100 directions: sum-product/di Benedetto vanishes at p^{0.19}; modern tools decoupling/restriction/VMVT — μ_n flat; the ~70-domain exhaustive loop; the ambitious meta-assault; geometry of numbers — cyclotomic lattice too round). For the KEY routes give the PRECISE refutation mechanism (each is a theorem). Then "what people said the next step would be" (Paley conjecture, effective Katz equidistribution, the BCHKS 1.12 char-sum cancellation). ~1800-2800 words.`},
  {id:'S4-empirical', t:`THESIS SECTION: "Empirical Evidence and Exact Pins." Write a rigorous section compiling ALL the computed evidence: M/√(2n log m)=0.77-0.85<1 (prize believed true); the di Benedetto BEAT (di Benedetto Thm 3.1 specialized to μ_n with Sidon-floor energies T_2=3n²-3n, T_3=O(n³), gives exponent 0.9583, saving 1/24 vs 31/2880 — a 3.9x improvement; machine-verified to n≤64); the onset law r_0=Θ(p^{1/φ(n)}) (measured constant 0.85-1.0); the DC-moment ratio 0.87→0.13 (below 1, improving with depth); the wraparound sub-randomness; no disproof found at n=64,128 over high-2-adic primes; the exact δ* pins (δ*(RS[F5,4,2])=1/4, δ*=1/4 on ε*∈[2/17,7/17) at F17). Present as rigorous empirical support with the precise numbers. ~1500-2200 words.`},
  {id:'S5-solution-space', t:`THESIS SECTION: "The Solution Space and What New Mathematics Would Look Like." Write a scholarly section delineating the PRECISE shape of the missing theorem: a growing-order (r≈log p) effective equidistribution / variance bound on the deep-r wraparound of μ_n, equivalently the second-moment/pair equidistribution of Jacobi sums on the Fermat correlation variety. Explain WHY no existing tool reaches it (Katz/Deligne fixed-order; the genus/Betti blowup ~n^r; the pincer). Then characterize what a GENUINE proof would require: an object that is SIGNED (escapes moment-necessity) AND subgroup-scale √n (escapes √p-vacuity) AND captures growing-order cancellation. Survey the ~28 created candidate objects and assess which is closest. ~1800-2800 words.`},
]
const ATTACKS = [
  {id:'A1-secondmoment-jacobi', t:`GENUINE FRESH PROOF ATTEMPT: the second-moment / PAIR equidistribution of Jacobi sums at growing order (the convergent core of the variance route). Try HARD to prove the sub-Poisson wraparound variance Var(W_r)≤mean, OR the off-diagonal pair cancellation Σ_{T≠T'}PairCorr≤o(#Rel), via the difference-variety reduction (V_diff=append(T,−T'), the 2nd-moment=1st-moment of Jphase over V_diff). Compute the V_diff first-moment cancellation rate exactly (probe), analyze V_diff's dimension/Frobenius weight (subgroup-scale or √p?), and push toward a genuine bound. If you reach a real axiom-clean partial result, build it. Honest: report exactly how far it reaches and the precise residual. This is the most credible open path — attack it for real.`},
  {id:'A2-novel-untried', t:`GENUINE FRESH PROOF ATTEMPT: invent a proof path NEVER tried in this campaign (not in the dead-routes ledger) and attack it for real. Build on the established structure: the prize is the variance of the wraparound fluctuation = a signed subgroup-scale quantity. Candidate genuinely-new paths: (a) a HYPERGEOMETRIC-MOTIVE / rigid-local-system realization where the Jacobi correlation is a hypergeometric sheaf with computable monodromy giving the cancellation; (b) a RELATIVE-TRACE / Kuznetsov over the Fermat family with a NEW geometric-side bound; (c) a CRYSTALLINE / p-adic-cohomology variance bound exploiting the 2-power Frobenius structure; (d) something genuinely from outside. Pick the most promising, build the object, push toward a proof, report honestly how far it reaches + the precise residual.`},
  {id:'A3-conditional-strongest', t:`Build the STRONGEST honest CONDITIONAL result for the thesis: the tightest end-to-end theorem 'X ⟹ prize' where X is the most elementary/credible named open hypothesis, fully axiom-clean. Consolidate _ProveAssemblyConcrete + the energy chain + the variance Chebyshev mechanism (_CreateWraparoundVariance.prize_via_subPoisson_variance) into ONE clean capstone theorem reducing the prize to the single sub-Poisson-variance (or pair-equidistribution) hypothesis, machine-checked. This is the thesis's central positive result (the conditional proof). Build it axiom-clean + state it precisely. Return the Lean fileContent + the prose explaining it.`},
]

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, sz, lbl){
  let acc=[]
  for (const [i,w] of chunk(items,sz).entries()){
    log(`${lbl} wave ${i+1}/${Math.ceil(items.length/sz)} (${w.map(x=>x.id).join(', ')})`)
    acc=acc.concat(((await parallel(w.map(it=>()=>mk(it))))||[]).filter(Boolean))
  }
  return acc
}
phase('Sections')
const sections = await waved(SECTIONS, (T)=>agent(`${FRAME}\n\n${T.t}\nReturn the full polished section prose in 'finding' (DRAFTED).`,
  {label:`sec:${T.id}`, phase:'Sections', effort:'high', schema:{...SCHEMA}}), 2, 'Sections')
phase('Attacks')
const attacks = await waved(ATTACKS, (T)=>agent(`${FRAME}\n\n${T.t}\nReturn the result in 'finding' (the analysis/proof) + fileContent for any Lean brick + theNewResult.`,
  {label:`atk:${T.id}`, phase:'Attacks', effort:'high', schema:{...SCHEMA}}), 2, 'Attacks')

const all=[...sections,...attacks]
const tally={}; for(const r of all) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`thesis-research-attack done: ${JSON.stringify(tally)}`)
return { tally, sections: sections.map(s=>({id:s.id, finding:s.finding||''})),
  attacks: attacks.map(a=>({id:a.id, outcome:a.outcome, axiomsClean:a.axiomsClean, finding:a.finding||'', theNewResult:a.theNewResult||'', file:a.file, fileContent:a.fileContent||''})) }
