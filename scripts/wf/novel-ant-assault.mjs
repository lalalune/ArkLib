export const meta = {
  name: 'novel-ant-assault',
  description: 'Invent genuinely-novel ANT to close the char-p energy bound (the prize core): must escape the moment-method necessity obstruction, not reduce to BGK, be machine-checkable; ruthless adversarial stress (#444)',
  phases: [
    { title: 'Invent',  detail: 'each agent invents ONE genuinely-novel ANT approach + a Lean skeleton + the precise new claim' },
    { title: 'Stress',  detail: 'ruthless adversarial: find the reduction-to-BGK / circular / vacuous step / moment-obstruction violation / countermodel' },
    { title: 'Deepen',  detail: 'survivors only: push toward an actual axiom-clean proof OR pin the precise obstruction' },
    { title: 'Verdict', detail: 'honest synthesis' },
  ],
}
const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444 (Ethereum Proximity Prize, $1M). TARGET — invent NOVEL mathematics to PROVE the single
open core (everything else is formalized axiom-clean):
  GaussianEnergyBound(μ_n; F_p) at depth r≈ln p:   rEnergy(μ_n, r) ≤ (2r−1)‼·n^r   over F_p (CHAR p),
  n = 2^30,  p ≈ n·2^128 (so n ≈ p^{1/5.27}, β≈5),  r* ≈ ln p ≈ 110.
The char-0 version is PROVEN in Lean (Frontier.CharZeroWickEnergy.gaussianEnergyBound_dyadic, requires
[CharZero F]). THE ENTIRE PRIZE = delete [CharZero F], prove it over F_p at r*. Equivalent forms:
 • wraparound excess W_r := rEnergy(F_p) − rEnergy^{char0} ≤ slack_r := Wick − rEnergy^{char0} ≈ Wick·r²/2n.
   (rEnergy^{char0} ≤ Wick proven; need the modular excess not to overflow the falling-factorial slack.)
 • equivalently M = max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| ≤ C√(n log m) (BGK/generalized-Paley near-Ramanujan, exponent 1/2).
 • the only char-p excess source: ADDITIVE WRAPAROUND — Σx_i ≡ Σy_i (mod p) that is NOT an equality of
   algebraic integers (over ℤ the only vanishing sums of 2^μ-th roots are antipodal pairs {x,−x}; mod p,
   short ±1 relations of ≤2r terms can wrap when their integer value is divisible by p).

THE HARDEST CONSTRAINT — your approach MUST clear it or it is dead on arrival:
 • **The MOMENT-METHOD NECESSITY OBSTRUCTION (in-tree, PROVEN: MomentLadderExceedsPrize.moment_ladder_exceeds_prize):**
   for ANY depth-r additive-moment count c with total mass n^r, the bare bound (q·Σc²)^{1/2r} ≥ n > target
   √(n·log(q/n)). I.e. NO single-moment / second-order / counting bound reaches the prize — the bound
   genuinely REQUIRES cross-moment cancellation. A novel approach that is "just another count / energy
   estimate / Cauchy-Schwarz / Plancherel" CANNOT work; it must capture the actual CANCELLATION (signs,
   phases, Galois, cohomology), not a magnitude count.
 • SOTA is exponent 1−o(1) (BGK, unconditional, ineffective); di Benedetto vanishes below p^{1/4} (prize is
   p^{0.19}); a 13-domain verified-citation literature sweep found 0 routes; μ_n is FLAT 0-dim (Σ|η_b|²=p·n
   trivial Plancherel) so curvature/decoupling/restriction are vacuous; V_r is 0-dim so Weil/Lang-Weil is
   vacuous (d=0 main term IS the count); the 2-power TOWER decoupling is REFUTED (saving-preserving); modern
   tools no-go; probabilistic extreme-value gives periods = exchangeable white-noise (not log-correlated).

WHAT WOULD ACTUALLY BE NEW (escape routes from the moment obstruction — invent IN these directions or a
genuinely new one): cross-moment / joint-cumulant cancellation across the prime family; a POSITIVE-dimensional
"excess variety" whose F_p-points = W_r (escaping the 0-dim Weil-vacuity); a p-adic/Iwasawa L-function whose
λ-invariant controls W_r growth in the Z_p-tower of primes; a Ruelle transfer operator on the 2-adic odometer
with spectral radius <1; a Stickelberger/Stark-unit forced cancellation; a Littlewood–Offord-type
anti-concentration of wraparound; a NEW ℓ-adic sheaf with controlled conductor giving Deligne √-cancellation; a
finite-free-probability edge cumulant; a genuinely new ANT invariant.

BUILD: scripts/pg-iterate.sh <file> (lock-free; READ #print axioms). autoImplicit OFF. Repo ${REPO}.
HONESTY (ABSOLUTELY PARAMOUNT — a fabricated proof wins NOTHING, the committee runs the same Lean checker):
NEVER claim closure unless there is a GENUINE axiom-clean Lean proof of the char-p statement with NO sorry,
NO native_decide, NO fabricated axiom, NO vacuous/circular hypothesis that smuggles in the result, NO hidden
[CharZero]/no-wraparound assumption. CLOSED = the actual char-p bound proven, audited. A skeleton with a NAMED
open step is SKELETON, not CLOSED — label it honestly. The default truth is "this reduces or has a gap"; the
burden is on the approach to overturn it. Bold invention is encouraged; dishonest closure is the one
unforgivable move. Clobber-proof: RETURN full fileContent.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['CLOSED','SKELETON','PARTIAL','REDUCES','REFUTED','OBSTRUCTION','FAILED']},
    axiomsClean:{type:'boolean'}, closesCharP:{type:'boolean'},
    idea:{type:'string'}, novelty:{type:'string'}, escapesMomentObstruction:{type:'string'},
    nonReduction:{type:'string'}, theNewClaim:{type:'string'}, theGapOrFlaw:{type:'string'},
    file:{type:'string'}, keyTheorem:{type:'string'}, axioms:{type:'string'},
    fileContent:{type:'string'}, finding:{type:'string'}, summary:{type:'string'} },
}

const APPROACHES = [
  {id:'N1-joint-cumulant', file:'_NovelJointCumulant', t:`CROSS-MOMENT JOINT-CUMULANT CANCELLATION. The necessity theorem kills single moments; the prize needs cross-moment cancellation. INVENT a joint-cumulant functional κ_r over the prize family of primes (or over the b-frequencies jointly) whose vanishing/decay at order r FORCES W_r ≤ slack. Define the cumulant object precisely (not a magnitude — a SIGNED/alternating cancellation), prove its provable algebra, state the new claim (cumulant decay ⟹ energy bound). Must genuinely escape the moment obstruction (be a cancellation, not a count).`},
  {id:'N2-excess-variety', file:'_NovelExcessVariety', t:`POSITIVE-DIMENSIONAL EXCESS VARIETY. The 0-dim V_r makes Weil vacuous. INVENT a NEW geometric model: a variety/scheme X_r whose F_p-points biject with the WRAPAROUND solutions W_r and has positive dimension d≥1, so Lang–Weil/Deligne gives |W_r| ≤ (main term) + O(p^{d−1/2}) with the √-saving beating slack_r at p≈n^{5.27}. The novelty is the geometric model of wraparound (e.g. fibering by the carry/quotient (Σx−Σy)/p). State the model, the dimension claim, the resulting bound; escape the d=0 vacuity HONESTLY.`},
  {id:'N3-padic-iwasawa', file:'_NovelPadicIwasawa', t:`p-ADIC / IWASAWA L-FUNCTION FOR W_r. Model W_r(p) as a p-adic L-value / measure across the Z_p-tower of prize primes p ≡ 1 (mod 2^μ). INVENT the L-function whose special values are the excess; bound its Iwasawa λ-invariant (growth rate) to force W_r ≤ slack for cofinally many p in the family (a valid prize prime suffices). State the L-function, the λ-bound claim, the interpolation. Genuinely p-adic-analytic, not a count.`},
  {id:'N4-transfer-operator', file:'_NovelTransferOperator2', t:`RUELLE TRANSFER OPERATOR ON THE 2-ADIC ODOMETER. The 2-power tower μ_2⊂…⊂μ_n carries the doubling/odometer map. INVENT a transfer (Ruelle) operator L on functions over the tower whose iterates generate the energy E_r, with spectral radius ρ(L) controlling the growth; show ρ(L)·(normalization) < the Wick growth (2r+1)n, forcing W_r ≤ slack. The cancellation comes from the operator's NEGATIVE eigenvalues (antipodal action). State L, its spectrum claim, the consequence.`},
  {id:'N5-stickelberger-stark', file:'_NovelStickelbergerStark', t:`STICKELBERGER / STARK-UNIT FORCED CANCELLATION. The Gauss sums g(χ) for 2-power χ have explicit Galois/Stickelberger factorization. INVENT a Stark-type unit identity in the cyclotomic tower forcing Σ_χ χ̄(b)g(χ) to cancel below √(n log m) — a GENUINE algebraic cancellation from the Galois module structure (not |g(χ)|=√p magnitude). State the unit identity, the cancellation it forces, the resulting bound. Must escape the "valuation is ℓ-adic, |g|=√p archimedean — orthogonal" no-go by coupling them.`},
  {id:'N6-anti-concentration', file:'_NovelAntiConcentration', t:`LITTLEWOOD–OFFORD ANTI-CONCENTRATION OF WRAPAROUND. INVENT a new anti-concentration inequality: the wraparound solutions (short ±1 relations of 2^μ-th roots that vanish mod p) ANTI-concentrate — no residue/relation-class holds too many — bounding W_r. Novel: a Littlewood–Offord / Erdős small-ball bound for SUMS OVER A MULTIPLICATIVE SUBGROUP (not iid). The cancellation is the spreading. State the small-ball claim and the W_r bound; escape the moment obstruction (anti-concentration is not a 2nd-moment count).`},
  {id:'N7-new-sheaf', file:'_NovelEllAdicSheaf', t:`NEW ℓ-ADIC SHEAF WITH CONTROLLED CONDUCTOR. The MonodromyConductorScaffold was flagged but not built. INVENT the specific ℓ-adic sheaf F on A^1/F_p whose trace function at b is the period η_b, compute/bound its conductor and the dimension of its cohomology, and apply Deligne's Weil-II to get |η_b| ≤ (conductor)·√p-type bound that at the subgroup scale gives √(n log m). The novelty is the explicit sheaf for the SUBGROUP sum (not a generic exponential sum). State the sheaf, the conductor bound, the Deligne consequence; address why it is NOT the vacuous 0-dim case.`},
  {id:'N8-finite-free', file:'_NovelFiniteFreeEdge', t:`FINITE-FREE-PROBABILITY EDGE CUMULANT. The periods η_b are the n eigenvalues of Cay(F_p,μ_n) = roots of a degree-? characteristic polynomial. INVENT a finite-free-probability argument: the finite-free cumulants of this polynomial (under the doubling/coset convolution) control the EDGE = M, with a finite-N correction that gives M ≤ √(2n log m) sharper than the moment method. Novel: finite-free cumulants of the GENERALIZED PALEY characteristic polynomial. State the cumulant recursion, the edge bound; escape moments (cumulants linearize convolution — genuinely different).`},
  {id:'N9-cross-prime-sieve', file:'_NovelCrossPrimeSieve', t:`CROSS-PRIME LARGE-SIEVE RESONANCE. The prize ALLOWS choosing p in the family p=Θ(n^β). INVENT a large-sieve / duality identity across the family: Σ_{p in family} (excess at p) is small, forcing W_r ≤ slack for a POSITIVE-DENSITY (hence existent) set of valid prize primes. Novel: a large-sieve for subgroup-sum excess ACROSS primes (not across frequencies). State the sieve identity, the density bound, why one good prime suffices for the prize. Confirm the prize permits prime choice (or honestly note it).`},
  {id:'N10-new-invariant', file:'_NovelShawInvariant', t:`INVENT A GENUINELY NEW ANT INVARIANT (the "Shaw invariant") that exactly controls W_r and is provably boundable for 2-power subgroups. It must be (a) genuinely new (not energy/Λ(q)/cumulant in disguise), (b) computable, (c) such that bounding it ⟹ the prize, (d) actually boundable by a NEW argument you give. Define it precisely, prove its key properties axiom-clean, give the bounding argument. If it reduces, say so; if it genuinely closes, prove it.`},
  {id:'N11-nilsequence', file:'_NovelNilsequence', t:`HIGHER-ORDER FOURIER / NILSEQUENCE INVERSE THEOREM. INVENT a new inverse theorem: if W_r is large then the period correlates with a degree-(s) nilsequence of bounded complexity tied to the 2-power structure; then SHOW the 2^μ-subgroup admits NO such correlation (its only structure is antipodal, degree-1), forcing W_r ≤ slack. Novel: a nilsequence inverse theorem specialized to multiplicative 2-power subgroups. State the inverse theorem and the no-correlation lemma; escape the moment obstruction via the higher-order structure.`},
  {id:'N12-wildcard', file:'_NovelWildcard', t:`WILDCARD — invent something from a field NOBODY has connected to this: e.g. tropical/log-geometry of the excess; a quantum-group/Hecke-algebra trace identity; a model-theoretic/o-minimal counting bound; an ergodic/equidistribution-with-rate via a NEW effective Ratner-type input; a coding-theoretic LP/Delsarte bound on the period spectrum. Pick the most promising genuinely-new connection, build the object, state the new claim, and either close or pin the obstruction. Maximum creativity; must still escape the moment obstruction and be machine-checkable.`},
]

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, sz, lbl){
  let acc=[]
  for (const [i,w] of chunk(items,sz).entries()){
    log(`${lbl} wave ${i+1}/${Math.ceil(items.length/sz)} (${w.map(x=>x.id||x).join(', ')})`)
    acc=acc.concat(((await parallel(w.map(it=>()=>mk(it))))||[]).filter(Boolean))
  }
  return acc
}

phase('Invent')
const invented = await waved(APPROACHES, (T)=>agent(
  `${FRAME}

INVENT approach ${T.id}. Create ${DIR}/${T.file.replace(/\s/g,'')}.lean. ${T.t}
Deliver: the precise NOVEL idea; why it is genuinely new; HOW it escapes the moment-method necessity
obstruction (this is mandatory — explain the cancellation mechanism, not a count); why it does not reduce to
BGK; the precise NEW claim (as a named Prop) that would close the char-p bound; a Lean skeleton proving the
PROVABLE scaffolding axiom-clean and stating the new claim. If you can actually CLOSE the char-p bound
axiom-clean, do it and mark closesCharP=true (it will be adversarially stress-tested). Return full fileContent.`,
  {label:`inv:${T.id}`, phase:'Invent', effort:'high', schema:{...SCHEMA}}), 4, 'Invent')

phase('Stress')
const toStress = invented.filter(r=>r.outcome!=='FAILED' && (r.fileContent||r.theNewClaim))
const stressed = await waved(toStress, (r)=>agent(
  `${FRAME}

RUTHLESSLY STRESS-TEST ${r.id} (claimed outcome ${r.outcome}, closesCharP=${r.closesCharP}).
Idea: ${(r.idea||'').slice(0,500)}
New claim: ${(r.theNewClaim||'').slice(0,400)}
Escape-mechanism claimed: ${(r.escapesMomentObstruction||'').slice(0,400)}
File: ${DIR}/${(r.file||'').split('/').pop()}
Your job is to BREAK it. In order: (1) does it REDUCE to BGK / the energy bound / a moment count (does the
"new claim" secretly equal the prize)? (2) is there a CIRCULAR or VACUOUS step — a hypothesis that smuggles in
no-wraparound / [CharZero] / the bound itself? (3) does it VIOLATE the moment-method necessity obstruction (is
the "cancellation" actually just a magnitude count in disguise)? (4) if it has a Lean file claiming closesCharP,
re-run pg-iterate, audit #print axioms (sorryAx? native_decide? fabricated axiom? vacuous hypothesis?). (5)
construct a COUNTERMODEL if the new claim is false. Default verdict REDUCES or has a GAP — only return SURVIVES
if you genuinely cannot break it after real effort, and say precisely why. Be the adversary. Return the verdict
+ theGapOrFlaw + (corrected) fileContent.`,
  {label:`str:${r.id}`, phase:'Stress', effort:'high', schema:{...SCHEMA}}), 3, 'Stress')

phase('Deepen')
const survivors = stressed.filter(r=>r.outcome==='CLOSED'||r.outcome==='PARTIAL'||r.outcome==='SKELETON')
  .filter(r=>r.theGapOrFlaw===undefined || !/reduc|circular|vacuous|moment|countermodel|false/i.test(r.theGapOrFlaw||''))
const deepened = survivors.length ? await waved(survivors, (r)=>agent(
  `${FRAME}

DEEPEN survivor ${r.id} — it survived the first stress pass. Idea: ${(r.idea||'').slice(0,500)}. New claim:
${(r.theNewClaim||'').slice(0,400)}. Either (A) PUSH it to an actual axiom-clean proof of the char-p bound
(build the Lean, prove the new claim, audit #print axioms — closesCharP=true ONLY if genuinely proven), or (B)
if it cannot be closed, pin the PRECISE remaining obstruction as a named Prop and state exactly what new
mathematics it needs. Be honest: most "survivors" still hide a gap at the deep step. Return outcome +
fileContent + the precise obstruction-or-proof.`,
  {label:`dpn:${r.id}`, phase:'Deepen', effort:'high', schema:{...SCHEMA}}), 2, 'Deepen') : []

const vmap=new Map(deepened.filter(Boolean).map(v=>[v.id,v]))
const smap=new Map(stressed.filter(Boolean).map(v=>[v.id,v]))
const fin=invented.map(r=>vmap.get(r.id)||smap.get(r.id)||r)
const closed=fin.filter(r=>r.outcome==='CLOSED'&&r.closesCharP===true&&r.axiomsClean===true)
const tally={}; for(const r of fin) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`novel-ant-assault done: ${JSON.stringify(tally)} | CLOSED-and-clean: ${closed.length}`)
return { tally, closedCount: closed.length,
  closed: closed.map(r=>({id:r.id, file:r.file, key:r.keyTheorem, axioms:r.axioms})),
  results: fin.map(r=>({id:r.id, outcome:r.outcome, closesCharP:r.closesCharP, axiomsClean:r.axiomsClean,
    file:r.file, idea:(r.idea||'').slice(0,200), theNewClaim:(r.theNewClaim||'').slice(0,200),
    theGapOrFlaw:(r.theGapOrFlaw||'').slice(0,300), fileContent:r.fileContent||''})) }
