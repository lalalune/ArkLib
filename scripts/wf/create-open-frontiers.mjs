export const meta = {
  name: 'create-open-frontiers',
  description: 'RULE IN the live open frontiers of the #444 core and CREATE novel mathematics for each: effective growing-order Jacobi equidistribution, wraparound variance, Stickelberger clustering, tower variance bootstrap, Fermat-Hodge decomposition, wraparound gen-fn, correlation L-function, rep-theory energy identity, prime-family sieve, third-basis invariant',
  phases: [
    { title: 'Create', detail: 'build each novel object as far as it genuinely goes (axiom-clean scaffolding + the precise NEW theorem named)' },
    { title: 'Assess', detail: 'how far did each construction reach? genuinely new? the precise missing piece?' },
  ],
}
const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444 ($1M). MANDATE: this is a CREATION pass, not a refutation pass. RULE IN the live open
frontiers and CREATE novel mathematics for each — objects/theorems that have never existed. The single open core
(everything else formalized): the char-p energy bound E_r(μ_n;F_p) ≤ (2r−1)‼·n^r at r≈log p (n=2^30, p≈n·2^128,
n≈p^{0.19}), equivalently the WRAPAROUND VARIANCE: W_r=E_r−E_r^{char0} has its random mean n^{2r}/p exactly
DC-cancelled; the prize is that the wraparound FLUCTUATION ≤ slack_r at r≈log p (a variance/equidistribution
statement). ESTABLISHED THIS CAMPAIGN (build ON these, all axiom-clean): _JacobiMomentIdentity (the 2r-th moment
is a SIGNED unit-phase Jacobi correlation, √p removed); _JacobiFermatCohomology (the off-diag is Tr Frob on the
correlation variety V_corr, weight 2r-1); _OnsetGrowthLaw (r_0=Θ(p^{1/φ(n)}), onset below saddle ⟹ prize is
quantitative W_r≤slack); _BridgeOneWall (additive=multiplicative, one object two dual bases); probe_wraparound_correction
(wraparound is SUB-random, DC-moment ratio 0.87→0.13 below 1 and improving).
YOUR JOB per frontier: CREATE the novel object (a new invariant / theorem / L-function / decomposition that does
NOT exist in the literature), build the provable scaffolding axiom-clean in Lean, and state the PRECISE NEW
THEOREM that would close the prize via this object. Push the construction as FAR as it genuinely reaches. Bold,
ambitious creation is the goal. These frontiers are RULED IN (not yet refuted) — do not pre-emptively refute;
BUILD. But stay honest: name the precise open step, never claim closure without a real axiom-clean proof.
BUILD: scripts/pg-iterate.sh <file> (lock-free; READ #print axioms ⊆ {propext,Classical.choice,Quot.sound}, no
sorryAx). autoImplicit OFF. Repo ${REPO}. MINIMAL imports. Create the file under ${DIR}/. RETURN full fileContent.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['CLOSED','DEEP_SCAFFOLD','SCAFFOLD','PARTIAL','REDUCES','FAILED']},
    axiomsClean:{type:'boolean'}, genuinelyNew:{type:'boolean'}, howFar:{type:'string'},
    theNovelObject:{type:'string'}, theNewTheorem:{type:'string'}, theMissingPiece:{type:'string'},
    file:{type:'string'}, keyTheorem:{type:'string'}, fileContent:{type:'string'}, summary:{type:'string'} },
}

const FRONTIERS = [
  {id:'F1-jacobi-growing-order', file:'_CreateJacobiGrowingOrder', t:`CREATE an EFFECTIVE GROWING-ORDER equidistribution theorem for Jacobi sums. Katz equidistribution is FIXED-order (Sato–Tate as p→∞ at fixed r). The prize needs r≈log p GROWING. CREATE the novel framework: an effective discrepancy bound D(r,p) for the joint distribution of the n^r normalized iterated Jacobi sums j_r(χ) on the Fermat correlation variety, with EXPLICIT dependence on the order r. Build the object (the empirical/moment characterization of the growing-order discrepancy), the provable scaffolding (e.g. the 2nd-moment of the discrepancy = a lower Jacobi correlation, computable), and state the precise NEW growing-order equidistribution theorem that would give the off-diagonal cancellation. This is genuinely un-attempted (Katz did fixed-order). Push it.`},
  {id:'F2-wraparound-variance', file:'_CreateWraparoundVariance', t:`CREATE a VARIANCE / second-moment theory of the wraparound. The wraparound W_r is SUB-random (W_r < n^{2r}/p, the random mean DC-cancelled). CREATE the novel object: Var(W_r) = the second moment of the wraparound count over the prime family (or over a randomization), and a NEW second-moment identity expressing it as a higher Jacobi correlation. Build the scaffolding (the variance decomposition, the diagonal contribution) axiom-clean, and state the precise NEW variance bound (Var(W_r) ≤ mean, sub-Poisson) that would give W_r ≤ slack via Chebyshev. A genuinely-new probabilistic-NT object for the wraparound. Push it.`},
  {id:'F3-stickelberger-clustering', file:'_CreateStickelbergerClustering', t:`CREATE the STICKELBERGER CLUSTERING STRATIFICATION. Not "does Stickelberger forbid short wraps" (refuted) — the FINER object: stratify the wraparound relations by their 𝔭-adic valuation profile (the Stickelberger element θ gives the exact 𝔭-adic valuation of each Jacobi sum). CREATE the new invariant: the valuation-stratified wraparound count, and a NEW identity relating the clustering (which relations are simultaneously 𝔭-divisible) to the Stickelberger combinatorics of the 2-power group. Build the valuation-stratification object axiom-clean + the precise new theorem (the high-valuation stratum is sparse ⟹ no clustering ⟹ bounded fluctuation). Genuinely-new p-adic-combinatorial object. Push it.`},
  {id:'F4-tower-variance-bootstrap', file:'_CreateTowerVarianceBootstrap', t:`CREATE a VARIANCE BOOTSTRAP up the 2-power tower. NOT tower-decoupling (refuted, saving-preserving). CREATE a genuinely-new self-improvement: the wraparound fluctuation at level 2n related to level n via a CONTRACTIVE variance recursion (the coset-doubling acts on the fluctuation, and the antipodal structure makes consecutive levels NEGATIVELY correlated). Build the coset-doubling variance recursion object axiom-clean + the precise new theorem (a contractive recursion Var_{2n} ≤ ρ·Var_n with ρ<1 driven by antipodal anti-correlation) that bootstraps to the prize. Genuinely-new RG-variance object. Push it.`},
  {id:'F5-fermat-hodge-decomp', file:'_CreateFermatHodgeDecomp', t:`CREATE a HODGE/GALOIS DECOMPOSITION of the large Fermat cohomology as a RESOURCE. The correlation variety V_corr has Betti number ~n^r (huge cohomology). CREATE the novel object: the decomposition of H^{2r-1}(V_corr) under the large automorphism group (S_r ⋉ μ_n^r) into isotypic/Hodge pieces, and a NEW theorem that the OFF-diagonal correlation lives in a SMALL isotypic piece (the sign/alternating representation) whose dimension is sub-exponential ⟹ effective cancellation. Build the isotypic-decomposition scaffolding axiom-clean + the precise new theorem (off-diag projects to a low-dim piece, weight < 2r-1). Genuinely-new motivic-decomposition object. Push it.`},
  {id:'F6-wraparound-genfn', file:'_CreateWraparoundGenFn', t:`CREATE the WRAPAROUND GENERATING FUNCTION and its analytic structure. CREATE the novel object: G(z) = Σ_r (W_r − n^{2r}/p) z^r / r! (the DC-subtracted wraparound EGF), and analyze its analytic continuation / singularity structure / a NEW functional equation. Build the gen-fn object + the provable analytic scaffolding (the radius of convergence, the diagonal singularity) axiom-clean, and state the precise NEW theorem (a saddle/singularity bound on G that gives W_r ≤ slack at the saddle r). A genuinely-new analytic-combinatorics object for the wraparound. Push it.`},
  {id:'F7-correlation-Lfunction', file:'_CreateCorrelationLFunction', t:`CREATE the FERMAT-CORRELATION L-FUNCTION. CREATE a genuinely-new L-function L(s) whose special values / Dirichlet coefficients are the off-diagonal Jacobi correlations (the Frobenius traces on V_corr across the prime family), with a conjectural functional equation and a NEW zero-free-region / convexity-breaking statement. Build the L-function object (Euler product over the prime family, the conductor) + the provable scaffolding axiom-clean, and state the precise NEW theorem (a subconvexity / zero-free region for L that gives the off-diagonal cancellation at the prize). Genuinely-new L-function. Push it (honest: the analytic continuation is the hard part).`},
  {id:'F8-reptheory-energy', file:'_CreateRepTheoryEnergy', t:`CREATE a REPRESENTATION-THEORETIC energy identity that EXPOSES the cancellation. CREATE the novel object: realize E_r(μ_n) as the dimension/character of a NEW representation (of S_{2r}, or a Hecke/wreath-product algebra acting on μ_n^{2r}) whose DECOMPOSITION into irreducibles makes the char-0 part (the Wick/diagonal) and the wraparound (the correction) separate isotypic pieces. Build the representation + the energy=character identity axiom-clean + the precise new theorem (the wraparound lives in a small irreducible whose multiplicity is bounded ⟹ W_r ≤ slack). Genuinely-new rep-theory object (NOT Schur, which was refuted as trivial — use a wreath/Hecke structure). Push it.`},
  {id:'F9-prime-family-sieve', file:'_CreatePrimeFamilySieve', t:`CREATE a NON-TAUTOLOGICAL PRIME-FAMILY large sieve. NOT the refuted cross-prime sieve (which used the tautological bridge). The prize ALLOWS p=Θ(n^β); CREATE a genuinely-new averaging that exploits the FAMILY's arithmetic: the wraparound relations are 𝔭-divisible, and across the family {p}, a fixed relation D is 𝔭-divisible for a CONTROLLED set of p (the primes dividing N(D)). CREATE the dual object: sum over the family of the wraparound, = Σ_D (number of p in family with p|N(D)) = Σ_D (small, by divisor bounds). Build the family-dual identity axiom-clean + the precise new theorem (the family-summed wraparound is small ⟹ W_r small for a positive-density / existent good prime). Genuinely-new family-sieve (the divisor-bound input is the new part, NOT a bridge). Push it.`},
  {id:'F10-third-basis', file:'_CreateThirdBasisInvariant', t:`CREATE a genuinely-new THIRD-BASIS invariant — neither additive nor multiplicative (the Fourier-dual pair is tautological, _BridgeOneWall). Candidates: the QUANTUM/Heisenberg basis (the metaplectic representation has a continuum of bases between position and momentum — the FRACTIONAL Fourier transform at angle θ); the wraparound viewed in a basis that diagonalizes the JOINT additive-multiplicative action (the Weil representation's oscillator basis). CREATE the object: η in the fractional-Fourier / oscillator basis, where the additive-multiplicative symmetry is BROKEN, and a NEW concentration statement in that basis. Build the third-basis representation axiom-clean + the precise new theorem (concentration in the oscillator basis ⟹ the bound). Genuinely-new basis (Walsh was refuted; the oscillator/fractional-Fourier basis is different). Push it.`},
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

phase('Create')
const created = await waved(FRONTIERS, (T)=>agent(
  `${FRAME}

CREATE frontier ${T.id}. Create ${DIR}/${T.file}.lean. ${T.t}
Deliver: the novel object (theNovelObject); the precise NEW theorem that would close the prize via it
(theNewTheorem); the precise missing piece (theMissingPiece); a Lean brick with the provable scaffolding
axiom-clean. Push the construction as FAR as it genuinely reaches (DEEP_SCAFFOLD if you build substantial real
structure; CLOSED only for a genuine axiom-clean proof of the core). Return full fileContent.`,
  {label:`create:${T.id}`, phase:'Create', effort:'high', schema:{...SCHEMA}}), 5, 'Create')

phase('Assess')
const toA = created.filter(r=>r.fileContent && r.outcome!=='FAILED')
const assessed = toA.length ? await waved(toA, (r)=>agent(
  `${FRAME}

ASSESS the creation ${r.id}. Object: ${(r.theNovelObject||'').slice(0,400)}. New theorem: ${(r.theNewTheorem||'').slice(0,300)}.
File: ${DIR}/${(r.file||'').split('/').pop()}. Re-run pg-iterate, confirm axiom-clean (#print axioms ⊆ standard, no
sorryAx). Judge HONESTLY: (1) is the object GENUINELY NEW (not a rehash of a refuted approach)? (2) how FAR does
the construction genuinely reach — real new structure, or a thin shell? (3) is the named missing piece the
HONEST open core (not a vacuous/circular hyp)? (4) does it CLOSE anything axiom-clean? Rate howFar honestly
(DEEP_SCAFFOLD / SCAFFOLD / thin). This is constructive assessment — credit real new structure, flag only fake
closure or pure rehash. Return verdict + fileContent.`,
  {label:`assess:${r.id}`, phase:'Assess', effort:'medium', schema:{...SCHEMA}}), 4, 'Assess') : []

const amap=new Map(assessed.filter(Boolean).map(v=>[v.id,v]))
const fin=created.map(r=>amap.get(r.id)||r)
const closed=fin.filter(r=>r.outcome==='CLOSED'&&r.axiomsClean===true)
const deep=fin.filter(r=>r.outcome==='DEEP_SCAFFOLD'&&r.axiomsClean!==false)
const tally={}; for(const r of fin) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`create-open-frontiers done: ${JSON.stringify(tally)} | CLOSED:${closed.length} DEEP:${deep.length}`)
return { tally, closedCount: closed.length, deepCount: deep.length,
  closed: closed.map(r=>({id:r.id, file:r.file, thm:r.keyTheorem})),
  results: fin.map(r=>({id:r.id, outcome:r.outcome, genuinelyNew:r.genuinelyNew, axiomsClean:r.axiomsClean, file:r.file,
    object:(r.theNovelObject||'').slice(0,160), newThm:(r.theNewTheorem||'').slice(0,160),
    missing:(r.theMissingPiece||'').slice(0,160), howFar:(r.howFar||'').slice(0,120), fileContent:r.fileContent||''})) }
