export const meta = {
  name: 'invent-refute-loop',
  description: 'One batch of the exhaustive invent→refute loop: invent N genuinely-novel approaches to the char-p energy bound from fresh math domains, adversarially refute each, surface any SURVIVOR (#444)',
  phases: [
    { title: 'Invent', detail: 'one novel approach per fresh domain + Lean skeleton + precise claim' },
    { title: 'Refute', detail: 'ruthless classification: REDUCES / NOT_NOVEL / REFUTED / SURVIVES' },
  ],
}
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'
const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
// BATCH is hardcoded and bumped per launch (the Workflow `args` global does not reliably propagate).
const BATCH = 6
const PER = 8

const FRAME = `ArkLib #444 ($1M). TARGET: PROVE the char-p energy bound rEnergy(μ_n,r) ≤ (2r−1)‼·n^r over F_p at
r≈ln p, n=2^30, p≈n·2^128 (n≈p^{0.19}, β≈5.27). Equivalently M=max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| ≤ √(2n log m).
TWO OBSTRUCTIONS any approach MUST clear (else it REDUCES): (i) MOMENT-NECESSITY (in-tree
MomentLadderExceedsPrize): no single-moment/2nd-order COUNT reaches the target — must capture CANCELLATION
(signs/phases). (ii) √p-VACUITY: μ_n is thin so Weil/Deligne gives O(√p)=O(n^{2.6})≫n — field-scale algebraic
geometry is vacuous; must bound at SUBGROUP scale (√n·polylog). PLUS: the additive↔multiplicative bridge is
TAUTOLOGICAL (proven, _BridgeOneWall: E_r and M bracket within q−1; same object two dual bases) — a survivor
must use genuinely JOINT/new structure, not re-express one face. The only joint lever (sum-product) VANISHES at
p^{0.19} (needs |H|>p^{1/4}, 724× too thin). Explicit Gauss phases floor at n/4 DOF (Katz ceiling).
ALREADY TRIED — all REDUCED/REFUTED, do NOT repeat (auto NOT_NOVEL): joint-cumulant, excess-variety,
p-adic-Iwasawa, transfer-operator/Ruelle, Stickelberger-Stark, anti-concentration/LO, ℓ-adic-sheaf/conductor/Swan,
finite-free-edge, cross-prime-sieve, Shaw-invariant, nilsequence/GTZ, Lorentzian/Hodge/log-concavity, subconvexity,
relative-trace, o-minimal/Pila-Wilkie, mixed-energy, Bourgain-Gamburd, explicit-Gauss-phase/HD/Gross-Koblitz,
sum-product census, Halász, flag-SDP, Shearer, Berkovich, Drinfeld, restriction/decoupling/VMVT, Λ(q)/Rudin,
dissociativity, B_h[g], expander-mixing, eigenvalue-interlacing, NA-moment, good-prime-density, Delsarte-LP-basic,
prismatic-basic, finite-free-prob, hypercontractivity.
BUILD: scripts/pg-iterate.sh <file> (lock-free; READ #print axioms). autoImplicit OFF. Repo ${REPO}. MINIMAL imports.
HONESTY (ABSOLUTELY PARAMOUNT): a fabricated proof wins NOTHING. SURVIVES requires ALL of: provably NOVEL (new to
this campaign AND not standard literature), escapes BOTH obstructions with a concrete mechanism, would genuinely
close the char-p bound, AND a machine-checkable axiom-clean skeleton. Default verdict = REDUCES. The burden is on
the approach. NEVER mark SURVIVES to be encouraging — only if you genuinely cannot refute it after real adversarial
effort. Clobber-proof: RETURN full fileContent.`

// ~48 fresh mathematical domains; batch i uses a rotating window of PER of them.
const POOL = [
  'condensed/pyknotic mathematics (Clausen–Scholze): the char-p energy as a condensed-abelian-group invariant / solid tensor structure',
  'prismatic cohomology / q-de Rham: a prism over Z_p whose q-deformation interpolates char-0↔char-p energy and bounds the wraparound',
  'topological cyclic homology / TC and the cyclotomic trace applied to the 2-power subgroup energy',
  'motivic / A^1-homotopy: the energy as a motivic class; a motivic measure / realization with √n-scale weight',
  'free entropy dimension (Voiculescu) of the Gauss-phase operators in a tracial von Neumann algebra',
  'subfactors / planar algebras: the periods as a planar-algebra trace; a Jones-index spectral-gap bound',
  'quantum groups / Hecke at roots of unity: a U_q(sl_2) R-matrix identity forcing Gauss-phase cancellation',
  'modular tensor categories / TQFT: the energy as a Reshetikhin–Turaev invariant with a Verlinde-formula bound',
  'vertex operator algebras / conformal blocks: the period sum as a character of a lattice VOA with modular bound',
  'Bethe ansatz / Yang–Baxter integrability: the energy ladder as a transfer-matrix spectrum with an exact gap',
  'random matrix loop equations / Tracy–Widom: the edge of Cay(F_p,μ_n) via a Riemann–Hilbert/loop-equation analysis',
  'determinantal point process: the Gauss-phase spectrum as a DPP with a correlation-kernel sup bound',
  'matroid / Lorentzian-polynomial DEEP (beyond N12): a NEW matroid whose basis-generating polynomial is the energy gen-fn',
  'effective equidistribution via property (τ) / Lindenstrauss–Margulis spectral gap with explicit rate at growing n',
  'unipotent dynamics / effective Ratner: an effective-rate equidistribution of the dilated-phase orbit',
  'heat-kernel / spectral-zeta determinant of the Cayley graph Laplacian with a small-time asymptotic bound',
  'semiclassical / quantum-ergodicity: the periods as eigenfunction sup-norms with a QUE-type bound at the subgroup scale',
  'property (T) / Kazhdan constant of the relevant action forcing a spectral gap = the sup bound',
  'Delsarte LP / SDP hierarchy DEEP: a degree-r LP/SOS certificate for the energy bound (Positivstellensatz)',
  'proof-complexity Nullstellensatz / polynomial-calculus degree lower/upper bound for the energy system',
  'slice rank / Croot–Lev–Pach polynomial method on the wraparound tensor',
  'incidence geometry / polynomial partitioning (Guth–Katz) for the additive relations of μ_n',
  'geometric complexity theory: the energy as an orbit-closure invariant / a Kronecker-coefficient bound',
  'theta correspondence / Weil representation: η_b as a theta lift with a Rallis-inner-product bound',
  'trace formula (Arthur–Selberg) DEEP: a NEW geometric-vs-spectral identity isolating the sup',
  'arithmetic statistics / Cohen–Lenstra heuristic made effective for the wraparound divisibility',
  'heights / equidistribution of small points (Bilu) of the Gauss-sum algebraic numbers',
  'linear forms in logarithms (Baker) bounding the wraparound integer away from 0 mod p effectively at deep r',
  'Schmidt subspace theorem / Diophantine approximation of the relation lattice',
  'Ruelle transfer-operator resonances DEEP (beyond N4): a thermodynamic-formalism pressure bound on the energy growth',
  'persistent homology / topological data analysis of the phase point cloud with a stability bound',
  'optimal transport / displacement convexity: a Wasserstein-gradient-flow bound on the energy ladder',
  'quantum walk / amplitude-amplification spectral bound on Cay(F_p,μ_n)',
  'online-learning / regret minimax bound recast as the worst-case sup over b',
  'tensor network / MPS bond-dimension bound on the period as a contracted network',
  'noncommutative geometry / spectral triple Dirac-operator bound on the subgroup',
  'p-adic Hodge / (φ,Γ)-modules: a Sen-weight / Hodge–Tate bound on the wraparound',
  'crystalline cohomology / F-isocrystal Newton-above-Hodge bound on the energy variety',
  'Drinfeld modular / function-field analogy: prove the function-field analogue, transfer via a NEW bridge',
  'random walk on the affine group mod p / Bourgain–Gamburd DEEP with the explicit 2-power generator spectrum',
  'large deviations / Gärtner–Ellis with a NON-convex rate function capturing the multiplicative structure',
  'free convolution / rectangular R-transform of the coset-doubling with a finite-N edge correction',
  'sphere-packing / Cohn–Elkies linear programming dual for the period spectrum',
  'cluster algebra / dilogarithm identity forcing a Gauss-phase relation beyond Hasse–Davenport',
  'Kontsevich–Zagier period / motivic Galois constraint on the Gauss-sum periods',
  'tropical / non-archimedean Monge–Ampère measure of the energy generating function',
  'continuous model theory / metric stability of the phase structure with a tame-counting bound',
  'higher Fourier / Host–Kra nilfactor DEEP with an EFFECTIVE inverse at the 2-power structure',
]

function pick(batch, per) {
  const out = []
  for (let k = 0; k < per; k++) out.push(POOL[((batch - 1) * per + k) % POOL.length])
  return out
}
const DOMAINS = pick(BATCH, PER)

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{
    id:{type:'string'}, domain:{type:'string'},
    outcome:{type:'string', enum:['SURVIVES','REDUCES','NOT_NOVEL','REFUTED','PARTIAL','FAILED']},
    novel:{type:'boolean'}, escapesBoth:{type:'boolean'}, axiomsClean:{type:'boolean'},
    idea:{type:'string'}, theNewClaim:{type:'string'}, theGapOrFlaw:{type:'string'},
    file:{type:'string'}, fileContent:{type:'string'}, summary:{type:'string'} },
}

phase('Invent')
const invented = (await parallel(DOMAINS.map((dom, k) => () => agent(
  `${FRAME}

INVENT (batch ${BATCH}, slot ${k+1}) a genuinely-novel approach to the char-p energy bound FROM THIS DOMAIN:
  «${dom}»
Create ${DIR}/_Loop${BATCH}_${k+1}.lean. Deliver: the precise idea; why it is NOVEL (new to the campaign + not
standard lit); HOW it escapes BOTH obstructions (moment-necessity AND √p-vacuity) with a concrete cancellation
mechanism; the precise NEW claim (named Prop); a Lean skeleton proving the provable scaffolding axiom-clean +
stating the claim. Bold invention encouraged; if it obviously reduces, say so honestly (mark REDUCES). Return
full fileContent.`,
  {label:`inv:${BATCH}.${k+1}`, phase:'Invent', effort:'high', schema:{...SCHEMA}}
))) || []).filter(Boolean)

phase('Refute')
const refuted = (await parallel(invented.map((r, k) => () => agent(
  `${FRAME}

RUTHLESSLY REFUTE (batch ${BATCH}, slot ${k+1}) this invented approach from domain «${r.domain||'?'}».
Idea: ${(r.idea||'').slice(0,600)}
New claim: ${(r.theNewClaim||'').slice(0,400)}
File: ${DIR}/${(r.file||'').split('/').pop()}
Classify HONESTLY: (1) NOT_NOVEL if it's in the campaign's tried-list or standard literature. (2) REDUCES if it
collapses to BGK / hits moment-necessity (just a count) / hits √p-vacuity (field-scale) / re-expresses one face
(tautological bridge). (3) REFUTED if the claim is false (give a countermodel; re-run pg-iterate, audit axioms).
(4) SURVIVES only if you genuinely CANNOT do (1)-(3) after real effort — it is novel, escapes BOTH obstructions
with a concrete mechanism, would close the bound, and has an axiom-clean skeleton. Default = REDUCES. Be the
adversary. Return the verdict + theGapOrFlaw + (corrected) fileContent.`,
  {label:`ref:${BATCH}.${k+1}`, phase:'Refute', effort:'high', schema:{...SCHEMA}}
))) || []).filter(Boolean)

const vmap = new Map(refuted.map(v => [v.id, v]))
const fin = invented.map(r => vmap.get(r.id) || r)
const survivors = fin.filter(r => r.outcome === 'SURVIVES')
const tally = {}; for (const r of fin) tally[r.outcome] = (tally[r.outcome] || 0) + 1
log(`batch ${BATCH}: ${JSON.stringify(tally)} | SURVIVORS: ${survivors.length}`)
return {
  batch: BATCH,
  domains: DOMAINS,
  tally,
  survivorCount: survivors.length,
  survivors: survivors.map(r => ({id:r.id, domain:r.domain, claim:r.theNewClaim, file:r.file, fileContent:r.fileContent})),
  verdicts: fin.map(r => ({id:r.id, domain:(r.domain||'').slice(0,80), outcome:r.outcome,
    flaw:(r.theGapOrFlaw||'').slice(0,200), idea:(r.idea||'').slice(0,120)})),
}
