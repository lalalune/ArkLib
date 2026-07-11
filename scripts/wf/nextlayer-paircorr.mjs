export const meta = {
  name: 'nextlayer-paircorr',
  description: 'Build the NEXT layer off the variance-core convergence: the off-diagonal pair correlation = covariance of two wraparound relations being simultaneously 𝔭-divisible = relation-norm factorization clustering; reduce 2nd→1st moment via the difference variety; make it computable / connect to Katz first-order (#444)',
  phases: [
    { title: 'Build',  detail: '3 next-layer constructions on the convergent 2nd-moment Jacobi-pair core' },
    { title: 'Assess', detail: 'how far + the precise residual' },
  ],
}
const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444 ($1M). The CREATION pass produced 10 novel objects; the 4 variance-core frontiers
(F1 _CreateJacobiGrowingOrder, F2 _CreateWraparoundVariance, F3 _CreateStickelbergerClustering, F4
_CreateTowerVarianceBootstrap, all axiom-clean) CONVERGE on one new open core: the SECOND-MOMENT / PAIR
equidistribution of Jacobi sums at growing order r≈log p. KEY ALGEBRA (from _JacobiMomentIdentity): the pair
correlation PairCorr(T,T') of two wraparound relations T,T' is the COVARIANCE over the prime family of the events
"𝔭 | N(T)" and "𝔭 | N(T')" — i.e. it measures whether the relation norms N(T), N(T') share the prime 𝔭. So
OffDiagonalPairCancellation (Σ_{T≠T'} PairCorr ≤ o(#Rel)) ⟺ the wraparound-relation NORMS do NOT cluster by
shared prime factors more than random (sub-Poisson). This is a CONCRETE, COMPUTABLE arithmetic statement about
the factorization statistics of N(T) for non-antipodal support-≤2r relations of 2^μ-th roots of unity. ESTABLISHED
(build ON, axiom-clean): _CreateWraparoundVariance (prize_via_subPoisson_variance, the Chebyshev mechanism is
DONE — only OffDiagonalPairCancellation is open); _JacobiMomentIdentity (PairCorr=Jphase product). Believed true
(wraparound SUB-random; DC-moment ratio 0.87→0.13 below 1, improving).
BUILD: scripts/pg-iterate.sh <file> (lock-free; READ #print axioms ⊆ standard, no sorryAx). autoImplicit OFF.
Repo ${REPO}. MINIMAL imports. CREATION/BUILD mode: push the construction as far as it genuinely reaches; name the
precise residual; never fabricate closure. RETURN full fileContent. Also write probes to scripts/probes/ where a
computation is decisive.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['CLOSED','DEEP_SCAFFOLD','SCAFFOLD','PARTIAL','REDUCES','FAILED']},
    axiomsClean:{type:'boolean'}, genuinelyNew:{type:'boolean'}, howFar:{type:'string'},
    theNovelObject:{type:'string'}, theNewTheorem:{type:'string'}, theMissingPiece:{type:'string'},
    file:{type:'string'}, keyTheorem:{type:'string'}, fileContent:{type:'string'}, summary:{type:'string'} },
}

const ANGLES = [
  {id:'L1-norm-factorization', file:'_NextNormFactorizationClustering', t:`CREATE + COMPUTE the relation-norm FACTORIZATION CLUSTERING. The pair correlation = covariance of "𝔭|N(T)" and "𝔭|N(T')" over the prime family = governed by gcd(N(T),N(T')) sharing 𝔭. CREATE the object: the factorization-clustering statistic C_r = (#pairs T≠T' with a common large prime factor)/(#pairs), and write a PROBE (scripts/probes/) computing the exact norms N(T) of non-antipodal support-≤2r relations of n-th roots (small n=4,8) and their shared-prime-factor statistics. Is C_r sub-Poisson (the relations' norms factor independently ⟹ no clustering ⟹ OffDiagonalPairCancellation holds)? Build the clustering object axiom-clean + the precise theorem (sub-Poisson factorization ⟹ prize) + the empirical verdict from the probe. This makes the converged open core CONCRETE and TESTABLE.`},
  {id:'L2-difference-variety', file:'_NextDifferenceVariety', t:`CREATE the 2nd→1st MOMENT DIFFERENCE-VARIETY reduction. By cocycle algebra (PairCorr(T,T')=Jphase(T)conj(Jphase(T')) = a single Jphase of the COMBINED/difference 2r-tuple), the SECOND moment of the off-diagonal over relation-pairs = a FIRST moment over the DIFFERENCE variety V_diff = {(T,T') : same locus}. CREATE V_diff, its dimension, and the reduction: Σ_{T,T'} PairCorr = Tr(Frob | H(V_diff)) — a single (higher-order) Jacobi correlation to which Katz FIRST-order equidistribution applies. Build the difference-variety reduction axiom-clean + the precise theorem (Katz first-order on V_diff gives the off-diagonal cancellation). Honest: does V_diff's dimension/weight give subgroup-scale or re-enter √p? This is the genuine second-moment-method step — name where it lands.`},
  {id:'L3-antipodal-anticorr', file:'_NextAntipodalAntiCorr', t:`CREATE + PROVE the ANTIPODAL ANTI-CORRELATION that drives F4's contraction. The 2-power antipodal structure (x,−x) makes consecutive tower levels NEGATIVELY correlated. CREATE the object: the exact sign of the covariance between the wraparound at level n and level 2n, via the coset-doubling η_b(μ_{2n})=η_b(μ_n)+η_{b'}(μ_n) and the antipodal involution. PROVE (axiom-clean, exact for small r) that the cross-level covariance is NEGATIVE (anti-correlation), giving F4's contraction factor ρ<1. Build the exact anti-correlation computation + the contraction it yields. Honest: is the anti-correlation UNIFORM in r (closes F4) or only at small r? Name precisely. This is the genuine driver of the variance bootstrap.`},
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
phase('Build')
const built = await waved(ANGLES, (T)=>agent(
  `${FRAME}

BUILD ${T.id}. Create ${DIR}/${T.file}.lean. ${T.t}
Return the novel object + the new theorem + the missing piece + howFar + full fileContent.`,
  {label:`build:${T.id}`, phase:'Build', effort:'high', schema:{...SCHEMA}}), 3, 'Build')

phase('Assess')
const toA = built.filter(r=>r.fileContent && r.outcome!=='FAILED')
const assessed = toA.length ? await waved(toA, (r)=>agent(
  `${FRAME}

ASSESS ${r.id}. Object: ${(r.theNovelObject||'').slice(0,400)}. New thm: ${(r.theNewTheorem||'').slice(0,250)}.
File ${DIR}/${(r.file||'').split('/').pop()}. Re-run pg-iterate, confirm axiom-clean. Judge HONESTLY: genuinely
new? how far does it reach? is the residual the honest open core (not vacuous/circular)? Does it CLOSE anything?
For L1 report the PROBE verdict (is factorization clustering sub-Poisson?). Credit real structure; flag fake
closure. Return verdict + fileContent.`,
  {label:`assess:${r.id}`, phase:'Assess', effort:'medium', schema:{...SCHEMA}}), 3, 'Assess') : []

const amap=new Map(assessed.filter(Boolean).map(v=>[v.id,v]))
const fin=built.map(r=>amap.get(r.id)||r)
const closed=fin.filter(r=>r.outcome==='CLOSED'&&r.axiomsClean===true)
const tally={}; for(const r of fin) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`nextlayer-paircorr done: ${JSON.stringify(tally)} | CLOSED:${closed.length}`)
return { tally, closedCount: closed.length,
  results: fin.map(r=>({id:r.id, outcome:r.outcome, genuinelyNew:r.genuinelyNew, axiomsClean:r.axiomsClean, file:r.file,
    object:(r.theNovelObject||'').slice(0,180), missing:(r.theMissingPiece||'').slice(0,180), howFar:(r.howFar||'').slice(0,140),
    fileContent:r.fileContent||''})) }
