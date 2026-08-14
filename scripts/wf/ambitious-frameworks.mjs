export const meta = {
  name: 'ambitious-frameworks',
  description: 'Attack δ* via genuinely NEW frameworks (different reductions + the analytic core), beyond the exhausted energy route (#444)',
  phases: [
    { title: 'Explore', detail: 'each agent develops one ambitious new framework, honest verdict' },
    { title: 'Verify', detail: 'adversarial check of any claimed new reduction / partial result' },
    { title: 'Synthesize', detail: 'the ambitious-frameworks ledger' },
  ],
}
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444. The prize: pin δ* for explicit dyadic RS codes; it reduces (PROVEN, formalized
chain) to ONE open input — bound the char-p wraparound W_r = #{(x,y)∈μ_{2^μ}^{2r}: p|(Σx−Σy)≠0} at the
prize prime p~n·2^128=2^38·n^4 (n=2^30), equivalently E_r(F_p)≤(2r−1)‼·n^r to depth r≈log p. Repo ${REPO}.

EXHAUSTED (do NOT rehash): the energy/sup-norm route, moment methods, the 2-power symmetry structures
(Clifford REFUTED — Galois moves the prime 𝔭; gen func Σ E_r t^r=(1/p)Σ_b 1/(1−η_b²t) is RATIONAL, poles=
periods=the wall), conjecture sweeps (everything reduces via the generic rank-n/2 obstruction). The
wraparound is a FIXED-PRIME object whose only fixed-𝔭 invariants are the periods. char-0 monotonicity is
PROVEN; the residue is the fixed-prime arithmetic (effective Linnik / S-unit).

YOUR JOB: attack via a GENUINELY DIFFERENT framework (not the energy route). Be ambitious and creative.
For your assigned framework: develop it concretely, state precisely what it would establish, and give an
HONEST verdict — NEW-REDUCTION (a different equivalent formulation, real progress), PARTIAL (a provable
partial result), REDUCES (back to the wall, with the trace), or DOESN'T-APPLY. Machine-test where you can
(scripts/probes/, exact F_p). NO fabricated closure — a clean reduction or honest reduces-verdict is the
goal; never claim the prize closed.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['NEW-REDUCTION','PARTIAL','REDUCES','DOESNT-APPLY','REFUTED']},
    finding:{type:'string'}, mechanism:{type:'string'}, nextStep:{type:'string'},
    fileContent:{type:'string'}, summary:{type:'string'},
  },
}

const ANGLES = [
  {id:'LP-Delsarte', t:`The LINEAR-PROGRAMMING / Delsarte bound for the EXPLICIT list size. The MCA list size at radius δ is the number of codewords in a ball; the Delsarte LP bound (with the cyclotomic/dyadic association scheme of μ_n) might pin the list size — hence δ* — DIRECTLY, without the sup-norm. The dyadic RS code has a cyclic/BCH structure with a known dual. Develop the LP for THIS specific scheme; does it give δ* exactly? (Note: a generic LP-vs-Parseval no-go exists, but the SCHEME-SPECIFIC LP with the cyclotomic Krein parameters may differ.) Honest verdict.`},
  {id:'code-transfer', t:`Explicit TRANSFER from a SOLVED decodable family. Dyadic RS = an evaluation code on μ_{2^μ}. Is there an EXPLICIT, list-size-preserving map to a family whose list-decoding radius IS known — folded RS (GG25), multiplicity/derivative codes (Kopparty), AG codes, or the BCH view? The prize is the EXPLICIT case; find a map that transports the known radius. (Random/folded need randomness μ_n lacks — but a STRUCTURED map specific to 2-power evaluation points might work.) Honest verdict.`},
  {id:'effective-linnik', t:`Attack the GOOD-PRIME existence DIRECTLY (the irreducible residue). Bad primes divide specific cyclotomic-difference norms; bound their COUNT/distribution at scale p~n^4·2^38 using the best analytic NT: Linnik's theorem on least primes in AP, the LARGE SIEVE, log-free zero-density estimates, Bombieri-Vinogradov. Can a good prime of size 2^38·n^4 be PROVEN to exist (avoiding the finite bad set)? Quantify the bad-prime count log R_n vs the prime density. Honest verdict on whether effective Linnik suffices or the bad-count is too large.`},
  {id:'amplification-bootstrap', t:`SELF-IMPROVING amplification. Assume a WEAK bound M(n)≤B(n) (e.g. the trivial n or BGK n^{1−o(1)}); can the TENSOR-POWER / tower structure BOOTSTRAP it to the sharp √(n log m)? The k-th tensor power of the code, or the relation M(n) via M(n^{1/2}), or a Bourgain-Gamburd-style expansion. Develop the bootstrap recursion; does it have a contracting fixed point at √(n log m)? (Dyadic tower descent was saving-neutral — but a NONLINEAR amplification may differ.) Honest verdict.`},
  {id:'dyadic-norm-recursion', t:`The DYADIC-TOWER relative-norm recursion at MATCHED thinness (the unresolved D). N:ℤ[ζ_{2^μ}]→ℤ[ζ_{2^{μ−1}}] maps wraparound at level μ to μ−1. Take the tower at FIXED p/n^4 (matched thinness across levels, avoiding the onset-scaling issue). Compute/derive the contraction factor of W_r(2^μ) vs W_r(2^{μ−1}). If <1, telescopes to the μ_2 base (provable). Machine-test at matched thinness. Honest verdict.`},
  {id:'RH-transfer', t:`Transfer via the RIEMANN HYPOTHESIS for a Dedekind/Hecke L-function. The wraparound / good-prime question is about prime splitting in ℚ(ζ_n) and divisibility of cyclotomic norms. Under GRH for the relevant Hecke L-functions, effective equidistribution (effective Chebotarev under GRH, Lagarias-Odlyzko) gives a good prime at polynomial size. Is the prize TRUE under GRH (a conditional closure)? Develop the GRH-conditional argument precisely. A conditional proof is a NEW-REDUCTION (prize ⟸ GRH). Honest verdict on whether GRH suffices.`},
  {id:'circle-method', t:`The HARDY-LITTLEWOOD CIRCLE METHOD for the wraparound count W_r at the cyclotomic place. W_r counts solutions to Σx≡Σy mod 𝔭 with a SMALLNESS constraint; set up the circle method over ℤ[ζ_n]/𝔭 with major arcs (the main/Eisenstein term) and minor arcs (the fluctuation). Does the major-arc term give the rank-INDEPENDENT main count, with minor arcs provably smaller via the 2-power structure? (Minor arcs = the wall generically — but the 2-power-specific major-arc analysis may dominate.) Honest verdict.`},
  {id:'complexity-lowerbound', t:`A COMPLEXITY-THEORETIC reframing. Is computing δ* (or the list size / W_r) #P-hard or related to a natural complexity class? Conversely, does a complexity SEPARATION or a proof-complexity bound (the W_r count as a certificate) give an UNCONDITIONAL lower/upper bound on δ*? Explore whether the prize connects to a complexity-theoretic statement that's PROVABLE (e.g., a natural-proofs-style barrier, or a #P-hardness that pins the value). Genuinely ambitious; honest verdict on whether it yields anything provable.`},
]

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, sz){
  let acc=[]
  for (const [i,w] of chunk(items,sz).entries()){
    log(`wave ${i+1}/${Math.ceil(items.length/sz)} (${w.map(x=>x.id||x).join(',')})`)
    acc=acc.concat(((await parallel(w.map(it=>()=>mk(it))))||[]).filter(Boolean))
  }
  return acc
}

phase('Explore')
const explored = await waved(ANGLES, (A) => agent(
  `${FRAME}

AMBITIOUS FRAMEWORK ${A.id}: ${A.t}
Develop it concretely (math, not vibes). Machine-test where possible. Return the honest structured verdict.`,
  {label:`explore:${A.id}`, phase:'Explore', schema:{...SCHEMA}}
), 4)

phase('Verify')
const claims = explored.filter(r => r.outcome==='NEW-REDUCTION' || r.outcome==='PARTIAL')
const verified = await waved(claims, (r) => agent(
  `${FRAME}

ADVERSARIALLY VERIFY the ${r.outcome} claim for ${r.id}: ${(r.finding||'').slice(0,500)}
Is it a GENUINE new reduction / partial result, or does it secretly reduce to the wall (period spectrum /
rank-n/2 obstruction / fixed-prime arithmetic)? Trace it hard. For a conditional reduction (e.g. ⟸ GRH),
confirm the hypothesis is genuinely weaker/different, not equivalent to the prize. Re-verdict honestly.`,
  {label:`verify:${r.id}`, phase:'Verify', schema:{...SCHEMA}}
), 3)

phase('Synthesize')
const vmap = new Map(verified.filter(Boolean).map(v=>[v.id,v]))
const fin = explored.map(r=>vmap.get(r.id)||r)
const tally={}; for(const r of fin) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`ambitious-frameworks done: ${JSON.stringify(tally)}`)
return {
  tally,
  results: fin.map(r=>({id:r.id, outcome:r.outcome, finding:(r.finding||'').slice(0,500),
    mechanism:(r.mechanism||'').slice(0,300), nextStep:(r.nextStep||'').slice(0,200),
    fileContent: r.fileContent||''})),
}
