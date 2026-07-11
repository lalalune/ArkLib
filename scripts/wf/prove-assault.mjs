export const meta = {
  name: 'prove-assault',
  description: 'Pull on every remaining open thread of δ* and try to PROVE: char-p transfer, spectral/Paley face, t-wise independence, downstream objects, then ASSEMBLE the proven pieces to close the gap (#444)',
  phases: [
    { title: 'Attack',   detail: '14 prove-oriented threads: char-p transfer, spectral, independence, downstream, novel' },
    { title: 'Verify',   detail: 'adversarial audit of every claimed proof/landing/refutation' },
    { title: 'Assemble', detail: 'combine the proven pieces into the tightest end-to-end conditional; pin the minimal gap' },
  ],
}
const DIR = 'ArkLib/Data/CodingTheory/ProximityGap/Frontier'
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const FRAME = `ArkLib #444 (Ethereum Proximity Prize, ABF26 ePrint 2026/680). GOAL: PROVE the prize (or prove a
genuine sub-piece, or pin the minimal gap). THE SINGLE MINIMAL OPEN RESIDUAL:
  the char-p energy bound at a SINGLE depth r*=⌈log p⌉:  E_{r*}(μ_n; F_p) ≤ (2r*−1)‼·n^{r*}
  (n=2^30, p≈n·2^128, r*≈110).  [⟹ M=max_{b≠0}|η_b| ≤ √(2e·n·log p) ⟹ δ* window interior — all PROVEN downstream.]
Here E_r(G) = #{x₁+..+x_r = y₁+..+y_r : xᵢ,yᵢ∈μ_n} (additive energy / 2r-th moment); η_b = Σ_{x∈μ_n}e_p(bx).
PROVEN IN-TREE (build on these EXACT handles — do NOT re-derive):
• char-0: E_r^{char0} ≤ (2r−1)‼·n^r (Lam–Leung antipodal matchings of distinct values; falling-factorial
  basis c_r=(2r−1)‼ EXACT, c_{r−1}=0 EXACT). The OPEN part is ONLY the char-p TRANSFER at deep r.
• base case r=1: μ_2 = n(p−n)/(p−1) ≤ n UNCONDITIONAL — _OpenCoreCharPLighterReduction.base_case_r1.
• monotone induction: base + moment-ratio μ_{r+1}·Wick_r ≤ μ_r·Wick_{r+1} ⟹ μ_{2r}≤Wick_r ALL r —
  _OpenCoreMonotoneReduction.open_core_of_subGaussian_growth.
• moment identities: ∑_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r} (DCSubtractedMoment.sum_nonzero_moment);
  ∑_{all b}‖η_b‖^{2r} = q·E_r (SubgroupGaussSumMoment.subgroup_gaussSum_moment). E_2=3n(n−1) (REnergyTwoExact).
• Wick algebra: oddDoubleFactorial, _MomentSaddleValue (M^{2r}≤q·Wick ⟹ M≤√(2en log p)). Λ(q)=energy
  (_LambdaQMeanZeroEnergy), spectral M=2nd eigenvalue of Cay(F_p,μ_n) (_LambdaQSpectralMoment).
• W_r excess (memory): W_r = E_r − E_r^{char0} is an ONSET-THRESHOLD, NOT a birthday power law. EXACT recompute:
  W_3=0 generic; W_4=0 at ALL tested non-Fermat n16 primes (nonzero only Fermat 65537); onset r_0(n) with
  n16: 4<r_0<6, n32: 4<r_0<5. The prize ⟺ onset r_0(n) > r*≈log p (no wraparound excess at the saddle depth).
EXHAUSTED — do NOT rehash (memory): generic moment/energy/sup-norm; 2-power Clifford & TOWER decoupling
(REFUTED, saving-preserving); good-prime counting (exponential bad-count); GRH (insufficient by counting);
modular gen-fn; the entire Λ(q) face (12 bricks, all reduce/refuted); the literature (0 verified routes, exp
1−o(1) SOTA); modern tools decoupling/restriction/VMVT (no-go, μ_n flat 0-dim); probabilistic extreme-value
(periods exchangeable white-noise not log-correlated); Schur/association-scheme (trivial/→√S).
BUILD: scripts/pg-iterate.sh <file> (lock-free; sorry=WARNING — READ #print axioms). autoImplicit OFF —
declare ALL binders. Minimal imports. Repo ${REPO}.
HONESTY (PARAMOUNT): NEVER fabricate closure. PROVED = a genuine UNCONDITIONAL axiom-clean theorem of a real
sub-piece. LANDED = axiom-clean conditional brick with a NAMED open hyp that IS the genuine open part (not a
vacuous/circular discharge). REDUCED = precise reduction. REFUTED = machine countermodel. A brick that "proves"
the prize via a hypothesis secretly equal to the prize is the ONE FORBIDDEN move — name such hypotheses
honestly. #print axioms ⊆ {propext, Classical.choice, Quot.sound}, NO sorryAx/native_decide. Clobber-proof:
RETURN the full fileContent.`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['id','outcome','summary'],
  properties:{
    id:{type:'string'},
    outcome:{type:'string', enum:['PROVED','LANDED','REDUCED','REFUTED','DERIVED','PARTIAL','FAILED']},
    axiomsClean:{type:'boolean'}, file:{type:'string'}, keyTheorem:{type:'string'}, axioms:{type:'string'},
    provesUnconditionally:{type:'boolean'}, namedResidual:{type:'string'},
    fileContent:{type:'string'}, finding:{type:'string'}, summary:{type:'string'} },
}

const THREADS = [
  // ---- CORE RESIDUAL: the char-p transfer (the whole prize) ----
  {id:'T1-noexcess-onset', file:'_NoExcessOnsetThreshold', t:`PROVE the wraparound excess W_r = E_r − E_r^{char0} VANISHES (or ≤ slack_r) for r up to r*≈log p. The exact recompute shows W_r is an ONSET-THRESHOLD (W_3=0, W_4=0 at non-Fermat primes; onset r_0(n)). W_r > 0 requires a nontrivial additive relation x₁+..+x_r ≡ y₁+..+y_r (mod p) that is NOT a char-0 relation — i.e. a genuine WRAPAROUND (sum lands in a different residue class). Build the EXACT W_r framework (W_r counts wraparound solutions) and PROVE: a wraparound at depth r needs the r-fold sumset of μ_n to exceed p, i.e. needs r ≥ r_0(n) where r_0(n) is the smallest r with (diameter of r-fold sums) ≥ p. Land the implication "no r-fold wraparound ⟹ W_r = 0 ⟹ E_r = E_r^{char0} ≤ Wick" axiom-clean, and pin the precise r_0(n) > r* question (= the prize). This is the SHARPEST core attack.`},
  {id:'T2-lamleung-charp', file:'_LamLeungCharPInjection', t:`Build the CHAR-P Lam–Leung matching injection. Char-0: energy solutions ↪ (matchings of the 2r values into antipodal-or-equal pairs) × [n]^r, giving E_r^{char0} ≤ (2r−1)‼·n^r. Build the char-p version: an injection from F_p energy solutions to (matchings × [n]^r × wraparound-tag) where the wraparound-tag is bounded. Land the ABSTRACT injection lemma axiom-clean: |solutions| ≤ |matchings|·n^r·(1+τ) given an injection with tag-multiplicity ≤ τ; name τ (the wraparound-tag count) as the open residual = the W_r excess.`},
  {id:'T3-frobenius-descent', file:'_FrobeniusEnergyDescent', t:`GALOIS / FROBENIUS descent on the energy solutions. σ_p (Frobenius x↦x^p) permutes μ_n and acts on the solution set of x₁+..+x_r=y₁+..+y_r. Since p≡1 (mod n) at the prize (n | p−1, μ_n⊂F_p), σ_p fixes μ_n pointwise (p≡1 mod n ⟹ x^p=x on μ_n) — so Frobenius is TRIVIAL on F_p solutions. Land this exactly (σ_p=id on μ_n ⟹ no Galois reduction of the F_p count) as an HONEST no-go brick, AND pivot: the descent that DOES help is over the TOWER Z/p ← Z (char-0 lift); build the reduction-mod-p map on the char-0 solution set and bound its fibers. Land what's provable; name the fiber residual.`},
  {id:'T4-stickelberger', file:'_StickelbergerValuation', t:`STICKELBERGER / Gross–Koblitz 2-adic valuation. Gauss sums g(χ) for χ of 2-power order have controlled valuation (Stickelberger: the prime factorization of g(χ) is explicit). η_b = (n/(p−1))Σ_χ χ̄(b)g(χ) over χ of order | n. Build the valuation framework: does the Stickelberger valuation of the order-2^k Gauss sums constrain Σ_χ χ̄(b)g(χ) (cancellation from valuation)? Land the valuation identity for 2-power χ axiom-clean and DERIVE whether it bounds |η_b| below the trivial n, or REFUTE that valuation helps (the |g(χ)|=√p is archimedean, valuation is ℓ-adic — orthogonal). Honest verdict.`},
  // ---- SPECTRAL / PALEY-GRAPH face ----
  {id:'T5-expander-mixing', file:'_ExpanderMixingBound', t:`EXPANDER MIXING on Cay(F_p,μ_n). M = 2nd eigenvalue. The expander mixing lemma relates M to edge-discrepancy: |e(S,T) − n|S||T|/p| ≤ M√(|S||T|). RUN it in REVERSE: a SET S,T with known edge count gives a LOWER bound on M (Parseval ⟹ M≥√(n−n²/p)); an UPPER bound needs the discrepancy to be small for ALL S,T = the wall. Land the mixing lemma instance for μ_n axiom-clean and DERIVE the exact two-sided bound it gives; name the all-S,T discrepancy residual = the sup-norm wall. Honest REDUCED.`},
  {id:'T6-interlacing-tower', file:'_EigenvalueInterlacingTower', t:`CAUCHY INTERLACING via the 2-power tower. Cay(F_p,μ_n) contains Cay(F_p,μ_{n/2}) structure (μ_{n/2}⊂μ_n). Cauchy interlacing relates the eigenvalues (η_b for μ_n vs μ_{n/2}). η_b(μ_n) = η_b(μ_{n/2}) + η_{b}(coset) (coset-doubling, in-tree _LambdaQTowerTensor.cosetDouble). Build the interlacing/recursion on M(n) vs M(n/2) axiom-clean; does it give M(n) ≤ √2·M(n/2) (⟹ M(n) ≤ n^{?}) or is it saving-neutral (memory: tower decoupling refuted)? Land the exact recursion and its consequence for the exponent.`},
  // ---- ARCSINE / INDEPENDENCE face ----
  {id:'T7-twise-independence', file:'_TwiseIndependenceFramework', t:`t-WISE INDEPENDENCE of the dilated phases. η_b=Σ_{k=1}^{n/2} 2cos(b·x_k); pairwise near-independence is in-tree (_PhasePairwiseToSubGaussian). For the r-th moment μ_{2r}≤Wick we need the joint moments to factorize up to order 2r, i.e. (2r)-wise independence of the phases (equivalently: the r-fold additive relations among the x_k are only the diagonal = the char-0 matchings). Build the framework "if the dilated set {b·x_k} is t-wise additively independent (no nontrivial ≤t-term ±1 relation mod p) then μ_{2r}≤Wick_r for r≤t/2" axiom-clean. The t-wise independence at t≈log m IS the open content (= no short relation = W_r=0). Name it precisely; this UNIFIES the independence and energy faces.`},
  {id:'T8-NA-moment', file:'_NegativeAssocMoment', t:`NEGATIVE ASSOCIATION full-moment route. The falling factorial (n)_r = sampling WITHOUT replacement = negatively associated (NA). The periods have Cov(η_a,η_b)=−Var/(m−1)<0. Build/extend the NA moment inequality: an NA family's even moments satisfy E[(ΣYₖ)^{2r}] ≤ (2r−1)‼·(ΣVar)^r (the NA sub-Gaussian/Wick bound — NA ⟹ moments ≤ independent ⟹ Gaussian). Land the abstract "NA ⟹ μ_{2r} ≤ Wick_r" implication axiom-clean and state the named hypothesis that the μ_n phase contributions form an NA family at depth r (= the multiplicative structure is negatively associated, the prize-TRUE direction). Genuinely-new structural attack.`},
  // ---- CONDITIONAL / AGGREGATE ----
  {id:'T9-goodprime-density', file:'_GoodPrimeFamilyDensity', t:`GOOD-PRIME DENSITY in the prize FAMILY. The prize fixes a family p=Θ(n^β), n=2^μ. At depth r, a "bad" p is one where a wraparound relation x₁+..+x_r≡y₁+..+y_r (mod p) holds that fails over ℤ — i.e. p | (a nonzero integer of size ≤ 2r·n ≤ 2^{O(log p)·30}). Count: each char-0-violating relation excludes the primes p dividing a bounded integer. DERIVE the density of bad primes at depth r* (is it o(1)? cofinite? positive density of GOOD p?). If GOOD p has positive density in the family AND the prize allows choosing p, the bound holds for SOME prize-valid p. Land the bad-prime-count bound axiom-clean (bad p ⊆ divisors of ∏(relation values)) and DERIVE the density; honest on whether the prize fixes p or allows choice.`},
  {id:'T10-almostall-amplify', file:'_AlmostAllToAllAmplify', t:`AMPLIFY almost-all-b to all-b. Parseval gives |η_b|~√n for ALMOST ALL b (the 2nd moment). The worst b is the wall. Build the amplification: the number of "bad" b (|η_b|>λ√n) is ≤ μ_{2r}/(λ√n)^{2r}·(p−1) (Markov/moment); if μ_{2r}≤Wick this is < 1 for λ=√(2 log m), forcing ZERO bad b = the prize. So the moment bound ⟹ all-b via Markov (this is the union bound, in-tree _MomentSaddleValue). Land the EXACT "≤K bad b at level λ" Markov brick axiom-clean and confirm it reduces all-b to the SAME moment bound — i.e. there is NO amplification gain beyond the moment (honest REDUCED, closes the 'maybe almost-all helps' hope).`},
  // ---- DOWNSTREAM OBJECTS ----
  {id:'T11-curve-decodability', file:'_CurveDecodabilityOpener', t:`CURVE-DECODABILITY (GG25 Def 3.1, B2 route) — a DIFFERENT object the prize reduces to. The MCA δ* relates to list-decoding the explicit RS code along curves. Build the explicit-μ_n curve-decodability OPENER (the Def 3.1 predicate as a Lean Prop + the first reduction step). Does the curve route BYPASS the sup-norm M, or reduce to it? Land the opener axiom-clean and the honest verdict on bypass-vs-reduce (memory: line-decoding reduces to BCHKS 1.12 = same wall; check if the CURVE version differs).`},
  {id:'T12-bchks-trilinear', file:'_BCHKSTrilinearConditional', t:`BCHKS 1.12 / di-Benedetto-beat trilinear (the SOTA-closest lever). di Benedetto H^{1−31/2880} via the Petridis–Shparlinski trilinear |X|^{3/4}|Y|^{3/4}|Z|^{7/8} (p^{1/4} tax). Land the CONDITIONAL implication "a trilinear estimate Σ_{x,y,z} with saving s at the prize exponent ⟹ μ_{2r}≤Wick / M≤prize" axiom-clean, with the precise trilinear-saving residual named (the p^{1/4}-tax removal at H~p^{1/5}). This packages the single most quantitatively-close external lever as a named Prop. Honest: the residual IS the half-power gap.`},
  // ---- NOVEL ----
  {id:'T13-novel-angle', file:'_NovelTransferOperator', t:`INVENT a genuinely-new angle NOT in the exhausted list. Candidate: a TRANSFER-OPERATOR / p-adic-analytic / tropical / generating-function-with-a-twist attack on E_r. E.g. the generating function Σ_r E_r z^r / r! and its analytic structure; or a transfer operator on the 2-adic tower whose spectral radius bounds the energy growth; or a p-adic interpolation of E_r in r. Build the object, prove its provable properties axiom-clean, apply to the deep-r bound. Genuinely new; name the open residual honestly. Bold exploration encouraged — label conjectural parts.`},
  {id:'T14-novel-shaw', file:'_ShawDeepTransferLaw', t:`INVENT + apply a NEW named "Shaw" theorem for the deep-r char-p transfer. State a precise NEW principle (e.g. "the Shaw transfer radius: E_r(F_p)/E_r^{char0} ≤ exp(r²/2n) with the defect controlled by the r-fold sumset diameter") and what it gives. Build the object, prove the provable skeleton (the diameter ⟹ no-wraparound ⟹ transfer direction), apply to r*≈log p. Name the precise open analytic residual. Genuinely-new named object; honest scope.`},
]

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, sz, lbl){
  let acc=[]
  for (const [i,w] of chunk(items,sz).entries()){
    log(`${lbl} wave ${i+1}/${Math.ceil(items.length/sz)} (${w.map(x=>x.id||x.file||'?').join(', ')})`)
    acc=acc.concat(((await parallel(w.map(it=>()=>mk(it))))||[]).filter(Boolean))
  }
  return acc
}
const hard = new Set(['T1-noexcess-onset','T2-lamleung-charp','T7-twise-independence','T8-NA-moment','T13-novel-angle','T14-novel-shaw'])
const mk = (T) => agent(
  `${FRAME}

THREAD ${T.id}. Create ${DIR}/${T.file}.lean. ${T.t}
Return the structured verdict + the COMPLETE fileContent (clobber-proof).`,
  {label:`atk:${T.id}`, phase:'Attack', effort: hard.has(T.id)?'high':'medium', schema:{...SCHEMA}})

phase('Attack')
const attacked = await waved(THREADS, mk, 4, 'Attack')

phase('Verify')
const toV = attacked.filter(r=>(r.outcome==='PROVED'||r.outcome==='LANDED'||r.outcome==='REFUTED'||r.outcome==='REDUCED'||r.outcome==='PARTIAL') && r.axiomsClean!==false && r.fileContent)
const verified = await waved(toV, (r)=>agent(
  `${FRAME}

ADVERSARIALLY VERIFY ${r.outcome} for ${r.id} (${DIR}/${(r.file||'').split('/').pop()}). key=${r.keyTheorem||'?'}; claimed namedResidual=${r.namedResidual||'?'}.
Re-run pg-iterate; confirm no sorry/native_decide, #print axioms ⊆ {propext,Classical.choice,Quot.sound}. Judge
FAITHFULNESS HARD: if it claims PROVED (unconditional), is the theorem REALLY unconditional and a genuine
sub-piece (not vacuous, not the prize laundered)? If conditional, is the named hypothesis the GENUINE open part
(deep-r multiplicative deviation / wraparound = BGK), NOT silently discharged or circular? For a refutation,
is the countermodel a real exact F_p compute? Re-verdict honestly + fileContent.`,
  {label:`vfy:${r.id}`, phase:'Verify', effort:'medium', schema:{...SCHEMA}}), 3, 'Verify')

phase('Assemble')
const vmap=new Map(verified.filter(Boolean).map(v=>[v.id,v]))
const fin=attacked.map(r=>vmap.get(r.id)||r)
const landed=fin.filter(r=>r.outcome==='PROVED'||r.outcome==='LANDED'||r.outcome==='REDUCED')
const ledger = landed.map(r=>`${r.id} [${r.outcome}] key=${r.keyTheorem||'?'} residual=${(r.namedResidual||'').slice(0,140)} :: ${(r.finding||r.summary||'').slice(0,240)}`).join('\n')
const assembled = await waved([
  {id:'A1-assemble', file:'_ProveAssembly', t:`ASSEMBLE the tightest end-to-end conditional. Read the landed pieces below and the in-tree proven handles (base_case_r1, open_core_of_subGaussian_growth, sum_nonzero_moment, _MomentSaddleValue, Λ(q)=energy). Build ONE Lean brick that chains the MAXIMAL proven prefix toward M≤√(2en log p), reducing the prize to the SINGLE tightest named residual (the one open hypothesis). State that residual as precisely as the pieces allow (ideally: "no r-fold wraparound for r≤r*", i.e. the onset r_0(n)>r*). Land it axiom-clean. This is the consolidation deliverable.
LANDED PIECES:\n${ledger}`},
  {id:'A2-gap', file:null, t:`GAP ANALYSIS (no Lean). Given the landed pieces below, write the PRECISE minimal remaining gap: the single mathematical statement whose proof would close the prize, expressed in the most elementary/attackable form across the faces (energy / wraparound-onset / t-wise-independence / NA / spectral). Identify which face gives the most tractable form of the SAME gap, and whether any landed piece UNCONDITIONALLY advances the known frontier (vs reduces). Be brutally honest: is anything actually closer to a proof, or is it all the same wall re-expressed?
LANDED PIECES:\n${ledger}`},
], (T)=>agent(
  `${FRAME}

${T.id}. ${T.file?`Create ${DIR}/${T.file}.lean. `:'(analysis only.) '}${T.t}
Return the structured verdict + ${T.file?'full fileContent':"the analysis in 'finding'"}.`,
  {label:`asm:${T.id}`, phase:'Assemble', effort:'high', schema:{...SCHEMA}}), 2, 'Assemble')

const tally={}; for(const r of [...fin,...assembled]) tally[r.outcome]=(tally[r.outcome]||0)+1
log(`prove-assault done: ${JSON.stringify(tally)}`)
return { tally,
  results: [...fin,...assembled].map(r=>({id:r.id, outcome:r.outcome, axiomsClean:r.axiomsClean, file:r.file,
    keyTheorem:r.keyTheorem, provesUnconditionally:r.provesUnconditionally, namedResidual:(r.namedResidual||'').slice(0,200),
    finding:(r.finding||'').slice(0,500), fileContent:r.fileContent||''})) }
