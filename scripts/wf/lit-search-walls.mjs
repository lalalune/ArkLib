export const meta = {
  name: 'lit-search-walls',
  description: 'Exhaustive literature sweep for ANY technique (even conditional / prize-range-only) that gives exponent 1/2 for 2-power subgroup Gauss-period sup-norm — the δ* wall (#444)',
  phases: [
    { title: 'Sweep',     detail: '13 literature domains, broad WebSearch for candidate techniques' },
    { title: 'DeepRead',  detail: 'fetch + extract exact statement & regime of validity of the distinct leads' },
    { title: 'PrizeCheck',detail: 'adversarial: does it actually beat exponent ≈1 at n~p^{1/5.3}, 2-power, worst-case b?' },
    { title: 'Synthesize',detail: 'the literature ledger + conditional-path verdict + uncovered-domain critic' },
  ],
}

const FRAME = `ArkLib #444 (Ethereum Proximity Prize, ABF26 ePrint 2026/680, proximityprize.org, $1M).
We need a LITERATURE ROUTE to ONE analytic bound. THE OBJECT:
  M := max_{b ∈ F_p^*} | Σ_{x ∈ H} e_p(b·x) |,   e_p(t) = exp(2πi·t/p),
where H = μ_n = the n-th roots of unity in F_p^* and n = 2^μ is a POWER OF TWO (n | p−1). This is the
GAUSS PERIOD / the non-principal eigenvalue of the generalized Paley graph Cay(F_p, μ_n).
PRIZE PARAMETERS (exact — this is the ONLY regime that matters; a result that needs a different regime
does NOT count unless it can be specialized here):
  • n = 2^30 ≈ 1.07e9, a 2-POWER subgroup (thin + highly structured).
  • p prime, p ≈ n·2^128 ≈ 2^158, so n ≈ p^{1/5.27} — the subgroup is THIN, |H| ≈ p^{0.19} (BELOW p^{1/4}).
  • m := (p−1)/n ≈ 2^128 cosets; ln m ≈ 88.7; saddle depth r* ≈ ln p ≈ 110.
GOAL ("prize floor"): M ≤ C·√(n·log m) ≈ 9.4·C·√n — i.e. EXPONENT 1/2 (up to a √log factor).
  EQUIVALENT FORMS (any one suffices — search ALL their literatures):
   (a) μ_n is a Λ(q)-SET with BOUNDED constant at q ≈ 2 ln m ≈ 178 (Rudin Λ(p)-set theory).
   (b) additive moments E_k(H) := #{x₁+..+x_k = y₁+..+y_k : xᵢ,yᵢ∈H} ≤ (2k−1)!!·n^k for k up to ≈ ln p (Wick/Gaussian).
   (c) the period is SUB-GAUSSIAN with variance proxy n (concentration / large deviations).
   (d) Cay(F_p, μ_n) is ~RAMANUJAN: M ≤ 2√n (this is the strong form; the prize only needs the √log-relaxed (a)).
STATE OF THE ART WE ALREADY HAVE (find something BETTER, or a CONDITIONAL/SPECIAL-CASE route):
  • Unconditional best at n~p^{1/5}: BGK (Bourgain–Glibichuk–Konyagin 2006) gives M ≤ n^{1−δ'} with δ'>0 TINY
    & ineffective (n^{1−o(1)}) — EXPONENT ≈1. di Benedetto–Solymosi–White (arXiv 2003.06165) gives
    H^{1−31/2880} but REQUIRES |H|>p^{1/4} and VANISHES at/below p^{1/4} — the prize n~p^{0.19} is BELOW it.
    Heath-Brown–Konyagin is VACUOUS below |H|~p^{1/3}. So all known unconditional bounds give exponent ≈1; the
    prize needs 1/2. THE GAP IS A FULL HALF-POWER IN THE EXPONENT.
  • Paley Graph Conjecture (M ≤ 2√n) would suffice but is OPEN; best toward it = BGK n^{1−o(1)}.
  • "Almost all b" is EASY (Parseval/2nd-moment give |η_b|~√n for a.e. b) — the WORST-CASE b is the entire wall.
THE ASK: search HARD — INCLUDING bodies of work that are NEW framings for this problem (Rudin/Bourgain Λ(p)-set
theory; random-multiplicative-function better-than-√ cancellation à la Harper/Soundararajan; generalized-Paley-
graph eigenvalue bounds à la Chi-Hoi Yip / Hanson–Petridis; hypercontractivity / Bonami over F_p; Gauss-period
equidistribution à la Duke–Garcia–Lutz / Katz / Kowalski–Sawin) — for ANY result, even CONDITIONAL (GRH,
Lindelöf, GRC, a provable-in-this-range hypothesis) or SPECIAL-CASE (2-power / smooth-order subgroups
specifically), that yields exponent 1/2, OR any improvement of the exponent toward 1/2, for M in the prize
regime (n ~ p^{1/5.3}, 2-power H, WORST-CASE b). Always report the REGIME OF VALIDITY precisely and whether it
survives specialization to the prize parameters.
ANTI-FABRICATION (PARAMOUNT, non-negotiable): every cited result MUST have a verifiable identifier (arXiv ID /
ePrint / DOI / journal+year+authors) that you CONFIRMED EXISTS via WebSearch/WebFetch this run. If you cannot
verify a paper exists, mark it UNVERIFIED and do NOT present it as real. Inventing a plausible-looking citation
is the WORST possible failure — a known prior failure mode on this project. Prefer 5 verified leads to 20 guesses.
TOOLS: FIRST call ToolSearch with query "select:WebSearch,WebFetch" to load the web tools, then use them. Search
arXiv (math.NT, math.CA, math.CO), ePrint/IACR, Google Scholar-style queries, and author homepages.`

const SWEEP_SCHEMA = {
  type:'object', additionalProperties:false, required:['domain','leads','summary'],
  properties:{
    domain:{type:'string'},
    leads:{type:'array', items:{type:'object', additionalProperties:false,
      required:['title','cite','claim','regime','prizeVerdict'],
      properties:{
        title:{type:'string'}, authors:{type:'string'}, cite:{type:'string', description:'arXiv/ePrint/DOI/journal+year — VERIFIED'},
        verified:{type:'boolean'}, claim:{type:'string'}, regime:{type:'string'},
        prizeVerdict:{type:'string', enum:['BEATS_BGK','IMPROVES_EXPONENT','MATCHES_BGK','VANISHES_AT_PRIZE','CONDITIONAL','IRRELEVANT','UNVERIFIED']},
        why:{type:'string'} }}},
    notFound:{type:'string', description:'what you searched for and did NOT find'},
    summary:{type:'string'} },
}
const DEEPREAD_SCHEMA = {
  type:'object', additionalProperties:false, required:['cite','verified','exactStatement','regimeOfValidity','summary'],
  properties:{ cite:{type:'string'}, verified:{type:'boolean'}, exactStatement:{type:'string'},
    regimeOfValidity:{type:'string'}, conditionalOn:{type:'string'}, appliesAtPrize:{type:'string'}, summary:{type:'string'} },
}
const CHECK_SCHEMA = {
  type:'object', additionalProperties:false, required:['cite','verified','verdict','summary'],
  properties:{ cite:{type:'string'}, verified:{type:'boolean'},
    verdict:{type:'string', enum:['REAL_CONDITIONAL_PATH','REAL_EXPONENT_GAIN','SOTA_BUT_NOT_PRIZE','VANISHES_AT_PRIZE','REDUCES_TO_WALL','IRRELEVANT','UNVERIFIED_DROP']},
    exponentAtPrize:{type:'string'}, conditionalOn:{type:'string'}, gapToHalfPower:{type:'string'},
    actionable:{type:'boolean'}, howToUse:{type:'string'}, confidence:{type:'string'}, summary:{type:'string'} },
}

const DOMAINS = [
  {id:'D1-subgroupsums', t:`CHARACTER SUMS OVER MULTIPLICATIVE SUBGROUPS — SOTA 2006–2026. Bourgain–Glibichuk–Konyagin and ALL successors: Bourgain–Chang, Konyagin, Shkredov, Shparlinski, Macourt, Kerr, di Benedetto–Solymosi–White, Petridis–Shparlinski, Mohammadi–Shkredov–Warren, Hanson, Murphy–Rudnev. For max_{a≠0}|Σ_{x∈H}e_p(ax)|, |H|~p^{1/5}: what is the BEST exponent as of 2026, and is there ANY result SPECIFIC to 2-power / smooth-order subgroups that beats generic BGK? Find the sharpest exponent and its |H| threshold.`},
  {id:'D2-lambdaP', t:`RUDIN Λ(p)-SET THEORY (harmonic analysis of thin sets). Rudin 1960; Bourgain's Λ(p)-set theorem; Pisier; Bourgain–Lewko; Talagrand; the relation Λ(2k)-constant ⟺ additive 2k-th moment ⟺ B_k[g]/Sidon structure. KEY QUESTION: is the Λ(q)-constant of a MULTIPLICATIVE SUBGROUP of F_p (or of n-th roots of unity) known, bounded, or estimated anywhere? Any theorem "arithmetic/structured sets are Λ(q) with bounded constant"? Dissociated sets, quasi-independent sets, the Λ(q)-constant growth in q.`},
  {id:'D3-gaussperiods', t:`GAUSS PERIOD / GAUSS SUM DISTRIBUTION & MOMENTS. Myerson "Period polynomials and Gauss sums"; Gurak; Duke–Garcia–Lutz "Pair correlation of Gauss periods / sums of roots of unity"; Lehmer; Katz "Gauss sums Kloosterman sums monodromy groups"; Kowalski–Sawin "Kloosterman paths"; Baker; the equidistribution / sub-Gaussian-tail / moment results for Gaussian periods of 2-POWER order specifically. Is the worst-case (not average) size of a Gauss period of 2-power order bounded by √n·polylog anywhere?`},
  {id:'D4-additiveenergy', t:`ADDITIVE ENERGY & HIGHER ENERGIES OF SUBGROUPS (additive combinatorics). Shkredov's E_k energy bounds; Murphy–Roche-Newton–Rudnev–Shkredov; Konyagin–Shkredov "new sum-product"; the higher additive energy E_k(H) of a multiplicative subgroup H at LARGE k (k~log p). Is there a bound E_k(H) ≤ (2k−1)!!·n^k (Gaussian/Wick) or close, for k up to log p, for subgroups — even 2-power ones? Few-sums-many-products line, Stepanov-method energy bounds.`},
  {id:'D5-paleygraphs', t:`GENERALIZED PALEY GRAPHS / PSEUDORANDOM CAYLEY GRAPHS. Liu–Zhou; Chi-Hoi Yip (MANY 2021–2024 papers on generalized Paley graphs, cliques, eigenvalues — search "Chi Hoi Yip generalized Paley graph"); Hanson–Petridis; the Paley Graph Conjecture status; eigenvalue bounds for Cay(F_q, S) with S a multiplicative subgroup. Any NON-PRINCIPAL EIGENVALUE bound for Cay(F_p, μ_n) with μ_n a 2-power subgroup that beats n^{1−o(1)}? Ramanujan-ness of these specific Cayley graphs.`},
  {id:'D6-randommult', t:`RANDOM MULTIPLICATIVE FUNCTIONS & BETTER-THAN-√ CANCELLATION. Adam Harper "Moments of random multiplicative functions / better than squareroot cancellation"; Soundararajan; Chatterjee–Soundararajan; Gorodetsky; Najnudel; Benatar–Nishry–Rodgers. KEY: Harper proved partial sums of random multiplicative functions are SUB-GAUSSIAN / have better-than-√ cancellation. Does ANY of this machinery (low moments, multiplicative chaos, Gaussian-ness) transfer to the DETERMINISTIC Gauss period Σ_{x∈μ_n}e_p(bx) over the b-average, giving worst-case or almost-all sub-Gaussian tails at exponent 1/2?`},
  {id:'D7-recency', t:`PURE RECENCY SWEEP 2023–2026 on incomplete/subgroup character sums, Gauss periods, multiplicative-subgroup pseudorandomness. Search arXiv math.NT new submissions, IACR ePrint, for ANYTHING in the last ~3 years improving subgroup-sum bounds, motivated by STARKs/FRI/proximity-gaps or otherwise. Include Thorner–Zaman (PNT in APs), and the ABF26 / KKH26 / GG25 citation neighborhoods. Flag the newest relevant exponent.`},
  {id:'D8-2power', t:`2-POWER / CYCLOTOMIC SPECIAL STRUCTURE. Stickelberger's theorem; Gross–Koblitz; the 2-adic valuation / congruences of Gauss sums for 2-POWER-ORDER characters; explicit evaluations of Gauss/Jacobi sums of order 2^k; cyclotomic units of 2-power conductor; the special algebraic structure (real subfield, ±1 root structure) of order-2^k subgroups. Does the 2-power structure give a SPECIAL-CASE sup-norm bound (e.g. via the tower F_p ⊃ μ_2 ⊃ μ_4 ⊃ …) stronger than generic BGK? Any "subgroups of 2-power order have smaller character sums" result?`},
  {id:'D9-conditional', t:`CONDITIONAL BOUNDS under standard conjectures. Under GRH / GRC (Generalized Riemann/Ramanujan), Lindelöf, the Paley Graph Conjecture itself, Sárközy-type, or a Vinogradov-mean-value input: what exponent for max_{a≠0}|Σ_{x∈H}e_p(ax)|, |H|~p^{1/5}, is provable? Does GRH give exponent 1/2 for SUBGROUP sums (vs the classical Montgomery–Vaughan √p·log p for INTERVALS)? Any conditional Ramanujan-ness of generalized Paley graphs? Search "subgroup character sum GRH", "conditional bound multiplicative subgroup exponential sum".`},
  {id:'D10-hypercontractive', t:`HYPERCONTRACTIVITY / CONCENTRATION over F_p / Z_p. Bonami–Beckner hypercontractive inequality applied to functions on Z_p or F_p; Bourgain's Λ(p)-set / concentration work; the (2,q)-norm of degree-1 functions; Keevash–Lifshitz–Long–Minzer "hypercontractivity for global functions"; restriction/extension estimates over F_p (Mockenhaupt–Tao). Does a FUNCTIONAL INEQUALITY (not equidistribution) bound the q-th moment of the rank-1 phase function Σ_k cos(b x_k) by its 2nd moment, giving exponent 1/2 for the sup over b?`},
  {id:'D11-decoupling', t:`DECOUPLING / RESTRICTION / VINOGRADOV in F_p. Bourgain–Demeter decoupling; the finite-field Vinogradov mean value; Bourgain–Garaev; sum-product–based exponential sum bounds; the Burgess method and its modern refinements for subgroups. Any decoupling/mean-value route to the SUP-NORM of a subgroup sum at exponent 1/2, or to the deep moments E_k(H)?`},
  {id:'D12-codingmotivated', t:`STARK / FRI / PROXIMITY-GAP-MOTIVATED literature for EXPLICIT Reed–Solomon list-decoding & the analytic input. ABF26 (ePrint 2026/680), KKH26 (2026/782), Jo26 (2026/891), GG25 (2025/2054), CS25, Ben-Sasson–Carmon–Ishai–Kopparty–Saraf (BCIKS proximity gaps), Ben-Sasson et al FRI. Has anyone — in the coding/STARK literature — proven the explicit-μ_n subgroup-sum / smooth-RS list-decoding-to-capacity input that the prize reduces to, even conditionally or for 2-power evaluation domains? The newest proximity-gap papers' analytic lemmas.`},
  {id:'D13-largesieve', t:`LARGE SIEVE / MOMENT METHODS for the WORST-CASE-over-b gap. The large sieve inequality for the sup over b; high-moment / amplification methods that upgrade "almost all b" (easy, √n) to "all b" (the wall); Gallagher's large sieve; the dispersion method; Bombieri–Vinogradov-style averaging. Is there a moment/large-sieve technique that controls the WORST b (not just the average) for subgroup sums at exponent 1/2, or that quantifies how many b can be "bad" (large)?`},
]

const DIR = 'ArkLib/Data/CodingTheory/ProximityGap'

phase('Sweep')
const sweep = (await parallel(DOMAINS.map(d => () => agent(
  `${FRAME}

DOMAIN ${d.id}. ${d.t}
Do 4–8 WebSearch/WebFetch queries. Return up to 6 of the MOST RELEVANT leads (verified citations only;
mark UNVERIFIED ones honestly). For each: exact claim, regime of validity, and your prizeVerdict
(does it help in the prize regime n~p^{1/5.3}, 2-power, worst-case b?). Be skeptical: most results give
exponent ≈1 or need |H|>p^{1/4}; say so. In notFound, record what you looked for and did not find.`,
  {label:`sweep:${d.id}`, phase:'Sweep', agentType:'general-purpose', schema:SWEEP_SCHEMA}
)))).filter(Boolean)

// Flatten + dedup leads across domains; rank by prize-promise.
const rankV = {BEATS_BGK:0, IMPROVES_EXPONENT:1, CONDITIONAL:2, MATCHES_BGK:3, VANISHES_AT_PRIZE:4, IRRELEVANT:5, UNVERIFIED:6}
const allLeads = sweep.flatMap(s => (s.leads||[]).map(l => ({...l, domain:s.domain})))
const seen = new Map()
for (const l of allLeads) {
  const key = (l.cite || l.title || '').toLowerCase().replace(/[^a-z0-9]/g,'').slice(0,44)
  if (!key) continue
  const prev = seen.get(key)
  if (!prev || (rankV[l.prizeVerdict] ?? 9) < (rankV[prev.prizeVerdict] ?? 9)) seen.set(key, l)
}
const ranked = [...seen.values()].sort((a,b)=>(rankV[a.prizeVerdict]??9)-(rankV[b.prizeVerdict]??9))
const top = ranked.slice(0, 22)
log(`Sweep: ${allLeads.length} raw leads → ${seen.size} distinct → deep-reading top ${top.length}. ` +
    `Promising (BEATS/IMPROVES/CONDITIONAL): ${ranked.filter(l=>(rankV[l.prizeVerdict]??9)<=2).length}`)

// Deep-read each distinct lead, then adversarially prize-check.
// WAVE-BATCHED (waves of 4) — a full 22-wide fan-out trips the server's burst throttle (memory:
// "server throttle kills 50-way fan-out"). Each lead's read→check chain runs sequentially, so peak
// concurrency is the wave size. Inner prompts kept byte-identical so completed agents still cache-hit.
function chunk(a,n){const o=[];for(let k=0;k<a.length;k+=n)o.push(a.slice(k,k+n));return o}
const readCheck = ({l, i}) => (async () => {
  const dr = await agent(
    `${FRAME}

DEEP-READ this lead (#${i}): "${l.title}" — ${l.cite} (${l.authors||'?'}). Domain ${l.domain}.
Claim as swept: ${l.claim}. Regime as swept: ${l.regime}.
WebFetch the actual paper (arXiv abstract+intro, or the relevant theorem). CONFIRM it exists (verified:true/false).
Extract the EXACT theorem statement (the precise sup-norm/energy/eigenvalue inequality + its hypotheses),
the REGIME OF VALIDITY (the |H| vs p threshold, the worst-case-vs-average, any condition), what it is
CONDITIONAL ON if anything, and whether/how it specializes to the prize (n~p^{1/5.3}, 2-power H, worst-case b).`,
    {label:`read:${i}`, phase:'DeepRead', agentType:'general-purpose', schema:DEEPREAD_SCHEMA})
  if (dr == null) return null
  return await agent(
    `${FRAME}

ADVERSARIALLY PRIZE-CHECK lead #${i}: "${l.title}" — ${l.cite}.
Deep-read found: verified=${dr.verified}; statement="${(dr.exactStatement||'').slice(0,600)}"; regime="${(dr.regimeOfValidity||'').slice(0,300)}"; conditionalOn="${dr.conditionalOn||'none'}"; appliesAtPrize="${(dr.appliesAtPrize||'').slice(0,300)}".
Judge HARD and HONESTLY: at the EXACT prize parameters (n=2^30, p≈2^158 so n≈p^{0.19} BELOW p^{1/4}, 2-power H,
WORST-CASE b, depth k≈ln p≈110): what EXPONENT does this give for M? Does it BEAT the BGK exponent ≈1 / move
toward 1/2? Or does it VANISH (like di Benedetto below p^{1/4}) / only handle the AVERAGE b / REDUCE to the same
sub-Gaussian-at-deep-r wall / require a regime the prize doesn't satisfy? If it's a REAL conditional path
(exponent 1/2 under a named hypothesis genuinely weaker-or-equal to the prize and not circular), say so and give
howToUse. If unverified, UNVERIFIED_DROP. Be the skeptic: the default prior is "reduces to the wall" — overturn it
only with a concrete exponent argument at the prize parameters.`,
    {label:`check:${i}`, phase:'PrizeCheck', agentType:'general-purpose', effort:'high', schema:CHECK_SCHEMA})
})
let checked = []
for (const w of chunk(top.map((l, i) => ({l, i})), 4)) {
  const part = await parallel(w.map(readCheck))
  checked = checked.concat((part||[]).filter(Boolean))
  log(`PrizeCheck progress: ${checked.length} leads checked (of ${top.length})`)
}

phase('Synthesize')
const realPaths = checked.filter(c => c.verdict==='REAL_CONDITIONAL_PATH' || c.verdict==='REAL_EXPONENT_GAIN')
const compact = checked.map(c => ({cite:c.cite, verdict:c.verdict, exp:c.exponentAtPrize, cond:c.conditionalOn, actionable:c.actionable, how:(c.howToUse||'').slice(0,200), why:(c.summary||'').slice(0,200)}))
const notFound = sweep.map(s => `${s.domain}: ${(s.notFound||'').slice(0,200)}`)
const synth = await agent(
  `${FRAME}

You are the SYNTHESIS + COMPLETENESS CRITIC. Here are the adversarially prize-checked leads (${checked.length}):
${JSON.stringify(compact, null, 1).slice(0, 9000)}

"Not found" notes per domain:
${JSON.stringify(notFound, null, 1).slice(0, 3000)}

Produce the LITERATURE LEDGER:
1. VERDICT: is there ANY real result (verified citation) that gives exponent 1/2 — or any genuine improvement of
   the exponent toward 1/2 — for M at the prize parameters, even CONDITIONALLY? List each such path with its exact
   citation, the exponent it gives, and the condition. If there are NONE, say so plainly and state the current SOTA
   exponent at n~p^{1/5.3} with its citation.
2. The SHARPEST conditional lever (if any): the single most promising verified result/conjecture, what it would
   need, and whether that need is genuinely weaker than (or equal to / circular with) the prize itself.
3. COMPLETENESS CRITIC: what literature domain / author / recent paper did we likely MISS that could hold the
   answer? Name concrete next searches.
4. HONEST bottom line: does the literature currently contain a route (even partial/conditional) to the prize in
   this regime, or does every verified result reduce to the BGK/Paley/sub-Gaussian-at-deep-r wall? No false hope;
   no false despair.`,
  {label:'synthesize', phase:'Synthesize', effort:'high'})

log(`lit-search-walls done: ${checked.length} leads checked, ${realPaths.length} flagged as REAL paths`)
return {
  realPathCount: realPaths.length,
  realPaths: realPaths.map(c=>({cite:c.cite, verdict:c.verdict, exp:c.exponentAtPrize, cond:c.conditionalOn, how:c.howToUse})),
  ledger: synth,
  allChecked: compact,
}
