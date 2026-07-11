export const meta = {
  name: 'prize-407-full-pool-assault',
  description: '#407: full sub-agent pool — attack EVERY open path from every angle; adversarially verify; hunt cross-path closure',
  phases: [
    { title: 'Assault', detail: 'one agent per open path x angle, genuine close-or-bound attempt' },
    { title: 'Verify', detail: 'adversarial skeptics refute any non-wall claim' },
    { title: 'Synthesize', detail: 'cross-path closure hunt + definitive map' },
  ],
}

const CONTEXT = [
  '# 407 Proximity Prize delta* — FULL-POOL ASSAULT on every open path (user-directed, exhaustive)',
  '',
  '## REGIME (CORRECTED — do NOT use the wrong wall)',
  'n=2^mu dyadic FFT subgroup mu_n in F_q*, mu up to 40. eps*=2^-128, q ~ n*2^128 prime, q=1 mod n.',
  'CRITICAL (issue comment 4700736246): the index m=(q-1)/n ~ 2^128 is held CONSTANT as n grows.',
  'So mu_n is POSITIVE-PROPORTION (n=Theta(q), n >> sqrt(q)), NOT a thin n=q^delta subgroup. The',
  'derived beta=1+128/log2(n) is n-dependent, not a fixed thin exponent. => the load-bearing wall is',
  'EFFECTIVE FIXED-INDEX GAUSS-SUM EQUIDISTRIBUTION, geometrically distinct from additive-comb BGK/Paley',
  '(thin subgroups). Do NOT spend effort on thin-BGK; it is the wrong regime.',
  '',
  '## THE EXACT OBJECT',
  'eta_b = (1/m)[ -1 + sum_{j=1}^{m-1} psi(b)^{-j} tau(psi^j) ], m=(q-1)/n, psi a mult char of order m.',
  'M(n,q)=max_{b!=0}|eta_b| ~ (sqrt(q)/m)*max_{w^m=1} |sum_{j} w^{-j} a_j|, a_j=tau(psi^j)/sqrt(q) UNIMODULAR.',
  'PRIZE BOUND: M <= C*sqrt(n*log(q/n)) <=> the unimodular Gauss-phase sequence (a_j) has DFT sup-norm',
  '<= C*sqrt(m*log m) over the m-th roots of unity — i.e. the phases (a_j) are FLAT / random-like.',
  'delta* = 1 - rho - H(rho)/(beta*log2 n), rho=k/n in {1/2,1/4,1/8,1/16}.',
  'NEW measured law: R(n,m)=M/sqrt(n*ln m) is FLAT in [1.1,1.5] (no trend) — log(q/n) is the EXACT',
  'normalization and worst-case constant C ~ 1.5.',
  '',
  '## EQUIVALENT FRAMINGS (all proven-equivalent or dual; the SAME residual)',
  '(1) analytic: Gauss-phase DFT flatness max_w|sum_j w^{-j} a_j| <= C*sqrt(m log m).',
  '(2) cumulant: kappa_r := (sum_i|eta_i|^{2r}/m)/((2r-1)!!*n^r) <= 1 at depth r ~ ln m. PROVEN r=1,2,3;',
  '    MEASURED kappa@r* ~ 0.01-0.03 << 1 to n=128. Floor M^{2r} <= n*sum_i|eta_i|^{2r}.',
  '(3) additive energy / p-defects: E_r^{F_q}(mu_n) - E_r^C <= n^{2r}/q (sparse <=2r-term root-of-unity',
  '    differences do not vanish mod the fully-split prime q-ideal in Z[zeta_{2^mu}] beyond baseline).',
  '(4) ideal-SVP: #{0!=alpha in q-ideal: house(alpha)<=2r} <= baseline; q-ideal fully-split deg-1, N=q.',
  '(5) NVM/R3: nonvanishing-minors of the compressed Fourier matrix of mu_n = repeated-degree generalized-',
  '    Vandermonde nonsingularity (LovettPrimitiveStep, GM-MDS) — characterized via Gauss sums/Chebotarev',
  '    (arXiv:2310.09992); index 2,3 solved, larger index OPEN.',
  '(6) coding: variety = weight-a {0,1}-codewords of RS[n,n-t+1] (zeros g^1..g^{t-1}) = sparse-sparse DFT',
  '    (Fourier uncertainty for Z/2^mu). lacBad = bounded-coeff subset-sum of t-th-power subgroup.',
  '(7) cross-parity: 96-100% of F_q-defects satisfy A = -g*B mod q (a sum-product/bilinear resonance).',
  '',
  '## PROVEN (axiom-clean/rigorous) — BUILD ON, do NOT re-derive',
  '- char-0 E_r^C(mu_n)=(2r-1)!!*n^r (Lam-Leung/Wick). kappa proven r=1,2,3 (Var=n, E2=3n^2-3n,',
  '  E3=15n^3-45n^2+40n). Newton: e_t = +-p_t/t under e_1..e_{t-1}=0.',
  '- norm regime: q > a^{n/2} (a=k+t0) => NO defects => delta*=prizeDeltaStar PROVEN. Holds n<=64, FAILS n>=128.',
  '- kappa_r = kA_r + kD_r split: kA_r (archimedean/char-0) UNCONDITIONALLY clean at prize scale (deviates',
  '  only at r_half=Theta(sqrt n)=2^20 >> ln m ~ 128); ENTIRE residual is mod-q defect kD_r.',
  '- well-roundedness (Fukshansky-Petersen): q-ideal well-rounded, lambda_1=...=lambda_{n/2}; PINS box count',
  '  two-sided at Theta((4r)^N/q) (NO-GO amplifier). lambda_1 >= sqrt(n/2) proven.',
  '- dyadic sqrt2 house floor: balanced sparse +-sum of 2^mu-roots has house>=sqrt2, none in (1,sqrt2).',
  '- delta* n-INDEPENDENT (= binding sub-level s*=2log2(q*eps*)/H(rho) ~ 64-256). coset reduction proven.',
  '- Lam-Leung tower: e_1..e_{t-1}=0 <=> prod(X-x) in F[X^t] <=> S=mu_t-coset-union (<= easy proven;',
  '  => open for t=2^j>4, the rigidity).',
  '',
  '## WALLS PROVEN (each technique exact stall — do not repeat without a NEW idea)',
  '- effective-Katz/Wasserstein (2505.22059): discrepancy ~ conductor*q^{-1/2}; need conductor<sqrt(n/m)',
  '  =2^-48<1 at prize => IMPOSSIBLE as posed.',
  '- moment/Betti: deep moments cap at r=2 (Adolphson-Sperber Betti ~ n^{2r} = ambient => Weil buys nothing',
  '  r>=3; Fermat-curve Hasse-Weil only r=2).',
  '- BGK/additive-comb: n^{1-nu}, nu->0 (WRONG regime, thin).',
  '- large-sieve avg-over-q: covering depth r <~ (1/2)log_n Q, strictly WEAKER than per-q norm; finite-phi',
  '  artifact (Q^{1/phi}->1 at phi=2^31).',
  '- well-rounded GoN: two-sided pin, no loose-upper rescue.',
  '- NVM (2310.09992): index 2,3 only; large index open.',
  '',
  '## ON-DISK PAPERS (~/papers/arklib/): 2505.22059, 2207.12439 (Rojas-Leon Gauss-sum independence),',
  '2310.09992 (NVM/uncertainty for subgroups), 1712.00761 (improved Gauss-sum bounds), 2302.13670',
  '(ultra-short trace sums), 2112.13886 (Garcia-Lorenz-Todd), 1611.07287 (Habegger), 2004.10278 (Pan-Xu),',
  'Cheng et al JNT2022, 1101.4442 (Fukshansky-Petersen).',
  '',
  '## HONESTY CONTRACT (OVERRIDING): NEVER claim proven what is not. No fabricated/silently-discharged',
  'bound presented as a theorem. A partial bound states EXACTLY its regime + what is assumed. The prize is',
  'a recognized open problem; goal = exhaustive correct analysis + any GENUINELY-NEW verified bound (even',
  'partial/conditional), NOT a fabricated closure. A real partial result or precise new obstruction is a',
  'SUCCESS; a fabricated closure is the one forbidden failure. The word "proven" is sacred.',
].join('\n')

const VECTORS = [
  { key: 'gauss-phase-flatness-algebra', prompt: 'THE CORRECTLY-FRAMED CORE. Attack the Gauss-phase DFT flatness DIRECTLY via the explicit algebra of the unimodular sequence a_j=tau(psi^j)/sqrt(q). Use Hasse-Davenport relations, Gauss-sum multiplication / Jacobi-sum factorization tau(psi^i)tau(psi^j)=J(psi^i,psi^j)tau(psi^{i+j}), and the Galois/Frobenius action (a_{cj}) to find STRUCTURE in (a_j) forcing its m-DFT sup-norm <= C*sqrt(m log m). Is there an exact functional equation / self-duality of (a_j) under the m-DFT (a Gauss-sum-of-Gauss-sums) bounding the sup-norm? Try to PROVE flatness or find the precise algebraic obstruction. Go deep — this is the live target.' },
  { key: 'rojas-leon-effective', prompt: 'Rojas-Leon (2207.12439) PROVES the Gauss-sum family {tau(psi^j)} is independent/equidistributed (only relations: conjugation/Galois/Hasse-Davenport). Can this QUALITATIVE independence be upgraded to an EFFECTIVE bound on the m-DFT sup-norm of (a_j) at the SPECIFIC prize p~2^160, m=2^128? The prize needs <=1/m-quality non-alignment. Does maximal monodromy => square-root cancellation for the DFT (a sum over the family) => sqrt(m log m)? Assess if "maximal monodromy => DFT flat" can be made effective, or if effectivity is exactly the gap.' },
  { key: 'nvm-dyadic-tower', prompt: 'R3 = analytic wall via NVM (2310.09992): repeated-degree generalized-Vandermonde nonsingularity (LovettPrimitiveStep/GM-MDS residual) characterized by Gauss sums (Chebotarev on roots of unity); index 2,3 solved, larger OPEN. EXPLOIT THE DYADIC STRUCTURE: index m=2^128 is a pure power of 2, mu_n in a TOWER. Can a recursive/tower Chebotarev argument (descend index 2^k -> 2^{k-1}) crack the NVM property for power-of-2 index where general large-index is open? Lam-Leung char-p vanishing is sharpest for prime-power order. Try to PROVE NVM for index 2^k by induction, or find why tower descent fails.' },
  { key: 'cumulant-deep-nonbetti', prompt: 'The cumulant kappa_r<=1 to depth r~ln m is the unified residual (proven r=1,2,3; moment/Betti caps at r=2). Find a NON-Betti route to deep cumulants: (a) cross-parity recursion A=-gB as a self-improving descent on kappa_r; (b) hypercontractivity/log-Sobolev on the Gauss-phase sequence; (c) tower mu_n superset mu_{n/2} as a martingale, bound increments; (d) SOS/positive-definiteness: kappa_r as a sum of squares <= (2r-1)!!n^r. Try to PROVE kappa_r<=1+o(1) to depth ln m bypassing Betti blow-up.' },
  { key: 'cumulant-from-flatness', prompt: 'Connect framings (1),(2): kappa_r = the 2r-th moment of the m-DFT of (a_j). PROVE rigorously DFT-flatness <=> kappa_r<=C for r~ln m and identify which direction is the content. Then attack the moment side: is sum_w|sum_j w^{-j}a_j|^{2r}/m <= (2r-1)!! m^r provable from the Gauss-sum orthogonality / autocorrelation sum_j a_j conj(a_{j+h}) (itself a Gauss/Jacobi sum)? Compute the autocorrelation exactly and see if it gives the moment bound.' },
  { key: 'ideal-svp-split-newangle', prompt: 'The fully-split cyclotomic ideal-SVP count #{0!=alpha in q-ideal: house<=2r} (Pan-Xu exclude split N=q). NEW angle BEYOND norm-bound + well-roundedness (both exhausted): (a) the DUAL lattice and a transference exploiting that alpha is SPARSE (<=2r-term) — the support sparsity GoN ignores; (b) CVP/BDD formulation; (c) the explicit basis (q, g-zeta) Gram structure; (d) theta-series/modularity counting. Can ANY bound the SPARSE-support sub-count (not full box) below baseline? Be rigorous about sparse-support vs full-box.' },
  { key: 'sumproduct-positive-proportion', prompt: 'CRITICAL: mu_n is POSITIVE-PROPORTION (n>>sqrt q), NOT thin — so the RIGHT regime is LARGE subgroups, with DIFFERENT (possibly stronger) bounds than thin-BGK. Derive the best sum-product/additive-energy/character bound for subgroups of size n>>sqrt q in F_q (Weil for multiplicative energy, Stepanov for large subgroups, Garcia-Voloch). Does the large-subgroup regime give E(mu_n) or the cross-parity count A=-gB better than thin n^{1-nu}? Could n>>sqrt q make a multiplicative-energy bound NON-trivial enough to close kD_r? This regime correction may be the key.' },
  { key: 'avg-over-q-largesieve', prompt: 'Prize is for an EXPLICIT code => "pick a good q". Excess C(n,k+t)/q^{t-1} is SUPPRESSED (log2 ~ -10^9) for typical q at the window-edge. Make AVERAGE-over-q rigorous: PROVE that for almost-all primes q=1 mod n in [Q,2Q] (Q~2^160) the window-edge defect count <= baseline (=> a good explicit q exists). Prior large-sieve walled on heavy first-moment tail (finite-phi). NEW: second moment over q with SPARSE structure, or a large-sieve for cyclotomic-prime-ideal divisibility sum_q|sum_alpha ...|^2, or restrict q to a smooth/structured family. Can almost-all-q be proven even if worst-case-q cannot?' },
  { key: 'fourier-uncertainty-dyadic', prompt: 'Framing (6): variety = weight-a {0,1}-codewords of RS[n,n-t+1] with t-1 CONSECUTIVE zero frequencies = sparse-time sparse-frequency on Z/2^mu. For Z/p^k there are SHARPER uncertainty principles than Donoho-Stark (support must be subgroup-structured). PROVE: a {0,1} vector of weight a with t-1 consecutive vanishing DFT coeffs must be mu_t-coset-supported (the dyadic-tower => rigidity) via the Z/2^mu uncertainty principle / structure of consecutive vanishing Fourier coeffs (Turan-type / Amrein-Berthier / Tao for Z/p). This would close the char-0 count. Try the => rigidity for t=2^j via uncertainty.' },
  { key: 'effective-katz-circumvent', prompt: 'Effective-Katz (2505.22059) walls: discrepancy~conductor*q^{-1/2} needs conductor<2^-48. CIRCUMVENT: the conductor barrier is for a SINGLE sum equidistribution. The prize needs only the SUP over m=2^128 phases to avoid alignment — a union-bound/extreme-value statement, not single-sum equidistribution. Is there a sheaf on the m-torus whose trace function is the m-DFT and whose conductor is poly(m) not exp, giving the sup-norm via moments-of-the-family (integral |sum w^{-j}a_j|^{2r} dw) without the per-sum barrier? Assess this moments-of-the-family route vs the per-sum barrier.' },
  { key: 'gauss-sum-explicit-1712', prompt: 'Use improved Gauss-sum bounds (1712.00761) and ultra-short trace sums (2302.13670) for the INCOMPLETE sum sup-norm in the FIXED-INDEX positive-proportion regime (n>>sqrt q). Extract the exact theorems, specialize to n=Theta(q) and dyadic mu_n, check non-vacuous at prize scale, and report the best bound on |sum_{x in mu_n} psi(bx)|. Does it beat trivial n / Weil sqrt(q), and how close to sqrt(n log(q/n))? If non-vacuous it is a genuine partial result toward M.' },
  { key: 'lovett-primitivestep-direct', prompt: 'Attack LovettPrimitiveStep (SOLE residual of R3/GM-MDS in-tree) DIRECTLY: the merge-branch substitution / repeated-degree generalized-Vandermonde determinant != 0 for dyadic mu_n. By NVM<->Gauss-sum it is a specific Gauss-sum non-vanishing (Chebotarev). For dyadic, the determinant is a product/resultant of cyclotomic-structured terms. Show !=0 via the 2-adic valuation (determinant 2-adic valuation controlled, !=0 mod the prime above 2) or an explicit Lam-Leung argument. Try to discharge LovettPrimitiveStep for n=2^mu.' },
  { key: 'dense-cayley-spectral', prompt: 'DIFFERENT DOMAIN: Cay(F_q, mu_n) has M = its non-trivial eigenvalue. For n=Theta(q) this is a DENSE Cayley graph (Alon-Boppana is for sparse). For dense abelian Cayley graphs the eigenvalues are the character sums; is there a representation-theoretic / SDP (Lovasz theta) / Krein bound for the SUP eigenvalue of a DENSE Cayley graph that the sparse-graph literature misses, pinning M<=C*sqrt(n log(q/n))? Explore the dense-regime spectral angle and whether quasirandomness (Chung-Graham-Wilson) of the generalized Paley graph at positive proportion forces the eigenvalue bound.' },
  { key: 'combine-norm-belowbinding', prompt: 'MOST LIKELY GENUINE WIN — verify carefully. The norm-regime closure (q>a^{n/2}) PROVES delta*=prizeDeltaStar for n<=64 and FAILS n>=128, BUT delta* is n-INDEPENDENT (= the binding sub-level s*=2log2(q*eps*)/H(rho)). For rho=1/2 the binding level is s*~64, which IS norm-OK at prize n=2^40 (proven ladder side). QUESTION: does n-independence + the binding-level reduction mean the PROVEN n<=64 norm closure at the binding level TRANSFERS to the prize n=2^40, closing rho=1/2 (or more rates) UNCONDITIONALLY? Check rigorously: (i) is the binding level s* <= 64 for any prize rate? (ii) does a proven small-n closure at the binding level imply delta* at large n (is the n-independence reduction itself proven, or conjectural)? This may be an ALREADY-PROVEN closure for some rate hiding in the n-independence. Be rigorous about whether the n-independence is proven or assumed — that is the crux.' },
]

const VERDICT = {
  type: 'object',
  required: ['vector','verdict','precise_statement','status','key_obstruction','novelty_1to10'],
  properties: {
    vector: { type: 'string' },
    verdict: { type: 'string', enum: ['CLOSES_prize_regime','PARTIAL_new_bound','reconfirms_wall','vacuous_in_regime','already_proven_transfer'] },
    precise_statement: { type: 'string' },
    status: { type: 'string', enum: ['rigorously_proven','conjecture_with_evidence','heuristic_only','refuted'] },
    key_obstruction: { type: 'string' },
    cross_path_lever: { type: 'string' },
    novelty_1to10: { type: 'number' },
  },
}
const VERIFY = {
  type: 'object',
  required: ['vector','holds_up','refutation_or_confirmation','corrected_verdict'],
  properties: {
    vector: { type: 'string' },
    holds_up: { type: 'boolean' },
    refutation_or_confirmation: { type: 'string' },
    corrected_verdict: { type: 'string', enum: ['CLOSES_prize_regime','PARTIAL_new_bound','reconfirms_wall','vacuous_in_regime','already_proven_transfer'] },
  },
}

phase('Assault')
const attacks = (await parallel(VECTORS.map(v => () =>
  agent(CONTEXT + '\n\n## YOUR ASSIGNED PATH/ANGLE: ' + v.key + '\n' + v.prompt +
    '\n\nWork as a rigorous research mathematician. Go deep on the actual math (the on-disk papers, explicit Gauss-sum/cyclotomic algebra, real theorems). Genuinely try to CLOSE or partially-bound; if you reach a real new bound give the exact statement + proof sketch + regime. If you wall, locate the obstruction precisely and note any partial lever that could combine with another path (cross_path_lever). Honesty contract applies. Return the structured verdict.',
    { schema: VERDICT, label: v.key, phase: 'Assault' })
))).filter(Boolean)

phase('Verify')
const claims = attacks.filter(a => a.verdict === 'CLOSES_prize_regime' || a.verdict === 'PARTIAL_new_bound' || a.verdict === 'already_proven_transfer')
const verifyThunks = []
for (const a of claims) {
  for (const idx of [0, 1]) {
    verifyThunks.push(() =>
      agent(CONTEXT + '\n\n## ADVERSARIAL VERIFICATION (skeptic ' + (idx + 1) + ')\nAn assault on path "' + a.vector + '" claims:\nVERDICT: ' + a.verdict + '\nSTATEMENT: ' + a.precise_statement + '\nSTATUS: ' + a.status +
        '\n\nYou are a hostile referee. Set the "vector" field to "' + a.vector + '". Try HARD to REFUTE: does it (i) hide an unproven assumption, (ii) reduce to the recognized open wall, (iii) make an arithmetic/regime error, (iv) only hold on-average/special-q, (v) misread a cited theorem? A genuine closure would be extraordinary — demand extraordinary rigor, default to downgrading anything not airtight. For already_proven_transfer, check the transfer step (n-independence does NOT automatically transfer small-n proofs). Return the structured verdict.',
        { schema: VERIFY, label: 'verify:' + a.vector + ':' + idx, phase: 'Verify' }))
  }
}
const verifs = (await parallel(verifyThunks)).filter(Boolean)

phase('Synthesize')
const survivors = claims.filter(a => {
  const vs = verifs.filter(v => v.vector === a.vector)
  return vs.length > 0 && vs.every(v => v.holds_up)
})
const synthesis = await agent(CONTEXT +
  '\n\n## SYNTHESIS + CROSS-PATH CLOSURE HUNT\nAll path attacks (JSON):\n' + JSON.stringify(attacks, null, 1) +
  '\n\nAdversarial verifications (JSON):\n' + JSON.stringify(verifs, null, 1) +
  '\n\nClaims that SURVIVED both skeptics:\n' + JSON.stringify(survivors, null, 1) +
  '\n\nProduce the DEFINITIVE report: (A) does ANY survivor close the prize regime n=2^40, airtight? (B) CROSS-PATH HUNT — examine pairs/combinations of the cross_path_lever fields: can two partials COMBINE into a closure or strictly stronger bound? Try concrete combinations. (C) strongest VERIFIED bound now + exact regime; (D) per-path one-liner (verdict+obstruction); (E) the single sharpest remaining open statement + most promising next attack. Honesty: report ONLY what survived verification; do not upgrade a downgraded claim. If nothing closes, say so plainly with the exhaustive honest map.',
  { label: 'synthesize', phase: 'Synthesize' })

return { attacks, verifs, survivors, synthesis }
