export const meta = {
  name: 'deltastar-cycle7-newdirections',
  description: 'Cycle 7: genuinely NEW non-additive directions (Delsarte LP, Chebyshev-Markov profile, VC/Sauer-Shelah, containers, wildcard) — each must NOT reduce to the known-hard walls; prove a delta* result OR prove the reduction-to-wall (refutation)',
  phases: [
    { title: 'Attack' },
    { title: 'Verify' },
  ],
}

const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

const AVOID = `
THE AVOID-LIST (the prize has been reduced to ALL of these; a direction that reduces to any of them is a DEAD END — if your direction reduces to one, your job becomes PROVING that reduction precisely, as a refutation of the direction):
  (W1) BCHKS Conjecture 1.12 — r-fold subgroup sumset / additive-energy growth / anti-concentration of mu_n mod p.
  (W2) Deep-moment validity: E_r(mu_n) ~ char-0 value for r ~ log q == square-root cancellation among Gauss-sum phases == BGK/MRSS/Weil (25-year open).
  (W3) Stepanov for the deep moment; Konyagin-Shkredov subgroup energy; Untrau value distribution.
  (W4) Thorner-Zaman PNT in arithmetic progressions (KKH26 s=128).
  (W5) Joint additive energy E_{1,2}(mu_n) / e1-support (absent from literature).
  (W6) The ENTIRE additive-moment hierarchy of mu_n: PROVEN insufficient (list <= sqrt(n*E), E>=n^2 always => short by n^{1/2}; higher moments fail F_p transport by pigeonhole).
  (W7) Guruswami-Sudan / Hasse multiplicity for PLAIN RS: PROVEN capped at the Johnson radius (m->infinity approaches but never exceeds it).
  (W8) Folded / random RS capacity results (Goyal-Guruswami 2025/2054): only for FOLDED codes, NOT the prize's plain smooth-domain RS.
  (W9) Interleaving-width blowup: every known correlated-agreement bound is only POLYNOMIAL in the interleaving width (union/linear factor).
A direction "COUNTS as new" only if it is (a) NOT already a file in ArkLib/Data/CodingTheory/ProximityGap/ (grep first), (b) NOT in DISPROOF_LOG.md, and (c) provably NOT a re-encoding of W1-W9. You MUST aggressively self-check (c): most plausible directions secretly reduce to a wall. If yours does, that reduction IS your deliverable (a clean refutation).
`

const COMMON = `
You are a Fable-tier formal-math researcher on the Ethereum Proximity Prize (GitHub lalalune/ArkLib issue #389): pin delta* (the mutual correlated agreement / MCA list-decoding threshold) for explicit smooth-domain (2-power NTT) Reed-Solomon codes. Prize window (1-sqrt(rho), 1-rho-Theta(1/log n)), eps*=2^-128, rho=k/n, n=2^m, q=p prime ~ n*2^128. The floor needs: worst-case far-line list <= q*eps* = n at the window radius (q-INDEPENDENT counting).

REPO: ${REPO}  (SHARED git tree with sibling agents).

BUILD RULES (violating these clogs a 16-core shared box):
- Iterate LOCK-FREE: scripts/pg-iterate.sh <file>  (= lake env lean + error filter + axiom audit). NEVER 'lake build', NEVER 'git push'. Orchestrator lands files.
- Scratch Lean file in ArkLib/Data/CodingTheory/ProximityGap/Frontier/ named '_wf7_<unique>.lean' (gitignored). Minimal imports.
- Python probes (for numerical evidence) go in scripts/probes/ named 'probe_wf7_<unique>.py'.

HONESTY CONTRACT (non-negotiable):
- NO sorry/admit/native_decide/fabricated axiom. #print axioms must show ONLY [propext, Classical.choice, Quot.sound].
- A FALSE statement gets a machine-checked countermodel, then stays documented-refuted. Do NOT "prove" a false thing.
- The open core may stay an EXPLICIT named Prop/hypothesis. Do NOT fabricate a closure.
- autoImplicit caveat: lake env lean runs autoImplicit=TRUE, real build is FALSE. Declare EVERY binder explicitly.
- A NUMERICAL probe must MATCH before you trust a formula; small-prime list probes are POLLUTED (use a LARGE prime p>=12289 for any list/agreement computation, per the in-tree char-0 discipline).

SUBSTRATE to build on (grep by theorem name; files get renamed):
- moment_identity_base / the agreement-profile binomial-moment identity: for any word w and the RS code of dim k, the agreement profile {a_c = #agree(c,w) : c in C} satisfies sum_c C(a_c, j) = C(n,j)*q^{k-j} for all j <= k (FIXED, w-independent). grep 'moment_identity'.
- Johnson bound: JohnsonListBound.lean (the order-2 / second-moment case).
- DeltaStarBracket.lean (deltaStar_bracket), HalfJohnsonDeltaStar.lean, MCAThresholdLedger.lean (mcaDeltaStar, le_mcaDeltaStar_of_good, mcaDeltaStar_le_of_bad), DISPROOF_LOG.md.

Your final message IS the structured return value. Return ONLY the requested fields.
${AVOID}
`

const ATTACK_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['target', 'verdict', 'reducesToWall', 'reach', 'file', 'probe', 'theorems', 'axiomClean', 'summary', 'keyFinding'],
  properties: {
    target: { type: 'string' },
    verdict: { type: 'string', enum: ['NEW_LIVE', 'NEW_PARTIAL', 'REDUCES_TO_WALL', 'REFUTED', 'PROVEN_PIN', 'FAILED'], description: 'PROVEN_PIN=a delta* pin proven axiom-clean; NEW_LIVE=genuinely new direction with a live new sub-question NOT on the avoid-list, with progress; NEW_PARTIAL=new direction, some structural lemma proven; REDUCES_TO_WALL=direction provably re-encodes a W#; REFUTED=direction gives a bound no better than Johnson with proof; FAILED=no traction' },
    reducesToWall: { type: 'string', description: 'if it reduces to a wall, WHICH (W1-W9) and the precise reduction; else "none"' },
    reach: { type: 'string', description: 'how far past Johnson (1-sqrt rho) this direction provably reaches, or "<=Johnson", or "unknown"; be quantitative' },
    file: { type: 'string', description: 'absolute path to _wf7 scratch file (empty if none)' },
    probe: { type: 'string', description: 'absolute path to probe_wf7 file (empty if none)' },
    theorems: { type: 'array', items: { type: 'string' }, description: 'fully-qualified compiled axiom-clean theorem names' },
    axiomClean: { type: 'boolean' },
    summary: { type: 'string', description: 'the math, the direction, what you proved, 5-10 sentences' },
    keyFinding: { type: 'string', description: 'the single decisive takeaway: a new live sub-question (state it), a reduction-to-wall, or a refutation mechanism' },
  },
}

const VERIFY_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['target', 'compileConfirmed', 'axiomAudit', 'isGenuinelyNew', 'reductionSound', 'isFabricated', 'issues', 'recommendation'],
  properties: {
    target: { type: 'string' },
    compileConfirmed: { type: 'boolean', description: 'true iff YOU re-ran lake env lean on the file: exit 0, no errors, no sorry/sorryAx' },
    axiomAudit: { type: 'string' },
    isGenuinelyNew: { type: 'boolean', description: 'true iff the direction is NOT in the tree, NOT in DISPROOF_LOG, and does NOT secretly reduce to W1-W9 (check this hard)' },
    reductionSound: { type: 'boolean', description: 'if the agent claimed REDUCES_TO_WALL or a reach bound, is the reduction/bound mathematically correct?' },
    isFabricated: { type: 'boolean', description: 'sorry/admit/native_decide/fabricated axiom OR a circular named hypothesis OR a vacuous statement' },
    issues: { type: 'string' },
    recommendation: { type: 'string', enum: ['LAND', 'LAND_WITH_NOTE', 'REJECT'] },
  },
}

const TARGETS = [
  {
    key: 'D1-DelsarteLP',
    prompt: `${COMMON}

DIRECTION D1 — THE DELSARTE LINEAR-PROGRAMMING BOUND (MacWilliams dual), applied to the MCA bad-scalar count.

Idea: the MCA-bad event at scalar gamma <=> the combination u_0 + gamma*u_1 lies within Hamming radius delta*n of the code C <=> its syndrome lies in the weight-<= delta*n ball of the dual space F_q^{n-k}. The number of bad scalars is the incidence of an affine line (in syndrome space) with this ball. The Delsarte LP bound (a linear program over the Krawtchouk polynomial basis, dual to the code's distance distribution via MacWilliams) is the STRONGEST general bound on codes/anticodes and is NOT a character-sum/additive-energy object. The classical Johnson bound is the ORDER-2 Delsarte LP; the FULL LP (all Krawtchouk constraints up to degree k) is strictly stronger.

YOUR TASK:
1. Set up the LP precisely for THIS problem: bound max-incidence of a line (far-coset direction) against the weight-floor(delta*n) ball in F_q^{n-k}, or equivalently the list size, via the Krawtchouk/Delsarte LP with the code's MacWilliams-transformed distance distribution as constraints.
2. The DECISIVE question: does the full LP optimum at radius delta in the prize window (1-sqrt rho, 1-rho-...) give list <= n (floor budget), i.e. does the LP BEAT Johnson into the window? Compute the LP for small (n,k) with a LARGE prime (probe_wf7), comparing LP-optimum vs Johnson vs the true list. If LP > Johnson into the window: this is a LIVE NEW direction (state the LP and its reach). If LP == Johnson (the higher Krawtchouk constraints don't bind because the q-ary ball's distribution is bulk-dominated): that is a clean REFUTATION (LP route capped at Johnson) — PROVE why the constraints don't bind.
3. CRITICAL self-check: does the LP secretly need the dual code's WEIGHT DISTRIBUTION, which for RS is a character-sum / Gauss-sum object (=> reduces to W2)? If the LP's input is the MacWilliams transform that itself requires deep-moment validity, you've hit a wall — say so precisely. The LP bound is "new" ONLY if it uses just the MINIMUM DISTANCE (d=n-k+1, MDS, known) and the Krawtchouk positivity, NOT the full weight enumerator.
Deliverable: the LP setup + a probe + an axiom-clean Lean lemma capturing whatever you can (e.g. the order-j moment bound, or the reduction-to-wall), + a precise reach/refutation verdict.`,
  },
  {
    key: 'D2-ChebyMarkov',
    prompt: `${COMMON}

DIRECTION D2 — SOLVE THE CHEBYSHEV-MARKOV AGREEMENT-PROFILE EXTREMAL PROBLEM EXACTLY (a pure constrained-moment LP, no mu_n additive structure).

The framing (from the issue, never solved): for ANY word w, the agreement profile {a_c : c in C} has its first k binomial moments FIXED and w-independent: sum_c C(a_c, j) = C(n,j)*q^{k-j} for all j <= k (in-tree moment_identity_base). The floor = maximize the upper tail #{c : a_c >= t} over all REALIZABLE profiles, at t = (1-delta)*n. This is a classical Chebyshev-Markov / Markov-Krein extremal moment problem: given the first k moments of a discrete measure, find the max mass above a threshold. Its solution is ATOMIC (Gauss-Chebyshev quadrature; the extremal measure is supported on <= k+1 points).

YOUR TASK:
1. Solve the extremal moment problem EXACTLY (Markov-Krein / canonical-moments theory): given the fixed binomial moments, compute the max #{a_c >= t} as a function of (n, k, t). This is pure LP/quadrature, NOT additive.
2. DECISIVE: evaluate the extremal value at the window radius (t = (1-delta)*n, delta in (1-sqrt rho, ...)). Does it give <= n (floor holds, BEATS Johnson), or does it collapse to the Johnson value? Probe small (n,k), LARGE prime: compare the LP-extremal tail vs the actual max list over many words vs Johnson.
3. CRITICAL: the LP is a RELAXATION (an UPPER bound on the floor) — its extremal profile may NOT be realizable by a real word. Determine the gap: is the relaxation TIGHT (a matching word construction), or LOOSE (the true floor is much smaller, so the LP can't pin it)? If the high moments are bulk-dominated and the LP optimum == Johnson, PROVE it (clean refutation: the moment problem caps at Johnson). If the LP optimum is strictly below Johnson into the window AND looks realizable, this is a MAJOR live new direction.
4. Self-check vs W6: this is NOT the additive-moment hierarchy of mu_n (that's about E_r(mu_n)); it's the agreement-profile moments of the CODE. Confirm the distinction holds.
Deliverable: the solved extremal formula + probe + an axiom-clean Lean lemma (e.g. the k-th-moment tail bound #{a_c>=t} <= C(n,k)/C(t,k), which IS provable, plus the full-LP refinement if it beats Johnson) + verdict on tightness/reach.`,
  },
  {
    key: 'D3-VCdim',
    prompt: `${COMMON}

DIRECTION D3 — VC-DIMENSION / SAUER-SHELAH / HAUSSLER PACKING on RS agreement sets (a combinatorial-dimension bound on the list, no additive structure).

Idea: for a word w, each codeword c gives an agreement set A_c = { i in [n] : c_i = w_i } subset [n]. The set system {A_c : c in C} is HIGHLY structured: any k+1 coordinates determine a codeword uniquely (RS interpolation), so two distinct codewords agree on <= k-1 points, i.e. |A_c ∩ A_{c'}| <= k-1 for c != c'. The "list at radius delta" = #{c : |A_c| >= (1-delta)n}. Bound this via the combinatorial dimension of the set system: a family of sets pairwise-intersecting in <= k-1 points, each of size >= t, has bounded cardinality (Fisher-type / Frankl-Wilson / Deza-Frankl / fractional-Helly / Haussler packing). These are PURELY COMBINATORIAL (set-intersection / VC / packing) bounds, NOT character sums or additive energy.

YOUR TASK:
1. Identify the sharpest set-system bound for: a family of t-subsets of [n] with pairwise intersection <= k-1. Candidates: the Frankl-Wilson / Ray-Chaudhuri-Wilson restricted-intersection bound (a family with all pairwise intersections in a set of s values has size <= C(n,s)); Deza-Frankl sunflower-free; Haussler's packing lemma (a delta-separated family in a VC-dim-d space has size <= (C/delta)^d). Here the "dimension" is k.
2. DECISIVE: does the resulting list bound at the window radius give <= n? E.g. Ray-Chaudhuri-Wilson with intersections in {0,...,k-1} gives size <= C(n, k-1)... too big. The size->=t restriction is the key extra constraint. Work out the bound and compare to Johnson. Probe small (n,k) LARGE prime: count actual high-agreement codewords vs the combinatorial bound vs Johnson.
3. CRITICAL self-check: does the bound IMPROVE on Johnson into the window, or is it WEAKER (combinatorial bounds ignoring the field are usually weaker than Johnson)? If weaker, that's an honest dead-direction; if it reaches into the window, it is a live new direction that BYPASSES every additive wall. Either way prove your claim.
Deliverable: the chosen set-system theorem instantiated + probe + an axiom-clean Lean lemma (the pairwise-intersection bound for RS agreement sets is provable in-tree: distinct codewords of rsCode dom k agree on <= k-1 points; grep) + reach verdict.`,
  },
  {
    key: 'D4-Containers',
    prompt: `${COMMON}

DIRECTION D4 — HYPERGRAPH CONTAINER METHOD / probabilistic deletion for the high-agreement codeword count (a modern combinatorial machine, never applied here).

Idea: the floor is a q-INDEPENDENT counting statement: bound #{ codewords with agreement >= t with w }, or the number of "bad (stack, gamma) configurations". The hypergraph container method bounds the number of independent sets / sparse configurations in a structured hypergraph by a small number of "containers". Model the bad configurations as the independent sets of a suitable hypergraph (vertices = codewords or coordinates; edges = the constraint that 3 codewords cannot pairwise-agree-too-much, from the <= k-1 pairwise-intersection rigidity). Containers / the Kleitman-Winston / Balogh-Morris-Samotij framework then bound the count.

YOUR TASK:
1. Set up the hypergraph precisely (what are vertices, what are the forbidden hyperedges encoding RS rigidity), and identify which container/deletion result applies.
2. DECISIVE: does it bound the list at window radius by <= n, q-independently? This is speculative — be rigorous about whether the hypergraph is "dense enough" for containers to give a nontrivial bound. Probe the relevant hypergraph density on small (n,k) LARGE prime.
3. CRITICAL self-check: container bounds often reduce to a "supersaturation" input that, here, might BE the additive-energy count (=> W6) or the list size itself (circular). Check hard whether the container setup secretly needs a wall input. If it does, REDUCES_TO_WALL with the precise reduction. If it gives a genuinely new combinatorial sub-question, state it.
Deliverable: the hypergraph model + density probe + verdict. Lean optional (only if a clean structural lemma emerges). This direction is high-risk; an honest REDUCES_TO_WALL or FAILED with a sharp reason is a valuable result.`,
  },
  {
    key: 'D5-Wildcard',
    prompt: `${COMMON}

DIRECTION D5 — WILDCARD: invent ONE completely orthogonal reformulation that no fleet comment, no tree file, and no avoid-list wall covers.

You have free rein, but you MUST: (a) grep the tree (ArkLib/Data/CodingTheory/ProximityGap/) and DISPROOF_LOG.md to confirm novelty; (b) certify (with a precise argument) that your direction does NOT reduce to W1-W9; (c) make a concrete claim and try to prove OR refute it.

Seed candidates (pick one you can make progress on, or invent your own — do NOT spread thin):
  (a) The MCA-bad locus as a LOW-RANK / DETERMINANTAL variety: the bad-gamma set is where a structured matrix (Hankel/Toeplitz/Sylvester in gamma) drops rank; bound the bad-gamma count by the DEGREE of the determinant (algebraic geometry / Bezout), NOT by character sums. Reach = degree/q?
  (b) PLOTKIN / anticode / Singleton-type bound directly on the correlated agreement, exploiting that the prize budget q*eps*=n is exactly n (the code length) — a sharp counting coincidence.
  (c) An INFORMATION-THEORETIC / entropy-compression bound: encode the list of high-agreement codewords compressively using RS rigidity; the encoding length bounds the list.
  (d) The DEEP HOLES of RS (words at max distance) and their covering structure: the MCA-bad words live near deep holes; bound via the (known, small) number of deep-hole classes for RS.
  (e) A GALOIS/Frobenius descent that is purely about the CODE's automorphism group (the affine group acting on the domain) and orbit-counting (Burnside), NOT about mu_n's additive structure.

DECISIVE: state your claim, give numerical evidence (probe_wf7, LARGE prime), and either prove an axiom-clean structural lemma OR a clean reduction/refutation. Quantify the reach past Johnson. Honesty over ambition.
Deliverable: the reformulation + probe + verdict + Lean lemma if one emerges.`,
  },
]

phase('Attack')
const results = await pipeline(
  TARGETS,
  (t) => agent(t.prompt, { label: `attack:${t.key}`, phase: 'Attack', schema: ATTACK_SCHEMA }),
  (atk, t) => {
    if (!atk) return null
    const vprompt = `${COMMON}

ADVERSARIAL VERIFICATION of NEW-DIRECTION target ${t.key}.

The attacking agent reported:
  verdict: ${atk.verdict}
  reducesToWall: ${atk.reducesToWall}
  reach: ${atk.reach}
  file: ${atk.file}
  probe: ${atk.probe}
  theorems: ${JSON.stringify(atk.theorems)}
  claimed axiomClean: ${atk.axiomClean}
  summary: ${atk.summary}
  keyFinding: ${atk.keyFinding}

YOUR JOB — skeptic, default to distrust. The PRIMARY question: is this direction GENUINELY NEW (not in tree, not in DISPROOF_LOG, does NOT secretly reduce to W1-W9), or did the agent miss a hidden reduction to a known wall?
1. If a Lean file is given, independently run: lake env lean ${atk.file} — confirm exit 0, no errors, no sorry/sorryAx, axiom set clean.
2. If a claim of "reach past Johnson" is made: is it mathematically sound, or does the bound actually collapse to Johnson / need a wall input (e.g. the dual weight enumerator = W2, the additive energy = W6)? Re-derive the key step.
3. If "REDUCES_TO_WALL": is the reduction correct and complete? (A wrong reduction would wrongly kill a live direction.)
4. If "NEW_LIVE/NEW_PARTIAL/PROVEN_PIN": HARD-CHECK that the new sub-question is not W1-W9 in disguise, and that any pin is not vacuous/circular. Sanity-check the probe logic (large prime? right radius?).
5. Verify no fabrication (sorry/admit/native_decide/fake axiom/circular hypothesis).
Report independent findings. compileConfirmed=false if you could not run it. Be specific.`
    return agent(vprompt, { label: `verify:${t.key}`, phase: 'Verify', schema: VERIFY_SCHEMA })
      .then((v) => ({ target: t.key, attack: atk, verify: v }))
  }
)

return results.filter(Boolean)
