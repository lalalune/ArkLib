export const meta = {
  name: 'refute25-conjectures',
  description: 'Adversarially attack the 25 curated novel delta* conjectures: 3 lenses each (reduce-BGK / reduce-Johnson / countermodel) into verdict ledger (#444)',
  phases: [
    { title: 'Refute', detail: '25 conjectures x 3 adversarial lenses, wave-batched' },
    { title: 'Synthesize', detail: 'per-conjecture verdicts + the survivor ledger' },
  ],
}
const REPO = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'
const CONJ = [
{
"signature": "Maslov-Weil-index-mstar-congruence",
"statement": "CONJECTURE (Maslov-index parity pin). Attach to the dyadic tower \u03bc_n \u2282 \u03bc_{2n} \u2282 \u2026 the Weil index \u03b3_p \u2208 \u03bc_8 (8th root of unity, the Maslov/Kashiwara cocycle of the squaring map x\u21a6x\u00b2 over Z/2^\u03bc), a Z/8-valued 2-cocycle on the metaplectic cover. CLAIM: the over-determination depth m* (with \u03b4* = 1\u2212\u03c1\u2212m*/n) is congruence-pinned by the Maslov index: m* \u2261 s(\u03b3_p^{(\u03bc)}) (mod 4) where s is the signature-defect of the Maslov triple-index of the three Lagrangians {domain, dual-domain, codeword-space} at the binder, AND m* is the UNIQUE depth in [\u230alog\u2082 n\u230b, 2\u230alog\u2082 n\u230b] meeting that congruence and the budget c",
"mechanism": "\u03b4* = 1\u2212\u03c1\u2212m*/n. The Maslov index is a Z/8-valued topological invariant of the triple of Lagrangian subspaces realized by (evaluation domain, its theta-dual, codeword space) \u2014 it is exactly the obstruction to a global metaplectic trivialization, hence the obstruction to the tower descent closing at the trivial depth. The congruence m* \u2261 Maslov (mod 4) PINS the residue class of m*; combined with the proven monotone budget-crossing (m* is the unique crossing depth, _DstarCollapseLaw rigidity_bound), the residue + the crossing window single out one integer m*. No averaging, no cancellation: the value is read off the Hilbert-symbol/Weil-index formula, which depends only on p mod 8 and \u03bc (this matc",
"whyNotBGK": "The Maslov index is INVISIBLE to every moment/energy method by construction: it is a torsion (Z/8) cohomology class, while the wall M\u2264C\u221a(n log m) is a real-analytic magnitude bound \u2014 the meta-theorem's three required properties (b-sensitive, archimedean, L\u221e) are all real-valued, and a Z/8 cocycle carries no real-magnitude information, so no moment can detect it (the period family is real Gaussian ",
"notBGK": 10,
"novelty": 10,
"feasibility": 3
},
{
"signature": "cat-map-QUE-rate-equidistribution-floor",
"statement": "CONJECTURE. Identify the \u03bc_n-coset incidence dynamics on the far line with iterates of a quantized linear toral automorphism (cat map) A\u2208SL_2(Z/n) of order = 2-power, acting on the (Z/n)\u00b2 lattice of (subset, scalar) pairs; let the depth-m binding count D*(m) = \u03a3 over A-periodic points of period dividing 2m of a Hecke-operator matrix coefficient \u27e8A^m \u03c8_R, \u03c8_R\u27e9 for the dyadic Hecke basis. HYPOTHESIS (QUE convergence RATE): the eigenstates \u03c8_R of the quantized cat map at level n=2^\u03bc satisfy QUANTUM UNIQUE ERGODICITY with an EFFECTIVE polynomial rate: |\u27e8A^m \u03c8_R,\u03c8_R\u27e9 \u2212 (Liouville/Haar average)| \u2264 C",
"mechanism": "D*(m) splits exactly into a Haar main term (=n, the equidistributed budget) plus a fluctuation term equal to the QUE matrix-coefficient decorrelation. \u03b4* is pinned because m* is precisely the depth where the QUE fluctuation O(n^{1/2}\u03b8^{-m}) crosses the O(1) budget slack: solving n^{1/2}\u03b8^{-m*}\u224d1 gives m*=\u00bdlog_\u03b8 n exactly. The EXACT value of \u03b4* is therefore the explicit decorrelation base \u03b8 (the spectral gap of the quantized cat-map Hecke operator), which QUE/Lindenstrauss-Bourgain-Lindenstrauss methods (entropy + Hecke recurrence) supply as an arithmetic spectral gap, not as a character-sum bound. The n-uniformity over the 2-power tower is the whole content.",
"whyNotBGK": "The object bounded is a HECKE-OPERATOR MATRIX COEFFICIENT \u27e8A^m \u03c8,\u03c8\u27e9 of an eigenstate of the quantized dynamics \u2014 a quantum dynamical correlation, not a value of \u03b7_b and not a power-sum of \u03b7-values. The decay mechanism is the ARITHMETIC SPECTRAL GAP of the cat-map Hecke operators (entropy of invariant measures, Lindenstrauss-style), which the meta-theorem cannot see because it is neither b-indexed ",
"notBGK": 9,
"novelty": 10,
"feasibility": 2
},
{
"signature": "KloostermanSheaf-FreqMonodromyPin",
"statement": "Conjecture (frequency field is a Kloosterman/hypergeometric sheaf trace; monodromy pins \u03b4*). The map b\u21a6\u03b7_b extends to b\u21a6\u03b7_b(t)=\u03a3_{x\u2208\u03bc_n}e_p(b x) as the trace function of an explicit \u2113-adic sheaf F on the multiplicative line (a [n]-Kummer pushforward of the Artin\u2013Schreier sheaf \u2014 a 'monomial Kloosterman sheaf' for the map x\u21a6x on \u03bc_n composed with t\u21a6t^n). HYPOTHESIS: F is geometrically irreducible with geometric monodromy group G_geom EQUAL to the full classical group predicted by Katz's diophantine criteria (the sheaf is 'as random as possible' in the multiplicative variable b), and its conduct",
"mechanism": "If b\u21a6\u03b7_b is the trace of a sheaf with full monodromy and small conductor, then by Deligne\u2013Katz the values are equidistributed across the m cosets with discrepancy O(conductor\u00b7q^{\u22121/2}); the SUP over m cosets is then attained at the finitely many GALOIS-FIXED singular cosets, and m* (the over-determination depth) is the monodromy DROP integer there. This pins \u03b4* to an exact p-independent value: the entire \u03b4* is read off a representation-theoretic invariant (the local monodromy drop), bypassing any \u221a-cancellation estimate of the sup.",
"whyNotBGK": "BGK/sup-norm treats \u03b7_b as a black-box exp-sum to be cancelled. Here \u03b7_b is identified as a SHEAF TRACE and its sup is pinned by the GEOMETRIC MONODROMY GROUP and CONDUCTOR \u2014 a Galois/\u2113-adic object orthogonal to additive energy. The repo's memory records that the distinct-\u03b3 union-count and \u03b4* are p-INDEPENDENT (smoking gun D=89 across 4 primes), which is exactly what a monodromy-drop integer predi",
"notBGK": 9,
"novelty": 10,
"feasibility": 3
},
{
"signature": "Stone-vonNeumann-derandomization-pin",
"statement": "CONJECTURE (Stone\u2013von Neumann de-randomization of \u03b4*). The Heisenberg group H(Z/n) (with n=2^\u03bc) has, by Stone\u2013von Neumann, a UNIQUE irreducible representation of given central character; the metaplectic group Mp(2,Z/n) acts on it by intertwiners. CLAIM: the explicit dyadic RS code RS[\u03bc_{2^\u03bc},k] and a HAAR-RANDOM evaluation-domain code of the same parameters carry the SAME Heisenberg-module structure on their (codeword stack \u2295 dual) spaces \u2014 they differ only by a metaplectic intertwiner that, being a Mp-isomorphism, PRESERVES the MCA bad-\u03b3 count function exactly. Therefore \u03b4*(explicit dyadic RS",
"mechanism": "The prize is exactly the EXPLICIT case (GG25/CS25 did random/folded RS to capacity; explicit dyadic RS is open). Stone\u2013von Neumann uniqueness is the canonical de-randomization tool: any two realizations of the same Heisenberg central character are metaplectically intertwined. If the MCA bad-\u03b3 event is a function on the Heisenberg module that is intertwiner-equivariant (because the bad-\u03b3 condition is a Lagrangian-incidence condition, manifestly Heisenberg-natural), its worst-case count is a Heisenberg-MODULE INVARIANT, hence identical for explicit and random codes by uniqueness. This pins \u03b4*(explicit) = \u03b4*(random) = 1\u2212\u03c1 EXACTLY (an equality of two Finset.card sup functions via a single intert",
"whyNotBGK": "It compares two \u03b4* values via a rep-theoretic ISOMORPHISM, never bounding any |\u03b7_b|; the only quantity is a Card equality under an intertwiner bijection. The meta-theorem requires a winning method to be b-sensitive/archimedean/L\u221e \u2014 but this method has NO b at all and NO norm: it is a transfer-of-equality between two codes, the structural opposite of a sup-norm bound. It cannot collapse to M\u2264C\u221a(n l",
"notBGK": 9,
"novelty": 10,
"feasibility": 2
},
{
"signature": "eichler-selberg-trace-identity-value",
"statement": "CONJECTURE. There is an EXACT Eichler-Selberg-type trace identity for the family \u03b7_b that pins M(n) as a sum of class numbers / Hurwitz numbers rather than a \u221a-cancellation. Concretely: let A_n be the n\u00d7n circulant 'dilation transfer matrix' of the doubling map x\u21a6x\u00b2 acting on the exponents of \u03bc_n (an order-\u03bc automorphism of \u03bc_{2^\u03bc}), and let H(\u00b7) be the Hurwitz class number. CONJECTURE: \u03a3_{b: b\u2208\u03bc_n} \u03b7_b\u00b7\\bar{\u03b7_b}\u00b7(twist by quadratic character of the discriminant of b\u2212x) = \u03a3_{t\u00b2\u22644n} P_k(t,n)\u00b7H(4n\u2212t\u00b2) + (Eisenstein/principal term), where P_k is a Gegenbauer polynomial \u2014 an EXACT identity making ",
"mechanism": "The Eichler-Selberg trace formula equates a spectral trace (\u03a3 over Hecke eigenvalues) with a GEOMETRIC sum over elliptic/hyperbolic conjugacy classes weighted by class numbers H(4n\u2212t\u00b2). Our \u03b7_b family, via the self-dual maximizer and the doubling-automorphism structure of \u03bc_{2^\u03bc}, is exactly such a trace (\u03b7_b = trace of Frob on the dilation transfer operator). The identity is EXACT \u2014 no inequality, no moment optimization \u2014 so it pins M(n) to the value of a class-number-weighted polynomial sum. The \u03b4*-rung is then determined by an arithmetic threshold (when does the class-number sum's leading mass point fall below budget), an exact integer/algebraic condition, not a \u221a-cancellation estimate. T",
"whyNotBGK": "A trace formula is an EXACT identity, structurally incapable of being the moment bound (which is an inequality saturated only in a limit). It uses class numbers H(4n\u2212t\u00b2) \u2014 an arithmetic-geometric invariant (point-counts on elliptic curves / binary quadratic forms) that the moment-blind meta-theorem cannot see, because it is NOT a symmetric function of the |\u03b7_b| values; it is a DUAL geometric expan",
"notBGK": 9,
"novelty": 10,
"feasibility": 2
},
{
"signature": "krein-parameter-vanishing-design-threshold",
"statement": "Let E_0,...,E_d be the primitive idempotents of the cyclotomic scheme on mu_n with Krein parameters q^k_{ij} >= 0 (the dual intersection numbers, nonnegative by the Krein condition). CONJECTURE: delta* is pinned EXACTLY at the radius where the agreement-set configuration first FAILS to be a relative t-design in the dual (Q-polynomial) ordering, i.e. delta* = (1/n)*(t*(n)+1) where t*(n) is the LARGEST t such that ALL Krein parameters of the t-th dual-degree closure vanish, q^k_{ij} = 0 for i+j <= t (the 'dual-tightness' / spherical-design strength of mu_n viewed as a code in the association sch",
"mechanism": "Mutual correlated agreement at radius delta requires a family of codewords whose pairwise agreement profile realizes a specific configuration in the scheme. By the linear-programming / Delsarte duality of association schemes, such a configuration of strength t exists at a given radius IFF the dual (Krein) inner distribution is feasible, which is governed by the VANISHING pattern of the Krein parameters q^k_{ij} (the design is 'tight' exactly when the relevant q^k_{ij}=0). The threshold radius is the largest t for which the Krein vanishing holds; beyond it a forbidden q^k_{ij}>0 obstructs the design and the bad family cannot be assembled, pinning delta*. Because q^k_{ij} are EXACT entries of ",
"whyNotBGK": "Krein parameters are the DUAL of intersection numbers -- they live in the Q-polynomial (Bose-Mesner *idempotent*) algebra, are nonnegative INTEGERS or exact algebraic integers, and encode design/tightness, an object the L-infinity sup-norm wall has no access to. The Krein condition q^k_{ij}>=0 is a positivity/feasibility constraint (Delsarte LP duality), NOT a cancellation bound; its VANISHING at ",
"notBGK": 9,
"novelty": 9,
"feasibility": 3
},
{
"signature": "o-minimal-deltastar-tameness-finite-cell",
"statement": "CONJECTURE: the threshold function (rho,t)->delta*(rho,n), t=1/log n, for explicit dyadic RS[mu_n,rho] at eps*=2^-128 (delta*=sup{delta: I(delta)<=q*eps*}), is DEFINABLE in R_{an,exp} UNIFORMLY in p=q for all p>P_0(n). By o-minimal cell decomposition the strip (1-sqrt rho, 1-rho-c*t) partitions into finitely many cells on each of which delta* is one real-analytic/semialgebraic expression with algebraic exponents; in particular delta*(rho,n)=1-rho-g(rho)/log n+O(1/log^2 n) with g(rho) ALGEBRAIC over Q(rho). PIN: g(rho) is the o-minimal leading-cell coefficient, read off from finite-cell boundar",
"mechanism": "delta* is the sup of a definable family (I(delta)<=q*eps* is a finite Boolean combination of polynomial inequalities in period coords exp(2 pi i k/2^mu), R_{an,exp}-definable). o-minimality => the sup is definable with finitely many non-analyticity points => delta* piecewise analytic on finitely many cells; a definable germ in the 1/log n->0 regime has algebraic leading exponent, FORCING the form 1-rho-g(rho)/log n. The single g(rho) is pinned by matching one exactly-known scale. Tameness turns 'compute an asymptotic' into 'read a finite cell datum'.",
"whyNotBGK": "BGK is an L-infinity sup-norm ESTIMATE giving a number, never the functional FORM of the threshold. This is a TAMENESS/finiteness statement about the threshold FUNCTION, invisible to the moment-blind meta-theorem: it is not a moment of any family but a definability statement about a sup, and it forbids the p-oscillation BGK must estimate -- consistent with the PROVEN p-independence of the distinct",
"notBGK": 9,
"novelty": 9,
"feasibility": 3
},
{
"signature": "FourierDimFreqField-RestrictionGap",
"statement": "Conjecture (frequency-field Fourier dimension forces the exact gap). View the normalized frequency field f: F_q^*/\u03bc_n \u2192 C, f(b\u0304)=\u03b7_b/\u221an (well-defined on cosets). Its multiplicative Fourier coefficients are f\u0302(\u03c7)=\u03c4(\u03c7)/\u221aq\u00b71[\u03c7|\u03bc_n=1] \u2014 supported on EXACTLY n characters, each of modulus 1. HYPOTHESIS (a Mockenhaupt\u2013Tao restriction/extension estimate for the MULTIPLICATIVE group F_q^*/\u03bc_n \u2245 Z/m): the measure \u03bc_f with these n unimodular Fourier coefficients on Z/m satisfies a Salem-type lower bound on its Fourier dimension AND a matching restriction estimate \u2016f\u0302\u2016_{\u2113^p(dual)} \u2272 (Mockenhaupt\u2013Tao expon",
"mechanism": "The frequency field's multiplicative spectrum is supported on the index-m SUBGROUP {\u03c7: \u03c7|\u03bc_n=1} with all coefficients unimodular (Gauss-sum normalization |\u03c4(\u03c7)|=\u221aq). A restriction estimate for a SUBGROUP support is exact (no \u221a-loss \u2014 subgroups are the equality case of Mockenhaupt\u2013Tao on Z/m), so the L^\u221e norm of f is pinned algebraically by the n unimodular coefficients on an index-m subgroup. This converts the sup directly into an EXACT closed form via the subgroup structure, pinning \u03b4* without any cancellation estimate.",
"whyNotBGK": "BGK/energy bounds the sup of an ADDITIVE exp-sum on \u03bc_n. This routes entirely through the MULTIPLICATIVE Fourier transform on F_q^*/\u03bc_n \u2245 Z/m, where the spectrum is a SUBGROUP (the \u03bc_n-annihilator) with unimodular weights \u2014 the equality/exact case of restriction, NOT a cancellation regime. The object is the Fourier DIMENSION of the frequency measure on the character group, an L^\u221e-restriction quant",
"notBGK": 9,
"novelty": 9,
"feasibility": 3
},
{
"signature": "Swan-break-valuation-deltastar",
"statement": "Define the local break-multiset (Swan/slope decomposition) of the convolution sheaf M_r = F_b^{*r} at its two singular points {0, infinity} on P^1 (F_b = [t->t^m]^* L_psi). FKM/Katz break-rigidity conjecture (this angle): delta* in the prize regime is pinned by the p-ADIC valuation/break-jump pattern, NOT the rank: specifically delta* = 1 - rho - m*/n where m* = min{ r : the break decomposition of M_r at infinity acquires a NON-INTEGER slope (a genuine wild-ramification break > 0) }. Conjecture: because m = (q-1)/n = 2^128 is a 2-power index and psi is additive of conductor 1, ALL breaks of F_",
"mechanism": "The Swan conductor / break decomposition is a p-ADIC (l-adic local-monodromy) invariant: it is an exact non-negative rational read from the wild inertia action, totally independent of the archimedean SIZE of any character sum. For a TAME sheaf the Euler-Poincare / Grothendieck-Ogg-Shafarevich count is EXACT (chi_c = rank\u00b7(2-2g-#sing) with Swan=0), so the number of Frobenius eigenvalues \u2014 hence the dimension of the incidence space, hence D*(m) \u2014 is determined by the rank+tame-singularity count alone with NO sqrt-p error. delta* binds precisely when a wild break first appears, because a wild break adds Swan>0 to the conductor and creates exactly one extra independent Frobenius eigenvalue, drop",
"whyNotBGK": "Swan conductors and break slopes are WILD-INERTIA (p-adic) invariants: rational numbers measuring ramification, with no archimedean content whatsoever. The energy/BGK wall lives in the COMPLEX magnitude of eta_b (an archimedean L-infinity object the meta-theorem filters on); a break slope is orthogonal by type \u2014 it is a valuation, the exact phase/valuation object the prompt names as moment-blind-i",
"notBGK": 9,
"novelty": 9,
"feasibility": 2
},
{
"signature": "DMO-nullcone-orbit-degree-relation-module",
"statement": "Conjecture (Dvir\u2013Mehta\u2013Oliveira orbit-degree of the relation module). Consider the F_p[\u03bc_n]-module Rel_{r} of F_p-linear relations among the depth-r dilation-twisted Gauss periods, viewed as a point in the affine space of (2r)-tensors via the moment map. Let the algebraic group G = F_p^\u00d7 \u00d7 Aut(\u03bc_n) (dilation \u00d7 Galois) act. DMO (Derksen\u2013Makam / Dvir\u2013Mehta\u2013Oliveira null-cone theory) attaches to this action a NULL-CONE membership degree and an ORBIT-CLOSURE separation degree \u03b4_DMO(r,p) = the minimal degree of a G-invariant polynomial separating the spurious-relation locus from the coset (char-0) ",
"mechanism": "The char-0 coset locus (V_r=2^{n/2^{\u230alog\u2082r\u230b+1}} solutions) is the STABLE orbit of the dilation\u00d7Galois action. The char-p spurious solutions are EXTRA solutions that appear only mod p. The DMO/null-cone claim is that these extras are precisely the UNSTABLE points (orbit-closure boundary) of the same action, with bounded separation degree \u03b4\u2080. Semicontinuity of orbit dimension then bounds the spurious count by the number of boundary strata, which \u03b4\u2080 controls. This caps Spur, discharges (P2-Slack)/_wf6P2, and via slack_route_full pins M and hence \u03b4* to the KKH26 upper edge.",
"whyNotBGK": "This is a GEOMETRIC-INVARIANT-THEORY object (null-cone, orbit-closure, Hilbert\u2013Mumford stability degree), not a magnitude. The BGK wall lives in the SCALAR \u2016\u00b7\u2016_\u221e of a character sum; DMO degree lives in the INVARIANT RING of a group action on a tensor \u2014 it sees the symmetry-degeneration STRUCTURE of relations, which the moment is provably blind to (moments are degree-0 invariants under a torus; DMO",
"notBGK": 9,
"novelty": 9,
"feasibility": 2
},
{
"signature": "Weil-metaplectic-MCA-rigidity",
"statement": "CONJECTURE (Weil-equivariance pin). Let n=2^\u03bc, q=p, RS[F_q, \u03bc_n, k] the explicit dyadic Reed\u2013Solomon code. The metaplectic double cover Mp(2,Z/n) acts on the pair (codeword stack, evaluation domain) by the finite oscillator/Weil representation W: the generator x\u21a6x\u00b2 (the Weil 'S' element conjugated by the squaring map) sends the MCA bad-scalar event E_\u03b4(u\u2080,u\u2081,\u03b3) to E_\u03b4(W\u00b7(u\u2080,u\u2081), \u03b3'), with \u03b3' an explicit unit twist. CLAIM: the worst-case bad-\u03b3 count function \u03b4 \u21a6 Card{\u03b3 : (u\u2080,u\u2081,\u03b3) bad} is INVARIANT under this whole Mp(2,Z/n) action (not just the cyclic rotation subgroup already pinned in MCAEqu",
"mechanism": "\u03b4* = capacity \u2212 m*/n (the in-tree collapse law _DstarCollapseLaw; m* = smallest over-determination depth with distinct-\u03b3 union-count \u2264 budget n). The metaplectic group is STRICTLY LARGER than the rotation (translation) group whose invariance is already proven (mcaEvent_rs_rotate). If the worst-direction bad-\u03b3 count is rigid under Mp(2,Z/n), then m* equals the index of the metaplectic stabilizer of the worst direction inside Mp \u2014 a GROUP-THEORETIC integer, computed by orbit-counting (Burnside), NOT by any growth-law numerics. The squaring generator halves the stabilizer at each dyadic octave, so the stabilizer chain has length \u03bc=log\u2082 n and m* = \u0398(log n) EXACTLY, pinning \u03b4* into the window. Th",
"whyNotBGK": "It never touches |\u03b7_b| or any moment \u03a3|\u03b7_b|^{2r}=q\u00b7E_r. It is a Card-of-a-Finset invariance under a finite group action on the (codeword,domain) pair \u2014 exactly the object class (MCAEquivariance) that the moment-blind meta-theorem cannot express, because the meta-theorem's necessity proof only obstructs methods that factor through the period family {\u03b7_b}. The metaplectic group action permutes the b",
"notBGK": 9,
"novelty": 9,
"feasibility": 4
},
{
"signature": "Fourier-SoS-degree-asymmetry-transition",
"statement": "Constant-degree Fourier SoS feasible below Johnson and above capacity; first-infeasible delta = delta* = 1-rho-Theta(1/log n).",
"mechanism": "Phase transition; char-p antipodal-identity SoS degree jumps (char-0 deg 2, char-p higher by splitting).",
"whyNotBGK": "Pseudoexpectation = PSD functional not a sum; IMP-2023 Fourier-SoS separates from energy; pin is the degree jump.",
"notBGK": 9,
"novelty": 9,
"feasibility": 3
},
{
"signature": "ZilberPink-PeriodTorusAnomalousIntersection",
"statement": "Conjecture (unlikely-intersection rigidity for the period torus). Let T_m = G_m^m be the multiplicative torus and let W \u2282 T_m be the (m\u22121)-dimensional subvariety cut out by the EXACT char-0 power-sum identities the Gauss-period value vector (w_1,\u2026,w_m) satisfies over \u2124 (\u03a3w_i=\u2212n/(q\u22121)\u00b7\u2026, \u03a3w_i^2=p\u2212n, \u03a3w_i^4=p(3n\u22123)\u2212n^3, the in-tree coset-collapse relations), m=(q\u22121)/n. CLAIM: the prize sup-norm event {max_i |w_i| \u2265 \u221a(2n log m)\u00b7(1+\u03b7)} for any fixed \u03b7>0 forces the reduced mod-p point (w_i mod p)_i to lie in the intersection of W with a torsion coset of a proper algebraic subgroup H \u228a T_m of bounde",
"mechanism": "An over-large sup-norm value at one frequency b is an algebraic constraint w_b \u2208 (large-modulus shell). Combined with the m\u22121 EXACT power-sum identities (which cut W to a curve once enough are imposed), a spike forces the point onto an unexpectedly small-dimensional intersection. Zilber\u2013Pink/Bombieri\u2013Masser\u2013Zannier say points on W lying in anomalous subgroup cosets have BOUNDED HEIGHT \u2014 a Northcott-type finiteness. Bounded height \u21d2 the underlying prime p (which sets the field size and hence the arithmetic height of w as an algebraic integer of norm related to powers of p) is bounded. So the spike can only occur for finitely many small p, excluded at the prize prime. This pins M exactly at th",
"whyNotBGK": "The wall is an ANALYTIC concentration estimate: bound a sup by \u221a(variance\u00b7log). Zilber\u2013Pink is a DIOPHANTINE FINITENESS theorem: it says certain algebraic points are finite/bounded-height because their COORDINATES are multiplicatively dependent in an unexpected way (anomalous subgroup membership). The invariant consumed is the lattice of multiplicative relations among the coordinates w_i and the H",
"notBGK": 9,
"novelty": 9,
"feasibility": 2
},
{
"signature": "cyclotomic-number-rank-pins-distinct-gamma-fusion",
"statement": "Let C_n(F_q) be the cyclotomic association scheme on \u03bc_n \u2286 F_q* (q=n^\u03b2, \u03b2\u22484-5, n=2^\u03bc). Its INTEGER structure constants are the cyclotomic numbers (i,j) := #{x\u2208\u03bc_n : x\u22121 \u2208 g^i \u03bc_n, conjugate offset g^j \u03bc_n}, equivalently the intersection numbers p_ij^k of the m=(q\u22121)/n-class fusion. Form the integer m\u00d7m cyclotomic-number matrix \u0393 = ((i,j))_{i,j}. CONJECTURE (Fusion-Rank Identity): the far-coset MCA incidence count that defines \u03b4* equals the corank deficiency of the dyadic fusion of \u0393, specifically  card(\u22c3_R {\u03b3_R}) = m \u2212 rank_{F_2}(\u0393 mod 2) + r,  and on the dyadic subgroup \u03bc_{2^a} this corank is",
"mechanism": "\u03b4* is, in the substrate, the p-independent integer union-count |\u22c3_R{\u03b3_R}| \u2264 n (the distinct-\u03b3 / line-explainability count, ABF26 \u00a74.5 far-coset face). The cyclotomic numbers (i,j) are the EXACT integer intersection data of the scheme: two far cosets \u03b3_R, \u03b3_S coincide on the weight-\u230a\u03b4n\u230b syndrome ball iff a specific cyclotomic-number block is nonzero. So the union-count is literally the rank/support of the integer matrix \u0393. For \u03bc_{2^a} the cyclotomic numbers obey an exact dyadic recursion (Gauss's evaluation of 2-power cyclotomic numbers via the rational part of Gauss sums = integers, no transcendental magnitude), giving \u0393 mod 2 a block-Toeplitz form whose F_2-corank is computable in closed fo",
"whyNotBGK": "The wall M=max|\u03b7_b| is a function of the magnitudes |\u03b7_b|=\u221a((i,i)+const); the two in-tree collapse files prove every magnitude-multiset functional renames M/\u221an. \u0393 is the INTEGER tensor (i,j), not the magnitudes: rank_{F_2}(\u0393 mod 2) is invariant under multiplying any \u03b7_b by a phase or rescaling magnitudes, so it cannot be recovered from {|\u03b7_b|} \u2014 it sees the COMBINATORIAL incidence (which coset hit",
"notBGK": 9,
"novelty": 9,
"feasibility": 4
},
{
"signature": "pseudocyclic-valency-multiplicity-defect-vector-pins-delta",
"statement": "For a genuinely PSEUDOCYCLIC association scheme the multiplicities equal the valencies (m_i = k_i for all nontrivial classes) \u2014 this is the van Dam\u2013Muzychuk characterization, and it forces a Ramanujan-tight design. The cyclotomic scheme on \u03bc_n is almost-pseudocyclic; define the INTEGER pseudocyclic defect vector d_i := m_i \u2212 k_i \u2208 \u2124 (NOT the magnitude defect |\u03b7|\u00b2\u2212n already shown field-universal in PseudocyclicDefectSum.lean). CONJECTURE: (i) \u03a3_i d_i = 0 and the defect vector d is supported exactly on the 2-power-order character classes (Galois orbits of size dividing 2^a); (ii) the MCA far-cos",
"mechanism": "Valencies k_i (sizes of scheme classes = coset sizes, all = m) and multiplicities m_i (dimensions of eigenspaces) are PURELY combinatorial integers from the Bose\u2013Mesner P/Q matrices; their difference d_i measures how far the scheme is from the pseudocyclic ideal where every eigenspace is balanced. A nonzero d_i at a class means that class carries an EXTRA explainable far-coset direction (a multiplicity surplus = an extra collinearity = an extra bad line), so the binding radius s* \u2014 the smallest s where far cosets over-determine \u2014 increments by exactly \u2016d\u2016_0. Counting the integer support of d (a finite, p-independent Galois-orbit computation via the cyclotomic-scheme P-matrix, which for 2-pow",
"whyNotBGK": "The wall bounds the magnitude of one eigenVALUE; d_i is the gap between an eigenspace DIMENSION (multiplicity, an integer = trace of an idempotent) and a class SIZE (valency, an integer). Neither m_i nor k_i is a magnitude of \u03b7_b \u2014 they are integer invariants of the idempotent/adjacency structure, invariant under any rescaling of the periods. The magnitude-defect total is fixed at \u2212n(n\u22121) (Pseudoc",
"notBGK": 9,
"novelty": 9,
"feasibility": 3
},
{
"signature": "OdometerSignLaw-BirkhoffAverage",
"statement": "Index the dilation orbit of b by k in Z/m via b_k = g^k * b0. CONJECTURE: the period sign s_{b_k}(i) is given by an EXPLICIT 2-adic substitution / odometer cocycle: there is a fixed finite-state map phi: (Z/2^mu) x {+,-} -> {+,-} such that s_{b_k}(i) = phi-orbit value determined by the 2-adic digits of k*(p-1)/n, making i -> s(i) the Birkhoff orbit of a minimal odometer (adding-machine) rotation on Z/2^mu. The asymptotic density of +'s, lim_{mu} (1/mu) #{i<=mu : s_{b}(i)=+}, equals the Birkhoff average alpha = mu(+-cylinder) of the odometer-invariant measure, a CONSTANT in (1/2, 1). Consequenc",
"mechanism": "An odometer (adding machine on Z/2^mu, the natural dynamics of the 2-power tower since going mu_{2^i}->mu_{2^{i+1}} is literally a +1 carry in the 2-adic digit of the dilation index) is UNIQUELY ERGODIC and MINIMAL: every orbit equidistributes deterministically with an EXACT (not random) large-deviation rate for run-lengths of any cylinder. Identifying the sign cocycle as a continuous {\u00b11}-valued function on the odometer gives an exact Birkhoff/large-deviation control on all-+ runs with no probabilistic input, capping the doubling trajectory and pinning delta*.",
"whyNotBGK": "Odometer dynamics is DETERMINISTIC and ARCHIMEDEAN (a uniquely-ergodic adding machine), and the run-length large-deviation it produces is an EXACT ergodic-average statement, NOT the probabilistic-EVT the meta-theorem forbids (periods-are-exchangeable-white-noise refutes EVT; an odometer is the OPPOSITE \u2014 fully rigid, zero entropy, deterministic). The object is the sign cocycle over a 2-adic odomet",
"notBGK": 9,
"novelty": 9,
"feasibility": 2
},
{
"signature": "WeilIndex-MultiplierWeightedFixedPoint",
"statement": "Conjecture (multiplier-weighted self-similar recursion). Let n=2^mu, p with mu_n in F_p, and for b in F_p^x set eta_b = Sum_{x in mu_n} e_p(b x). Because the squaring map sq: mu_n -> mu_{n/2} is a 2-to-1 group homomorphism with fibers {x,-x}, write eta_b = Sum_{y in mu_{n/2}} (T-twisted partial Gauss sum over the fiber of y). Define the Weil-index-weighted transfer operator on the m-tuple of normalized phases u_b := eta_b/sqrt(n): conjecture there is an EXACT identity eta_b = gamma_p(b) * sqrt(2) * eta'_{phi(b)}, where eta'_c = Sum_{y in mu_{n/2}} e_p(c y) is the SAME functional at half scale,",
"mechanism": "The exact fiberwise identity eta_b = gamma_p(b) sqrt(2) eta'_{phi(b)} is a TRUE rewriting (completing the square b x = b((x+(-x))/... ) on the antipodal fiber and applying the Weil/metaplectic transformation law for the order-2 Gauss factor), NOT an inequality. Iterating mu-1 times reduces M(n) to a base object on mu_2 (a fixed finite cyclotomic object, p-independent at fixed dyadic ratio) times the product of |gamma_p|=1 multipliers. The point: the recursion is EXACT and length-tracking (each step is a genuine equality with an explicit phase multiplier and an explicit factor sqrt(2)), so the supremum M(n) is pinned by the orbit structure of the reindexing phi on the dual coset Z/m, which is",
"whyNotBGK": "The multiplier gamma_p(b) in mu_8 is an 8th-root-of-unity automorphy factor. Every moment/energy/Wick object (E_r, A_r, the deep autocorrelation recursion) is a sum of |eta_b|^{2r}, which is BLIND to all unit-modulus phases by construction: |gamma_p eta'|^{2r}=|eta'|^{2r}, so the meta-theorem (which caps any 2nd-order method at Johnson) provably cannot see this identity. It is also distinct from t",
"notBGK": 9,
"novelty": 9,
"feasibility": 3
},
{
"signature": "DAM-IncompleteTheta-CuspAutomorphy-SquareLattice",
"statement": "Conjecture (Demirci-Akarsu-Marklof automorphy for the SQUARED incomplete theta). The in-tree refutation (_wf2ND) showed {eta_b/sqrt(n)} is Gaussian, NOT the DAM self-similar law for the LINEAR incomplete Gauss sum. Conjecture the DAM/quantum-modular law DOES hold for the QUADRATICALLY-PARAMETRIZED partial theta attached to mu_n: define Theta_N(b,p) = Sum_{0<=k<N} e_p(b * w^{k^2}) where w is a generator of mu_n and N=n (so the exponents run over the SQUARE residues k^2 mod n, the image of the squaring section). Then Theta_N satisfies the EXACT three-term theta functional equation (continued-fra",
"mechanism": "For the quadratic phase k -> k^2 the partial theta sum Theta_N is a genuine incomplete Jacobi theta value, and (unlike the linear sum) it obeys the modular/quantum-modularity functional equation exactly: the metaplectic group SL_2(Z)-action renormalizes (b/p) by the continued-fraction (Gauss) map with a sqrt(N/N') contraction and a Weil-index multiplier at each step. Because the continued fraction of a rational b/p TERMINATES, the renormalization is a FINITE exact product (a cocycle telescoping), pinning Theta_n(b,p) to a closed form. Re-expressing eta_b over mu_n in terms of these quadratic theta values (via the squaring section being a 2-to-1 cover and quadratic Gauss reciprocity threading",
"whyNotBGK": "DAM renormalization pins the value by an EXACT continued-fraction cocycle telescoping, never by a moment/sqrt-cancellation argument; the heavy DAM tail (which _wf2ND found ABSENT for the linear sum) is the signature that, on the square-residue exponents, the object is genuinely self-similar and the value is determined by the Gauss-map orbit of b/p (an arithmetic-dynamical, b-sensitive, archimedean",
"notBGK": 9,
"novelty": 9,
"feasibility": 2
},
{
"signature": "horocycle-escape-of-mass-winding-pins-deltastar",
"statement": "Conjecture (dyadic horocycle escape-of-mass winding). Encode the dyadic-RS agreement set as a closed orbit of the horocycle flow on the unit tangent bundle of the modular surface: the mu_n-orbit lifts to a periodic horocycle of period T(n,q) ~ n at height y = 1/q, and the agreement excess above Johnson is the WINDING NUMBER w(n,q) = net number of times this horocycle crosses the cusp neighborhood (the escape-of-mass / non-equidistribution defect). By Sarnak/Stroembergsson effective horocycle equidistribution, the integral over the horocycle of an incomplete Eisenstein series = Haar + E(n,q) wi",
"mechanism": "delta-star is pinned to a DISCRETE/RIGID invariant -- the integer winding number w(n,q) of the closed horocycle around the cusp -- which is moment-blind because it is a topological degree (an integer cohomology class), not a continuous size. The exact value delta-star = 1 - sqrt(rho) + w/n then lives on a RATIONAL LATTICE 1/n apart, and the specific w in the interior is pinned by the FIRST Fourier coefficient of the incomplete Eisenstein series (an Estermann/divisor-sum special value, computable exactly) via Stroembergsson's effective horocycle theorem. The mechanism never invokes the sup-norm: the winding number counts cusp-crossings of one closed orbit (a degree), and the effective rate is",
"whyNotBGK": "The pinning object is an INTEGER WINDING NUMBER (topological degree / cohomology class of the closed horocycle around the cusp), structurally incapable of being a moment or a sup-norm -- it is rigid and discrete, exactly what the moment-blind meta-theorem (constraining only continuous moment/RMS/sup quantities) cannot reach. The continuous-spectrum contribution is an EXACT divisor-sum (Estermann s",
"notBGK": 8,
"novelty": 10,
"feasibility": 2
},
{
"signature": "Howe-dualpair-O1-Sp-branching-multiplicity-pins-mstar",
"statement": "Over F_p, the additive characters and \u03bc_n sit inside the finite Weil representation of Sp_2(F_p); the reductive dual pair (O_1,Sp_1) (O_1={\u00b11}=Aut of the rank-1 quadratic form x\u00b2) acts on the oscillator space, and the squaring map x\u21a6x\u00b2 is exactly the O_1-coinvariants projection. CONJECTURE: decompose 1_{\u03bc_n}=\u03a3_\u03c7 m_\u03c7\u00b7v_\u03c7 into O_1\u00d7(torus) Howe-dual isotypic components; the binding depth m* equals the Howe BRANCHING MULTIPLICITY \u03bc_n\u2192\u03bc_{n/2} of the relevant O_1-isotypic piece, an exact representation-theoretic integer (a Kostant-type weight multiplicity of the F_p-torus character lattice). Then \u03b4*",
"mechanism": "Howe duality gives a multiplicity-FREE-up-to-the-O_1-action decomposition; the branching law \u03bc_n\u2193\u03bc_{n/2} along the squaring tower is governed by an exact multiplicity formula (the number of torus weights collapsing under x\u21a6x\u00b2), which is a COUNT OF REPRESENTATIONS, not of character-sum mass. \u03b4* is pinned because the worst-direction list size at binding equals this multiplicity (the \u03c3-orbit of the worst weight), and the multiplicity equals the trivial-O_1-type count in the a-fold oscillator branching = a+O(1)=\u0398(log n). The fixed point is the stable branching multiplicity of the Howe-dual pair, reached in a=log\u2082n squaring steps; the value is an exact integer with no \u221a-cancellation.",
"whyNotBGK": "It counts REPRESENTATIONS (isotypic multiplicities in a Howe-dual decomposition), an object in the Grothendieck group of Sp_2(F_p)-modules, not character-sum magnitudes. The energy ladder/BGK/Wick are all moments of |\u03b7_b|; a branching multiplicity is a dimension of a Hom-space, invisible to any magnitude functional. The dual pair (O_1,Sp) makes the {\u00b11}-kernel of squaring into a GROUP acting on th",
"notBGK": 7,
"novelty": 10,
"feasibility": 2
},
{
"signature": "GaussSumSatoTate-FreqRestriction",
"statement": "Conjecture. Index the m=(q\u22121)/n cosets of \u03bc_n in F_q^* by the multiplicative characters \u03c7 trivial on \u03bc_n (the dual group of F_q^*/\u03bc_n, |\u00b7|=m). Then \u03b7_b = \u03a3_{x\u2208\u03bc_n} e_p(bx) is, by Gauss-sum expansion, \u03b7_b = (1/(q\u22121)) \u03a3_{\u03c7: \u03c7^? } \u03c4(\u03c7) \u03c7\u0304(b)\u00b7G_\u03c7(\u03bc_n), where \u03c4(\u03c7) is the Gauss sum and G_\u03c7(\u03bc_n)=\u03a3_{x\u2208\u03bc_n}\u03c7(x) is the \u03bc_n-restricted character sum (nonzero only on the n characters trivial on \u03bc_n). Equivalently the frequency field b\u21a6\u03b7_b is a *finite linear combination of exactly n Gauss sums* \u03c4(\u03c7_j) weighted by the unitary roots-of-unity matrix. HYPOTHESIS (Sato\u2013Tate / Katz equidistribution on the FREQUE",
"mechanism": "\u03b7_b is LITERALLY a fixed unitary (DFT-of-roots-of-unity) image of the n-vector of Gauss sums (\u03c4(\u03c7_j)). The sup over b is the sup over the m cosets of an n-term sum of FIXED Gauss sums against VARYING unimodular phases \u03c7\u0304_j(b). Katz equidistribution (a curvature/monodromy input on the Gauss-sum family \u2014 its geometric monodromy group is large) pins the joint distribution of the n phases, hence pins the exact extreme value of the n-term sum across the m cosets. \u03b4* is read off as 1\u2212\u03c1 minus the over-determination depth m*=(extreme value)/\u221an-deficiency, which the discrepancy bound makes EXACT rather than \u221a-cancellation-bounded.",
"whyNotBGK": "The BGK wall bounds the sup by \u221a-cancellation of a SINGLE additive exp-sum (the period side). Here the period side is held FIXED (the n Gauss sums \u03c4(\u03c7_j) are arithmetic constants, computed once) and ALL the variation is in the multiplicative phases \u03c7\u0304_j(b) over the m cosets \u2014 a DIFFERENT object whose equidistribution is governed by Katz monodromy of Gauss-sum sheaves, not by the energy/moment of \u03bc",
"notBGK": 8,
"novelty": 9,
"feasibility": 4
},
{
"signature": "Frame-number-2adic-integrality-pin",
"statement": "Cyclotomic scheme on mu_n has Frame number F = (q^n times prod of valencies k_i) over (prod of multiplicities m_j), a positive integer. The MCA binding radius s-star(rho) is the smallest agreement dimension s for which the partial Frame quotient Phi_s = (prod of k_i for i<=s) over (prod of m_j for j<=s) first fails 2-adic integrality, i.e. where the 2-adic valuation of the multiplicity product overshoots that of the valency product. Then delta-star = 1 minus sqrt(rho) plus (s-star(rho) minus k(rho))/n exactly, with s-star decided by a divisibility test on integer valencies/multiplicities, p-in",
"mechanism": "The off-Johnson binding rung is pinned by an integrality obstruction: a partial Frame quotient must be a rational integer for the scheme to fuse/quotient cleanly; the first s where the 2-adic valuation of the multiplicity product overshoots the valency product marks the binding radius. delta-star equals Johnson plus (s-star minus k)/n exactly, since both s-star (integrality test) and the +1/n step are integers/rationals, with no asymptotic sqrt-loss.",
"whyNotBGK": "Uses the Frame number, multiplicities m_j and valencies k_i (sizes of eigenspaces and cyclotomic-class cardinalities), and a 2-adic valuation test on their product: an integrality/divisibility, non-archimedean object. The wall is an analytic archimedean magnitude bound on |eta_b|; valuations of integer eigenspace dimensions are a different invariant the magnitude-only archimedean meta-theorem cann",
"notBGK": 8,
"novelty": 9,
"feasibility": 4
},
{
"signature": "Andre-Oort-special-points-pin-deltastar-CM-stratification",
"statement": "Place the family {dyadic RS code at scale 2^\u03bc}_{\u03bc} as a curve/variety C in a moduli/Shimura-type parameter space whose SPECIAL points correspond to scales where the code's agreement-stratification degenerates (extra collinearity / extra codewords). CONJECTURE (Andr\u00e9-Oort form): the parameters \u03bc at which \u03b4*(2^\u03bc,\u03c1) is NOT given by the generic closed form 1 \u2212 \u221a\u03c1 + (g(\u03c1))/n \u2014 i.e. the SPECIAL scales \u2014 are exactly the Andr\u00e9-Oort special points on C, a FINITE set; for all OTHER (generic) scales \u03bc, \u03b4* equals the GENERIC EXACT value \u03b4*(n,\u03c1) = (1\u2212\u03c1) \u2212 (1/log n)\u00b7log(1 + \u03ba(\u03c1)) with \u03ba(\u03c1) a single rational",
"mechanism": "Andr\u00e9-Oort (proven for A_g, Pila-Tsimerman; o-minimal) states the special points (CM points) on a subvariety are a FINITE union of special subvarieties \u2014 an exact, effectively-finite set. The mechanism reframes the SCALE-dependence of \u03b4* as a moduli problem: \u03b4* is a piecewise-algebraic function of the scale parameter that is GENERICALLY constant (in the normalized sense) but jumps at a finite set of arithmetically-special scales (e.g. Fermat-prime-related, where in-tree data already shows anomalies). Andr\u00e9-Oort caps the special scales to a FINITE explicitly-listable set, so for the prize scale \u03bc\u224830 \u2014 provably non-special \u2014 \u03b4* takes its generic closed-form value EXACTLY. This pins \u03b4* by EXCLU",
"whyNotBGK": "The pinning is by a FINITENESS-of-special-points theorem (Andr\u00e9-Oort), which localizes ALL possible anomalous behavior to a finite, listable set of special scales \u2014 orthogonal to bounding any exponential sum at the prize scale, because the argument is that the prize scale is GENERIC and hence carries the generic (BGK-free) closed form by stratification rigidity. It uses the moduli/CM-stratificatio",
"notBGK": 5,
"novelty": 9,
"feasibility": 2
},
{
"signature": "Swan-conductor-jump-at-binding-radius",
"statement": "For each far-frequency b, consider the pullback sheaf F_b = [x -> b x]^* L_chi^{(n)} on G_m, where L_chi^{(n)} is the rank-1 sheaf whose local system encodes the mu_n indicator (a tame Kummer sheaf twisted by the additive character psi via the [n]-pushforward). Define the LOCAL SWAN CONDUCTOR profile s_b(t) = Swan_infinity(F_b \u2297 (twist by the order-t dilation character)) as t runs over the index lattice ZZ/m. CONJECTURE: the binding/saturation index m* of the worst frequency is exactly the smallest t at which the Swan conductor at infinity JUMPS from 0 (tame) to >=1 (wild) under the t-fold dil",
"mechanism": "The worst frequency saturates precisely when the local monodromy at infinity transitions from tame (sqrt-p cancellation holds, agreement stays at capacity) to wild (cancellation degrades, agreement binds). This onset is a ramification-theoretic INTEGER (a break/slope of the local representation), read off from the Hasse-Arf / break-decomposition of the explicit Kummer-pushforward sheaf, NOT from any magnitude estimate. The Swan jump location is exactly m* by the proxy identity; it matches the in-tree onset-threshold phenomenology (the W_r excess is an ONSET-THRESHOLD r0(n), per the MEMORY 'Wr-excess-onset-threshold' entry -- this conjecture geometrizes that empirical onset as a wild-ramifica",
"whyNotBGK": "The Swan conductor is a VALUATION/ramification invariant (a p-adic slope of the local Galois representation), categorically NOT a magnitude. The L-infinity / energy / moment method is provably blind to it: two sheaves with identical |trace| profiles can have different Swan conductors, and conversely the Swan jump is invisible to any sum of |eta_b|^{2r}. This is exactly the 'phase/valuation object ",
"notBGK": 7,
"novelty": 10,
"feasibility": 3
},
{
"signature": "FreqDecoupling-CosetCurvatureModuli",
"statement": "Conjecture (\u2113^2 decoupling on the frequency cosets). Partition the m=(q\u22121)/n cosets b\u00b7\u03bc_n into dyadic blocks indexed by the 2-adic valuation v_2(ind(b)) of the discrete log of b (the FRI/STARK valuation filtration). For a smooth weight w on F_q define the frequency-extension operator E_freq g (x) = \u03a3_b g(b) \u03b7_b e_p(\u2212bx). HYPOTHESIS: the curve b\u21a6\u03b7_b, as b ranges over a single \u03bc_n-coset of the multiplicative group, has NONVANISHING discrete curvature in the sense that {(b, \u03b7_b, \u03b7_{b\u00b2},\u2026, \u03b7_{b^{\u2113}})} is in 'general position' (the frequency field is a NONDEGENERATE algebraic curve of degree O(n) i",
"mechanism": "Decoupling on the frequency curve converts the m-fold sup into a block-orthogonal \u2113^2 sum over O(log m) dyadic valuation blocks, each of size controlled by curvature. Because the curve is nondegenerate (curvature input), the blocks are nearly orthogonal and the sup is forced to the \u221a(n\u00b7#blocks)=\u221a(n log m) scale with EXACT constant 1 (not C), pinning \u03b4* exactly at the window edge 1\u2212\u03c1\u2212\u0398(1/log m). The valuation filtration supplies the dyadic scales that the FLAT period side lacked.",
"whyNotBGK": "The repo's no-go explicitly states decoupling is dead on the PERIOD side because \u03bc_n is 0-dimensional/flat (no curvature, wrong norm: decoupling outputs L^{2r} moments). Here decoupling is applied to the FREQUENCY field b\u21a6\u03b7_b, which is NOT 0-dimensional: as b ranges over a coset it traces an honest degree-O(n) algebraic curve in C^{\u2113+1} with nonvanishing discrete curvature. The decoupling output i",
"notBGK": 8,
"novelty": 9,
"feasibility": 3
}
];

const FRAME = `THE PROBLEM (#444): prove delta* (mutual-correlated-agreement / list-decoding threshold) EXACTLY for
explicit dyadic Reed-Solomon codes, window interior (1-sqrt(rho), 1-rho-Theta(1/log n)), prize regime
n=2^mu~2^30, q=n^beta (beta~4-5 Burgess barrier), eps*=2^-128. Repo ${REPO}.

THE PROVEN STATE: delta* is bracketed [1-sqrt(rho) Johnson, (1-rho)-Theta(1/log n) KKH26] and reaches the
window INTERIOR <=> the char-p BGK/Paley floor M(n)=max_{b!=0}|Sum_{x in mu_n}e_p(bx)| <= C*sqrt(n log m)
(= char-p Lam-Leung energy A_r<=(2r-1)!!n^r at r~ln q). char-0 closed; char-p transfer = the open prize =
the 25-year-open BGK wall. The far-line proxy -> Johnson (Plotkin lower envelope). META-THEOREM: any winning
method must be SIMULTANEOUSLY (a) b-sensitive, (b) deterministic-archimedean (periods exchangeable
white-noise Cov=-Var/(m-1), kills probabilistic-EVT), (c) genuinely L-infinity (sup not RMS). Dead ledger:
every moment/energy/2nd-order/Stepanov/discriminant/spectrum/sum-product route reduces to or caps below it.

YOUR JOB: ADVERSARIALLY ATTACK a candidate conjecture via ONE lens. DEFAULT TO KILLING IT. These are novel
FRAMINGS; the prior (79+ prior conjectures, 0 survivors) is that each secretly reduces to the BGK wall, to
Johnson, or is false. Be RIGOROUS and CONCRETE: trace an explicit reduction chain, cite an in-tree proven
fact, or give a machine-checkable countermodel. If after a genuine hard attempt you CANNOT kill it, say
SURVIVES and state precisely what blocks the kill (a valuable, rare outcome).`

const SCHEMA = {
  type:'object', additionalProperties:false, required:['signature','lens','outcome','reason'],
  properties:{
    signature:{type:'string'}, lens:{type:'string'},
    outcome:{type:'string', enum:['REDUCES-TO-BGK','REDUCES-TO-JOHNSON','REFUTED-FALSE','SURVIVES','SURVIVES-PARTIAL']},
    reason:{type:'string'},
  },
}
const LENSES = [
  {k:'reduce-BGK', p:`LENS [reduce-to-BGK]: trace an EXPLICIT reduction to the BGK/energy wall M<=C sqrt(n log m) / A_r<=(2r-1)!!n^r. Does proving it REQUIRE or IMPLY the char-p sqrt-cancellation? Show the chain step by step. If the pinning device ultimately needs to bound/count the same Gauss-period sup-norm or additive-energy/Spur_r object, it REDUCES-TO-BGK. Be specific WHERE the wall re-enters.`},
  {k:'reduce-Johnson', p:`LENS [reduce-to-Johnson]: show it only reaches JOHNSON / the far-line Plotkin proxy (delta*->1/2 lower envelope, or caps at 1-sqrt(rho)), NOT the interior. Does its mechanism pin only the over-det/proxy count (O(n), p-indep, -> Johnson) not the true interior value? If its exact value is the Johnson-locked proxy, REDUCES-TO-JOHNSON.`},
  {k:'countermodel', p:`LENS [countermodel]: REFUTE it FALSE. Find a machine-checkable countermodel: exact small-n F_p computation contradicting its claimed value/structure, contradiction with an in-tree PROVEN fact (dead ledger / meta-theorem / white-noise period covariance), a vacuity (unsatisfiable hypothesis), or a wrong-direction error (e.g. height = lower bound not the needed upper bound). If false/vacuous, REFUTED-FALSE with the explicit countermodel.`},
]
function sig(s){ return (s||'').toLowerCase().replace(/[^a-z0-9]+/g,'-').replace(/^-|-$/g,'').slice(0,50) }
function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, sz){
  let acc=[]
  for (const [i,w] of chunk(items,sz).entries()){
    log(`Refute wave ${i+1}/${Math.ceil(items.length/sz)} (${w.length} attacks)`)
    acc=acc.concat(((await parallel(w.map(it=>()=>mk(it))))||[]).filter(Boolean))
  }
  return acc
}
phase('Refute')
const jobs = CONJ.flatMap(c => LENSES.map(L => ({c, L})))
log(`Attacking ${CONJ.length} conjectures x ${LENSES.length} lenses = ${jobs.length} attacks`)
const attacks = await waved(jobs, ({c,L}) => agent(
  `${FRAME}

CANDIDATE CONJECTURE:
  signature: ${c.signature}
  statement: ${c.statement}
  mechanism: ${c.mechanism}
  whyNotBGK (author's claimed orthogonality - DISPROVE it): ${c.whyNotBGK || '(none)'}

${L.p}`,
  {label:`refute:${sig(c.signature).slice(0,22)}-${L.k}`, phase:'Refute', schema:{...SCHEMA}}
), 6)
phase('Synthesize')
const byConj = new Map(CONJ.map(c => [sig(c.signature), {c, atk:[]}]))
for (const a of attacks.filter(Boolean)) {
  let e = byConj.get(sig(a.signature))
  if (!e) { for (const [k,v] of byConj) if (k.startsWith(sig(a.signature).slice(0,18)) || sig(a.signature).startsWith(k.slice(0,18))) { e=v; break } }
  if (e) e.atk.push(a)
}
const ledger = [...byConj.values()].map(({c, atk}) => {
  const kill = atk.find(a => ['REDUCES-TO-BGK','REDUCES-TO-JOHNSON','REFUTED-FALSE'].includes(a.outcome))
  const survives = atk.length>0 && atk.every(a => a.outcome.startsWith('SURVIVES'))
  return {
    signature: c.signature, notBGK: c.notBGK, novelty: c.novelty, feasibility: c.feasibility,
    statement: c.statement, mechanism: c.mechanism,
    verdict: kill ? kill.outcome : (survives ? 'SURVIVES' : 'MIXED'),
    killLens: kill ? kill.lens : null, killReason: kill ? kill.reason : null,
    attacks: atk.map(a=>({lens:a.lens, outcome:a.outcome, reason:(a.reason||'').slice(0,300)})),
  }
})
const tally={}; for(const l of ledger) tally[l.verdict]=(tally[l.verdict]||0)+1
log(`refute25 done: ${JSON.stringify(tally)}`)
return { count: CONJ.length, tally, ledger }
