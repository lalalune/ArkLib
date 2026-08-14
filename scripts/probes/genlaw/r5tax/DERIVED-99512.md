# The r=5 stratum at s=32 is structurally derived: 99,512 = Σ C(v,(14−h)/2) over a proven axis alphabet — parity-purity is a theorem, the engine is s-uniform to N₅(64) and N₇(64) EXACTLY, and it predicts the s=128 rungs

Lane `nubs/issue232-effective-pa`. Two passes, mutually verifying: **v1** (2026-06-10,
raw-frame engine `analyze.py`/`structure.py`, §§1–7 + appendix below) and **v2**
(2026-06-11, independent re-derivation in canonical φ-coordinates with a σ-rank engine
that never enumerates sign-vectors, §§8–12). The two passes were written independently
against the same audit ground truth (`rec5.txt` ≡ `rec32r5.txt`, byte-identical audit
DP records) and agree on every overlapping number: per-class (h, forced-set, v,
free-set, ways) equality on all 11,808 classes, identical (h,v) census, strata, ε-split,
E5 census, B-injectivity. The exact analogue of `../n32census/level2/DERIVED-672.md`
(the O108 engine) for the r=5 stratum discovered in O130 (`RESULTS-GENERAL-LAW.md` §4).

**Headline upgrades over the O130 charts** (which were "charted, not derived"):

1. **Parity purity is now a THEOREM for r=5 at every 2-power s** (was
   `parity_pure_empirical`). The r=3 proof does break — two odd products *can* be
   antipodal across 4 distinct fibers — but a matching/3-cycle argument closes every
   mixed parity class (L1′, §2; machine-checked: 3.15M mixed sign-classes, zero
   odd-balanced).
2. **The complete axis alphabet is PROVEN**: exactly 6 live non-z\*-axis types and
   exactly 10 live z\*-axis types; everything else is dead by lemma. This *derives* the
   L3-break (products reach the −z\* fiber in exactly two z\*-axis patterns, BP|LP and
   LP|OP, 2,496 + 288 = 2,784 classes), "E6 only at slot s/2", and the z\*-type ⟶
   stratum bijection behind the 11-entry table.
3. Given the (enumerated) node census, **all four target charts are derived by
   structural counting, not re-enumeration**: 99,512 ways, the ε split 49,768/49,744,
   the E5 census {0: 3,768, 1: 7,880, 2: 160}, and the 11-entry z\*-strata table.
4. **The engine is s-uniform and r-uniform** (§11): one canonical-frame kernel
   reproduces C19's 8, DERIVED-672's 672 *including its 304/368 ε-split*, 764,544 (r=3,
   s=32), the level-4 anchors N₃(64) = 244,593,584,640 and — the blind gates —
   **N₅(64) = 141,450,979,280 (2,212,000 classes) EXACTLY** and
   **N₇(64) = 1,586,840,480 (3,300,096 classes) EXACTLY**; the latter is pure-only,
   so **parity purity at r=7, s=64 is now an enumerated fact** (it was unknown). New
   theorem-grade predictions: N₃(128) and N₅(128) (§11).
5. A new **axis-parity pigeonhole** (E-par, §10) partially explains v1's residual #1:
   every feasible class carries an even-axis collision (≥ 2 at ε=0), killing all five
   lone-event node families at ε=0 and the lone-E3 family at both parities.

Dialect note (closes RESULTS-GENERAL-LAW caveat 5 for this doc): v1 (§§1–7) speaks the
raw frame — slots 2c | 2c+32, z\*-axis c = 8, letters O/P/L per slot 16|48. v2 (§§8–12)
speaks the canonical φ-frame — axes Z₁₆, sides 0/1, events DD/DP/PP/DPP. The mapping is
the π-shift of §8; both name z\*-types identically (P|L, OP|LO, …), and E1/E5/E6/E7/E8 =
DD / PP-opposite / PP-same / DP / D-in-DPP respectively.

## 1. Setup and reduction (cited theorem, all odd r)

s = 32, n = 64, H = μ₆₄, z\* = ζ₆₄¹⁶, w = X³⁴ − z\*X³², code = RS degree < 32. Marginal
(agree-33) elements have fiber pattern (b, r) = (14, 5):
e = Π₁₄(X² − z_b) · (X − x₁)⋯(X − x₅)(X − ξ), ξ = −Σxᵢ, xᵢ² = z_{oᵢ}, oᵢ ∈ O distinct.
By the general reduction (RESULTS-GENERAL-LAW §2, theorem for every odd r ≥ 3, machine-
asserted), consistency ⟺ **antipodal balance** (cnt[t] = cnt[t+32] in ζ₆₄-exponents,
the 2-power Lam–Leung principle, in-tree as `LamLeungTwoPow.vanishing_iff_antipodal_coeffs`
/ `LamLeungMultisetAntipodal.multiset_antipodal_iff`) of the **30-term multiset**

  {aᵢ+aⱼ : i<j}  (10 products) ⊎ {2oᵢ} (5) ⊎ {2b : b ∈ B} (14) ⊎ {48}  (the −z\* slot),

aᵢ ∈ {oᵢ, oᵢ+32}. L4 (ξ ∉ μ₆₄ ∪ {0}) holds for all odd r (cited), so balance is exact
agreement 33, and global negation x⃗ ↦ −x⃗ acts freely: **elements = 2 × classes**.
Fibers pair into 16 axes {c, c+16}, c ∈ [0,16); axis c owns slots 2c (light) and 2c+32
(heavy); the z\*-axis is c = 8 (slots 16 | 48), and the λ-term sits at 48 = heavy.

## 2. Lemma ledger

Grades: [P] proven char-0 (s-independence noted), [P-m] proven by machine-asserted exact
finite check (char-0 combinatorics, same epistemic grade as the dual-B census in
DERIVED-672), [E] enumerated census (exact, but no derivation).

**L0 (placement rule) [P, all s, all r].** Fix (O, mask) and let Δ_c = (light − heavy)
count of the 16 non-B terms on axis c. A B-set balances iff per axis
B_light − B_heavy = −Δ_c with B ∈ {0,1} per fiber and B ∩ O = ∅. Hence: |Δ_c| ≤ 1;
Δ_c = ±1 forces one B on the light(er) side, dead if that fiber ∈ O; Δ_c = 0 admits 0 B,
or both fibers iff the axis is O-free. With h = #forced axes, v = #(Δ=0, O-free,
pair-available) axes: **ways = C(v, (14−h)/2)**. Equivalently in occupancy terms: an
axis with t terms is live iff its side-split is (t/2, t/2) [Δ=0] or ((t±1)/2) [forced];
v counts the balanced O-free axes (including empty ones).

**L0′ (h parity) [P].** Δ_c ≡ t_c (mod 2) and Σt_c = 16 ⟹ h = #{odd-t axes} is even;
14 − h ≡ 0 (mod 2) always. (General r: Σt = C(r+1,2)+1 ≡ b (mod 2) automatically.)

**L0″ (criticality at s=32, r=5) [P].** 16 non-B terms on 16 axes: the generic
(coincidence-free) configuration has all t_c = 1, h = 16 > 14 ⟹ dead. **Every live
class contains coincidences** (≥ 2 even-t axes). This is the qualitative difference from
r=3 (7 terms, 8 axes, generic live) and from s=64 r=5 (16 terms, 32 axes, generic live —
which is why N₅(64) explodes to 2,212,000 classes).

**L1′ (parity purity) [P, all 2-power s].** O is parity-pure. *Proof.* Odd slots are hit
only by products xᵢxⱼ across the parity split (k odd-parity fibers, 5−k even): k(5−k)
terms, which must self-balance into antipodal pairs. A pair sharing an index dies
(xᵢxⱼ = −xᵢxₗ ⟹ xⱼ = −xₗ ⟹ z_j = z_l, same fiber), so pairs are disjoint.
k = 1, 4: K₁,₄ — all 4 edges share the hub, no disjoint pair, 4 ≠ 0 terms ⟹ dead.
k = 2, 3: K₂,₃ — a perfect antipodal matching of the 6 edges pairs (u₁,w) with
(u₂,π(w)), π a fixed-point-free permutation of 3 letters, i.e. a 3-cycle. Multiplying
the three relations: x_{u₁}³ · (y_a y_b y_c) = −x_{u₂}³ · (y_a y_b y_c) ⟹
(x_{u₁}/x_{u₂})³ = −1 ⟹ x_{u₁}/x_{u₂} = −ω with ω³ = 1; μ_{2^{j+1}} has no 3-torsion,
so ω = 1, x_{u₁} = −x_{u₂} ⟹ same fiber. ∎ (Uses only gcd(3, 2-power) = 1; fully
s-independent. The corresponding general-r statement remains open — the matching
structure for r ≥ 7 is richer than a forced 3-cycle; see §11 for the r=7, s=64
enumerated resolution.)
*Corollary:* all 10 products land on even slots; the engine may enumerate the 2·C(16,5)·16
= 139,776 parity-pure configs only. Gates: exact class-set equality with the full audit
sweep over all C(32,5)·16 configs ✓; additive machine check (`purity_check.py`): all
68,096 (s=16) + 3,082,240 (s=32) mixed-parity sign-classes fail odd-balance alone ✓.

**L2′ (shared-index lemma) [P, all s, r].** Two products sharing an index are never
equal or antipodal (either forces z_j = z_l for distinct fibers). *Corollaries:*
(i) **E5 is impossible at r=3** — any two of the three products share an index; this is
the turn-on mechanism of the r=5 phenomenology. (ii) Every product–product coincidence
(equal = E6, antipodal = E5) involves 4 distinct fibers.

**L2″ (own-index lemma) [P].** A product on an O-term's axis-slot pair
(aᵢ+aⱼ ≡ 2o_m or 2o_m+32) cannot involve index m (else a_j ≡ a_m (+32), same fiber).

**L2‴ (≤ 2 products per axis) [P at r=5].** Three products on one axis: two share a slot
(pigeonhole), forming an E6 over 4 distinct fibers (L2′); the third would need a pair
disjoint from both — a 6th index — impossible at r=5; sharing dies by L2′. ∎

**L3-break mechanism [P, given the alphabet]** — see §3/§4: a product reaches slot 48
only inside the two z\*-axis types P|LP and OP|LP. r=3's L3 fails exactly because r=5
has enough products to pay for the required slot-16 compensation.

**L5′ (E6 location: same-slot product pairs occur ONLY at slot 16) [P].** An E6 pair
contributes ±2 on its slot; |Δ| ≤ 1 needs 1-or-2 compensating terms on the opposite
slot with specific Δ. Opposite-slot candidates: a product (⟹ 3 products on the axis,
dead by L2‴); an O-term (Δ = +1 ⟹ forced B on the O-term's own fiber, dead by L0);
both O-terms impossible (same fiber). Only the λ-term survives: E6 at 16, L at 48
(Δ=+1, forced B on fiber 24 — type PP|L) or E6 at 16, L+O₂₄ at 48 (Δ=0 — type PP|LO).
E6 on slot 48 itself dies (≥3 products or |Δ| ≥ 2). ∎  Census check: e6 classes
928 = PP|L 880 + PP|LO 48 ✓ exact.

**L5″ (E1-axis exclusivity) [P].** An axis carrying an antipodal O-pair (E1) carries
nothing else: an extra product makes Δ = ±1 with the forced B landing on an O-fiber
(dead by L0); two extra products die by L2‴/6-index counting (an ('OP','OP') axis needs
4+2 = 6 distinct indices). [v2 adds the geometric form, Lemma X §9: an E1 axis can
never even *geometrically* host two disjoint products at r=5 — 0 occurrences in all
4,368 U-sets.]

**L6′ (two-E1 forcing) [P].** Two E1 pairs {x_u, x_{u+16}}, {x_w, x_{w+16}} force, among
their four cross products, **exactly one E5 pair and one E6 pair** (the sign options
δ₁, δ₂ ∈ {±16} in a_{·+16} = a_· ± 16 give either {same slot, 32 apart} or
{32 apart, same slot}). With L5′, the forced E6 sits at slot 16 — hence every q=2 class
has z\*-type PP|L or PP|LO. Verified: all 152 q=2 classes satisfy e5 ≥ 1 ∧ e6 ≥ 1, and
the q=2 node rows are exactly the PP|L / PP|LO ones (32+96+16+8 = 152) ✓.

**L7 (E5 pair structure) [P-m + P].** An E5 relation is u·a ≡ 32 (mod 64) with
u = eᵢ+eⱼ−eₖ−eₗ (15 such vectors at r=5). Hand lemmas: shared-pair double-E5 dies
(remaining 3 indices force a repeated fiber); two E5 relations omitting the same index
die (u±u′ = 2(eᵢ−eⱼ) ⟹ aᵢ ≡ aⱼ (mod 32)). Machine-asserted finite check
(`e5max_proof.py`): of the 105 relation pairs exactly 60 are admissible — **all with
distinct omitted indices** — matching the data: all 160 e5=2 classes omit distinct
indices ✓.

**L7′ (e5 ≤ 2) [E — sharp, with the obstruction located].** The kill-rule system of L7
does NOT close the bound: 80 of 455 relation triples survive the linear kills and 60 of
those are genuinely satisfiable with distinct fibers and parity purity
(`e5triple_sat.py`, e.g. a = (0,4,60,30,2)). The bound is a *liveness* phenomenon:
sweeping ALL 139,776 parity-pure configs, the e5 census is {0: 74,880, 1: 54,912,
2: 9,600, 3: 384} — e5 = 3 configs exist, and **all 384 die on an axis with |Δ| ≥ 2**;
e5 ≥ 4 never occurs (`nodes_and_e5scan.py`). So "e5 ≤ 2 in live classes" is exact but
enumerated; a derivation must couple the relation system to the balance bookkeeping.

**L8 (ε mod-4 lemma) [P, all 2-power s].** O-terms sit at 2o ≡ 2ε (mod 4); the z\*-axis
slots s/2, 3s/2 ≡ 0 (mod 4). Hence **O-fibers reach the z\*-axis only at ε = 0** —
the six z\*-types containing an O (O|L, OP|L, P|LO, OP|LO, OP|LP, PP|LO) are ε=0-pure
(2,992 classes), as is their strata image. Verified exactly (node table ε columns).

**L9 (B-injectivity / multiplicity menu) [E, verified here].** Expanding every class's
C(v,k) B-completions: 99,512 distinct B-sets, **zero duplicates** — B determines
(O, mask). With free negation this gives elements = 199,024 with B-multiplicity menu
{2}, i.e. `dual_B = 0`: the r=3 dual-B mechanisms (share-2 / disjoint) do not fire at
r=5. (Structural reason: open; at r=3/s=64 the menu is {2,4}.)

## 3. The event taxonomy (complete, with proven location constraints)

Elementary coincidence relations between non-B terms:

| event | relation | where it lives (proven) |
|---|---|---|
| E1 | antipodal O-pair {o, o+16} ⊂ O | its own axis, type ('O','O'); exclusive (L5″); on the z\*-axis = {8,24} ⊂ O → OP|LO |
| E5 | product–product antipodal | a free ('P','P') axis, or inside T6, or z\*: P|LP, OP|LP; 4 distinct fibers (L2′) |
| E6 | product–product same slot | **slot 16 only** (L5′): PP|L, PP|LO |
| E7 | product–O antipodal | ('O','P') balanced O-axis; on z\*: O₂₄+P = P|LO, O₈+P… see OP types |
| E8 | product–O same slot | only inside T6 ('OP','P') or z\* types OP|L, OP|LO, OP|LP |
| E3 | product at slot 16 (antipodal to λ) | z\* types P|L, OP|L, PP|L(×2), P|LP, OP|LP, PP|LO(×2) |
| E3′ | product at slot 48 (**L3 break**) | z\* types P|LP, OP|LP only |
| E4 | 8 ∈ O (O-term at 16) | z\* types O|L, OP|L, OP|LO, OP|LP; ε=0 only (L8) |
| E4′ | 24 ∈ O (O-term at 48) | needs compensation: P|LO, OP|LO, PP|LO; ε=0 only (L8) |

**T6 anatomy [P].** A ('OP','P') axis is the compound relation
x_ix_j = z_m = −x_kx_l with {i,j,k,l,m} = all five indices (L2″ forces m out of both
pairs; 5 indices leave exactly the partition). It carries one E8, one E8′ (antipodal
product–O), and one E5 — three pair-relations on one axis.

**Identities [P, verified 0/11,808 violations].** With node vector
(a, q, p5, f3, z8) and per-axis letters P8/O8 on the z\*-axis:
  np + a + 2·p5 + 2·f3 + P8 = 10   (products),
  no + a + 2·q + f3 + O8 = 5     (O-terms),
  E0 = 15 − (np+no+a+q+p5+f3)    (empty axes),
  **h = np + no + f3 + [z\*-axis odd-t]**, **v = E0 + p5 + [z\* = P|L]**,
  **ways = C(v, (14−h)/2)**,
  **e5 = p5 + f3 + [z8 ∈ {P|LP, OP|LP}]**, **e6 = [z8 ∈ {PP|L, PP|LO}]**.

### The complete axis alphabet [P]

Non-z\* axes — exactly 6 live types + empty (all others dead by L0/L2′/L2‴/L5′/L5″):

| type | letters | Δ | role | inventory (class-weighted) |
|---|---|---|---|---|
| T1 | ('','P') | ±1 | forced | 81,600 |
| T2 | ('','O') | ±1 | forced | 25,728 |
| T3 | ('O','P') | 0 | E7, p0 | 12,800 |
| T4 | ('O','O') | 0 | E1, p0 | 8,048 |
| T5 | ('P','P') | 0 | E5, **free** | 6,360 |
| T6 | ('OP','P') | ±1 | E8+E8′+E5, forced | 1,200 |

z\*-axis (slot 16 | slot 48 ∋ L) — exactly 10 live types; the full case analysis over
occupancies {O₈?, O₂₄?, ≤2 products, L} shows every other candidate dies:
-|LP and -|LO (Δ=−2); O|LP, O|LO, O|LOP, OP|LOP (forced B on fiber 8 ∈ O);
PP|LP, P|LOP and all 3-product types (L2‴); OO-types (same fiber). **All 10 live
candidates are realized** — the alphabet is tight in both directions.

| z\* type | Δ | B action | → stratum | classes | ways | ε0/ε1 |
|---|---|---|---|---|---|---|
| P|L  | 0 | **free**: pair ↔ no pair | BL\|BP / L\|P | 3,680 | 22,720 + 23,024 | 1152/2528 |
| -|L  | −1 | forced B₈ | B\|L | 3,680 | 14,208 | 1024/2656 |
| OP|L | +1 | forced B₂₄ | BL\|OP | 944 | 12,032 | 944/0 |
| PP|L | +1 | forced B₂₄ (E6!) | BL\|PP | 880 | 10,896 | 368/512 |
| O|L  | 0 | none (E4) | L\|O | 1,136 | 7,264 | 1136/0 |
| P|LO | −1 | forced B₈ (E4′) | BP\|LO | 576 | 4,480 | 576/0 |
| P|LP | −1 | forced B₈ (**L3 break**) | BP\|LP | 576 | 2,496 | 352/224 |
| OP|LO | 0 | none (E1 on z\*!) | LO\|OP | 224 | 1,600 | 224/0 |
| PP|LO | 0 | none (E6+E4′) | LO\|PP | 48 | 504 | 48/0 |
| OP|LP | 0 | none (**L3 break**) | LP\|OP | 64 | 288 | 64/0 |

## 4. The counting engine and the derived charts

**(b) 99,512 ways.** The (h,v) joint census (13 cells, enumerated) + L0:

| h | v | classes | C(v,k) | ways |
|---|---|---|---|---|
| 6 | 6 | 336 | 15 | 5,040 |
| 6 | 7 | 56 | 35 | 1,960 |
| 8 | 4 | 608 | 4 | 2,432 |
| 8 | 5 | 1,368 | 10 | 13,680 |
| 8 | 6 | 1,312 | 20 | 26,240 |
| 8 | 7 | 80 | 35 | 2,800 |
| 10 | 3 | 768 | 3 | 2,304 |
| 10 | 4 | 2,640 | 6 | 15,840 |
| 10 | 5 | 2,048 | 10 | 20,480 |
| 10 | 6 | 80 | 15 | 1,200 |
| 12 | 3 | 1,936 | 3 | 5,808 |
| 12 | 4 | 384 | 4 | 1,536 |
| 14 | 2 | 192 | 1 | 192 |

Crossfoot: classes 11,808 ✓, **ways 99,512** ✓ (= audit waysum, exact). h is even (L0′),
h ∈ [6,14]: ≥ 1 coincidence is forced (L0″) and at most 5 pair-events fit (the richest
realized nodes have h = 6).

**(d) The z\*-strata table is the image of the z\*-type census under L0** — no
B-enumeration: forced/p0 types map their full Σways to one stratum; the unique free type
P|L splits per class as C(v−1,k−1) (take the axis-8 pair → BL|BP) + C(v−1,k) (don't →
L|P). Result (table above): **23,024 / 22,720 / 14,208 / 12,032 / 10,896 / 7,264 /
4,480 / 2,496 / 1,600 / 504 / 288** — all 11 entries equal the audited chart, crossfoot
99,512 ✓. The five new-at-r=5 slot types (BL|PP, BP|LP, LO|OP, LO|PP, LP|OP) are exactly
the E6 / L3-break / z\*-E1 / E6+E4′ / double-L3 rows — each now has a mechanism, and the
L3-break total is 2,496 + 288 = **2,784** classes as charted.

**(c) ε split and E5 census.** Summing the node-table ε columns with per-node ways:
**ε0 = 49,768, ε1 = 49,744** ✓ exact (classes split the other way: 5,888 / 5,920 —
ε0 wins on ways because the six ε0-pure O-on-z\* types (L8) carry above-average v).
The E5 census follows from the e5 identity (§3): e5 = 2 ⟺ p5 = 2 (160 classes — all
three p5=2 nodes carry z8 = OP|L, an enumerated curiosity), e5 = 1 ⟺ exactly one of
{p5, f3, z\*-E5} (7,880), else 0 (3,768) ✓ exact.

**(a) 11,808 classes.** Status: **derived down to the node census, which is
enumerated.** The alphabet (proven) + bookkeeping identities admit 451 abstract node
vectors; 70 are realized (Appendix). Closed-form anchors checked en route: the
parity-pure O-universe is 2·C(16,5) = 8,736 with E1-pair census per parity
C(8,p)·C(8−p,5−2p)·2^{5−2p} = 1,792 / 2,240 / 336 (p = 0,1,2); live O-sets: 3,886, with
live-mask multiplicities {1: 400, 2: 1,852, 3: 16, 4: 1,302, 6: 88, 8: 204, 12: 24}
(crossfoot 11,808 ✓). A genuinely closed-form 11,808 was not reached — consistent with
the general-law caveat that per-s censuses are irregular (the same boundary DERIVED-672
hit at its ε=0 "38 live + 18 dead" cell).

## 5. What transfers beyond s = 32 (char-0 generality)

s-independent at r=5: the reduction (cited), L0/L0′, L1′ (parity purity — **new
theorem**), L2′/L2″/L2‴, L5′/L5″/L6′, L8, and hence the **entire axis alphabet** (6+10
types). s=32-specific: criticality L0″ (16 terms = 16 axes) and every census number.
At s = 64 the same alphabet applies with 32 axes — generic configs are live there, so
the N₅(64) = 2,212,000 census should be attackable as "alphabet + sparse placement"
with coincidences as corrections rather than as the survival condition — §11 confirms
the engine transfers EXACTLY. The r ≥ 7 exclusion at s=32 also gets a structural frame:
r=7 has C(8,2)+7+1 = 29 terms on 16 axes with b = 13, so liveness needs coincidence
mass c ≥ 8 under the same alphabet — a max-coincidence bound, not a sweep, is the
natural exclusion theorem (left to #334).

Effective transfer: every non-solution's 30-term sum is a nonzero α ∈ ℤ[ζ₆₄] with
power-basis coefficient sum-of-squares ≤ 900, so N(α) ≤ 900^{16} < 2^{158}
(E1 norm bound at m = 64). For split primes p > 2^{158} the census holds verbatim
mod p; practical primes rest on the audited spot checks (12/12 r=5 constructive
BabyBear samples agree exactly 33, per FORECAST_n64.json).

## 6. Honest residuals

1. **The node census (hence 11,808) is enumerated**, not derived; 381 of 451
   bookkeeping-admissible vectors are empty for arithmetic reasons beyond the lemmas.
   *v2 upgrade (§10):* the axis-parity pigeonhole E-par now PROVES emptiness of all
   five lone-pair-event families at ε=0 and of lone-E3 at both parities; the ε=1
   lone-E1 / lone-E5(even-axis) / lone-E7 families remain enumerated-empty (the
   even-axis bound is tight there), still smelling like one more invariant.
2. **e5 ≤ 2 is enumerated** (sharp form in L7′: the 384 e5=3 configs all die |Δ|≥2;
   the linear kill-system provably cannot close it).
3. ε-split closed form (the 24-ways gap) not derived; per-stratum ε purity is proven
   (L8) but the mixed rows' splits are enumerated.
4. dual_B = 0 (menu {2}) is verified by exhaustive B-expansion, but the structural
   reason r=5 lacks the r=3 share-2/disjoint mechanisms is open.
5. All p5=2 classes have z\*-type OP|L (enumerated curiosity, unexplained).
6. L1′ is proven for r=5 only; general odd r needs the full antipodal-matching
   classification (the 3-cycle trick is r=5-specific). At (r,s) = (7,64) purity is now
   enumerated-true (§11); a proof remains open.
7. Char-0 statements throughout; see §5 for the transfer boundary. The s=128 numbers
   in §11 are theorem-grade computations of the proven criterion but have no
   independent enumeration yet (falsifier: `audit_sweep64.c`-style sweep at s=128,
   ~4.2×10⁹ configs for r=5).

## 7. Calibration gates (all EXACT, no tolerance)

| gate | structural engine | audit enumerator | status |
|---|---|---|---|
| s=16 r=3 (O108 anchor) | 672 (304/368 by ε, §11) | 232 classes / 672 ways | ✓ reproduces DERIVED-672 incl. ε-split |
| s=32 r=3 (O130 anchor) | 764,544 (373,440/391,104) | 3,304 / 764,544 | ✓ incl. ε-split |
| s=32 r=5 class set | 11,808 parity-pure | 11,808 (full sweep) | ✓ exact set + per-class (h,forced,v,free,w) equality |
| ways | 99,512 | 99,512 | ✓ |
| ε split (ways) | 49,768 / 49,744 | chart | ✓ |
| E5 census | 3,768 / 7,880 / 160 | chart | ✓ |
| strata (11 entries) | §3/§4 tables | chart | ✓ all |
| B-injectivity | 99,512 distinct, 0 dup | `distinct_B` 99,512 | ✓ |
| identities / e5+e6 identities | 0 violations / 11,808 | — | ✓ |
| v1 engine ≡ v2 engine | per-class, per-node | byte-identical rec files | ✓ (independent implementations) |
| s=64 / s=128 rungs | §11 battery | level-4 anchors | ✓ N₃(64), N₅(64), N₇(64) exact |

---

# PART II — v2 extensions (canonical frame, σ-law, s-uniformity, new lemmas)

## 8. The canonical φ-frame [P]

By L1′ write oᵢ = 2uᵢ + π, π ∈ {0,1} (ε = π's complement-free name: ε0 ⟺ π=0 even O),
aᵢ = oᵢ + 32mᵢ, ψᵢ := (aᵢ − π)/2 = uᵢ + 16sᵢ ∈ Z₃₂, sᵢ = mᵢ. Halving the (all-even)
exponents maps balance to fiber space Z₃₂ with axes Z₁₆, antipode = +16. The 16 non-B
terms become, with γᵢⱼ = [uᵢ+uⱼ ≥ 16] (reps in [0,16)), ρᵢ = [uᵢ ≥ 8], λ = 8 − π:

| term | axis (Z₁₆) | side | s-dependence |
|---|---|---|---|
| double Dᵢ (= O-fiber slot) | 2uᵢ mod 16 | ρᵢ | none |
| product Pᵢⱼ | uᵢ + uⱼ mod 16 | γᵢⱼ ⊕ sᵢ ⊕ sⱼ | affine |
| Λ (the −z\* term) | λ = 8 − π | 1 | none |

Classes ⟷ (π, U = {u₁<…<u₅} ⊂ Z₁₆, s ∈ GF(2)⁵, s₁ = 0): the global flip is global
negation, already quotiented. **The parity enters only through λ = 8 − π** — the whole
ε-mechanism in one line: at π=1 the λ-axis is odd, so no O-double (2u ≡ 7 impossible)
ever reaches it (= L8), and the PΛ pairing {u, 7−u} has 8 pairs vs 7 pairs + 2 fixed
slots {4,12} at π=0 (§9 C2/C3). Signature alphabet (off-λ): DD:b = E1, DP:b = E7
(must balance — same-side is Δ=±2 dead), PP:b = E5 (same-side dead off-λ), DPP:f± = T6
(forced mixed pattern, B opposite the O-side, always carries an E5). λ-axis: the 10
types of §3. The σ-law: all side conditions are affine in s ∈ GF(2)⁵/⟨1⟩ ≅ GF(2)⁴, so
each (U, resolution) contributes **σ = 2^{4−rank}** sign-classes (Gaussian elimination,
0 if inconsistent). `deriv.py` implements the count with NO sign enumeration and NO
placement DP: per-(π,U) and per-node agreement with the sign-enumerating chart and the
audit DP is exact (0 mismatches; 3,886 geometries, 107 φ-frame node signatures —
the 70 raw-frame nodes of the Appendix refine to 107 when keyed by (π, λ-sig, exact
off-λ event multiset); both crossfoot 11,808 / 99,512).

**Node accounting (Lemma A) [P].** With X = Σ(t_c − 1) over occupied axes (= #empty
axes), F = #multi-axes with Δ = 0, G = #multi-axes with Δ = 0 and no O-fiber:
h = 16 − X − F, v = X + G, k = (X + F − 2)/2, ways = C(X+G, (X+F−2)/2). Verified on all
11,808 classes, 0 violations. Feasibility needs X + F ≥ 18 − m (m = #axes): ≥ 2 at
m = 16 (= L0″), vacuous at m ≥ 32, ≥ 10 at m = 8 (with only 8 axes for 16 terms —
N₅(16) = 0, machine: the finer constraints kill everything; no hand proof claimed).

## 9. Closed-form censuses [P] and the geometric exclusion

**C1 (E1 pairs {u, u+8}) and C2 (π=1 PΛ pairs {u, 7−u}):** both are perfect pairings of
Z₁₆ ⟹ #U with exactly j pairs = C(8,j)·C(8−j, 5−2j)·2^{5−2j} = **1,792 / 2,240 / 336**
(j = 0,1,2). **C3 (π=0 λ-layer):** with a = |U ∩ {4,12}| (the OΛ slots 2u ≡ 8) and
t = #pairs {u, 8−u} among the other 14 elements (7 pairs):
N(a,t) = C(2,a)·C(7,t)·C(7−t, 5−a−2t)·2^{5−a−2t} = 672/1120/210; 1120/840/42; 280/84/0
(Σ = 4,368 ✓). All verified exactly (`forms.py`).

**Lemma X (geometric DD+PP exclusion) [P].** An E1 axis 2a (pair {α,β}, u_β = u_α+8)
cannot carry a product pair: a product on it cannot involve α or β (L2″-type: forces
u_x = u_α or u_β), so two disjoint pairs would need 4 of the remaining 3 indices. ∎
(0 occurrences in all 4,368 U-sets; this is the geometric half of L5″.)

**λ-sector ways table (the strata derivation in φ-coordinates):**

| λ-sig | π=0 ways | π=1 ways | stratum |
|---|---|---|---|
| ∅\|L | 3,904 | 10,304 | B\|L = 14,208 ✓ |
| P\|L | 14,576 | 31,168 | L\|P + BL\|BP = 45,744 = 23,024 + 22,720 ✓ |
| PP\|L | 3,584 | 7,312 | BL\|PP = 10,896 ✓ |
| P\|LP | 1,536 | 960 | BP\|LP = 2,496 ✓ |
| O\|L / OP\|L / P\|LO | 7,264 / 12,032 / 4,480 | — | L\|O / BL\|OP / BP\|LO ✓ |
| OP\|LO / PP\|LO / OP\|LP | 1,600 / 504 / 288 | — | LO\|OP / LO\|PP / LP\|OP ✓ |
| **Σ** | **49,768** | **49,744** | Δ = 24 [E] |

## 10. Lemma E-par (axis-parity pigeonhole) [P] — and what it kills

In the φ-frame, doubles live on EVEN axes (2u mod 16); a product's axis parity is
par(uᵢ)+par(uⱼ); Λ's is π. With w = #odd uᵢ, the even-axis load is
EL = 5 + C(w,2) + C(5−w,2) + (1−π) over only 8 even axes, so the even-axis collision
excess is ≥ EL − 8, i.e. (using C(w,2)+C(5−w,2) ≥ 4):

  **every feasible class has even-axis collision excess ≥ 1; ≥ 2 when π = 0** —
  and ≥ 3+(1−π) when w ∈ {1,4}, ≥ 7+(1−π) when w ∈ {0,5}.

Verified: 0 violations; the bounds are TIGHT (realized minima 1 at π=1, 2 at π=0);
w-census of feasible classes {(0,1): 720, (0,2): 2000, (0,3): 2496, (0,4): 672,
(1,1): 672, (1,2): 2288, (1,3): 2288, (1,4): 672}; **w ∈ {0,5} never occurs** [E — the
bound ≥ 7 exceeds every realized excess (max 6), but the a-priori cap is enumerated].
Consequences for residual #1: lone-E1/E5/E7/E4 nodes are impossible at π=0 (excess 1
< 2), and **lone-E3 (a single PΛ collision and nothing else) is impossible at BOTH
parities** (at π=1 the λ-axis is odd — zero even-axis excess; at π=0 excess 1 < 2).
The surviving unexplained emptiness is exactly the π=1 lone-{E1, even-axis-E5, E7}
families.

## 11. s- and r-uniformity: one kernel, every rung (`struct_count.c`)

The canonical-frame kernel (φ-coordinates + placement law, parity-pure only, per-π
totals). Every known rung is reproduced EXACTLY, including ε-splits never published
before (π0 = ε0 = even O):

| (s, r) | classes π0/π1 | ways π0/π1 | total | status vs ground truth |
|---|---|---|---|---|
| (8,3) | 4 / 4 | 4 / 4 | **8** | ✓ C19 (16 elements) |
| (16,3) | 96 / 136 | 304 / 368 | **672** | ✓ DERIVED-672 incl. ε-split |
| (32,3) | 1,496 / 1,808 | 373,440 / 391,104 | **764,544** | ✓ O130 incl. ε-split |
| (64,3) | 16,328 / 17,952 | 121,593,117,440 / 123,000,467,200 | **244,593,584,640** | ✓ level-4 anchor (split NEW) |
| (16,5) | 0 | 0 | **0** | ✓ |
| (32,5) | 5,888 / 5,920 | 49,768 / 49,744 | **99,512** | ✓ this doc |
| (64,5) | 1,037,920 / 1,174,080 | 70,236,357,776 / 71,214,621,504 | **141,450,979,280** | ✓ EXACT vs fresh N₅(64); 2,212,000 classes ✓ (split NEW) |
| (32,7) / (32,9) | 0 / 0 | 0 / 0 | **0** | ✓ |
| (64,7) | 1,643,712 / 1,656,384 | 811,877,344 / 774,963,136 | **1,586,840,480** | ✓ EXACT vs fresh N₇(64); 3,300,096 classes ✓ — pure-only count = all-O count ⟹ **parity purity holds at (7,64)** [E, NEW FACT] |
| (128,3) | 151,464 / 158,784 | 2,735,745,184,314,231,778,304 / 2,743,674,148,802,919,349,248 | **5,479,419,333,117,151,127,552** | **PREDICTION** (theorem-grade: purity, reduction, placement all proven at r=3) |
| (128,5) | 71,334,432 / 76,678,272 | 5,694,034,018,163,399,085,600 / 5,720,893,162,149,695,939,840 | **11,414,927,180,313,095,025,440** | **PREDICTION** (theorem-grade via L1′; no independent enumeration yet) |

Marginal-layer corollary if the predictions and the r_max = 2j−5 pattern hold:
marginal(128) ≥ 2·(N₃+N₅)(128) ≈ 3.4×10²² — for #334's per-level law bookkeeping.
Note the ε-direction is NOT monotone in (s,r): ε1 leads at r=3 (all s) and at (64,5),
ε0 leads at (32,5) by 24 and at (64,7) — closed form open.

## 12. Artifact inventory (this dir, scripts/probes/genlaw/r5tax — self-contained)

v1: `analyze.py` (raw-frame engine + gates + classes.json v1), `structure.py`
(identities, z\*/(h,v)/ε tables), `e5max_proof.py` (L7), `e5triple_sat.py` (L7′),
`nodes_and_e5scan.py` (e5 global scan, node_table.json), `final_checks.py`,
`rec5.txt` + `sweep` (audit ground truth), logs `analyze.log`, `structure.log`,
`nodes.log`.
v2: `chart.py` (φ-frame sign-enumeration, gates G1–G7, classes.json), `deriv.py`
(σ-rank engine, no sign enumeration/no DP, NODE-TABLE.txt 107 rows), `forms.py`
(C1–C3, Lemma A/V/X, strata+E5+ε derivations), `purity_check.py` (L1′ machine check),
`pigeonhole.py` (E-par), `struct_count.c` (the all-rung kernel; binary `struct_count`),
`mknodetable.py`, `audit_sweep64.c` + `audit` + `rec32r5.txt` (≡ rec5.txt), run logs
`run_64_7.txt`, `run_128_5.txt`, `chart_out.txt`, `deriv_out.txt`.

## Appendix: the 70-node table (v1 raw-frame census; everything else derived from it)

Columns: a=E7 axes, q=E1 axes, p5=E5 axes, f3=T6 axes, z\* type, E0=empty axes |
np, no = lone-P/lone-O axes (determined), h, v, ways/class | classes, ways, ε0/ε1.

```
  a q p5 f3  z8       E0 | np no  h  v  w/cls | classes  ways  eps0/eps1
  1 1  1  0  P|L       4 |  6  2  8  6   20 |    784  15680  240/544
  0 1  1  0  P|L       3 |  7  3 10  5   10 |    768   7680  192/576
  1 1  1  0  -|L       3 |  7  2 10  4    6 |    896   5376  256/640
  2 1  0  0  P|L       4 |  7  1  8  5   10 |    512   5120  192/320
  3 1  0  0  P|L       5 |  6  0  6  6   15 |    336   5040  144/192
  1 0  1  0  P|L       3 |  6  4 10  5   10 |    448   4480  192/256
  0 1  0  1  P|L       4 |  7  2 10  5   10 |    256   2560  64/192
  1 1  1  0  PP|L      5 |  5  2  8  6   20 |    128   2560  32/96
  0 1  2  0  OP|L      5 |  5  2  8  7   35 |     64   2240  64/0
  1 1  1  0  O|L       4 |  7  1  8  5   10 |    224   2240  224/0
  3 0  0  0  P|L       4 |  6  2  8  5   10 |    224   2240  32/192
  0 2  1  0  PP|L      5 |  6  1  8  6   20 |     96   1920  32/64
  2 0  1  0  P|L       4 |  5  3  8  6   20 |     96   1920  32/64
  3 1  0  0  -|L       4 |  7  0  8  4    4 |    480   1920  96/384
  0 1  1  0  -|L       2 |  8  3 12  3    3 |    576   1728  192/384
  0 1  1  0  O|L       3 |  8  2 10  4    6 |    288   1728  288/0
  1 0  1  0  PP|L      4 |  5  4 10  5   10 |    160   1600  64/96
  1 0  1  0  O|L       3 |  7  3 10  4    6 |    256   1536  256/0
  2 1  0  0  -|L       3 |  8  1 10  3    3 |    512   1536  128/384
  2 1  0  0  OP|L      5 |  7  0  8  5   10 |    144   1440  144/0
  2 1  0  0  P|LO      5 |  7  0  8  5   10 |    144   1440  144/0
  1 1  0  0  P|LP      4 |  7  2 10  4    6 |    224   1344  160/64
  1 0  1  0  OP|L      4 |  6  3 10  5   10 |    128   1280  128/0
  1 1  1  0  OP|L      5 |  6  1  8  6   20 |     64   1280  64/0
  2 0  1  0  OP|L      5 |  5  2  8  6   20 |     64   1280  64/0
  0 0  2  0  OP|L      4 |  5  4 10  6   15 |     80   1200  80/0
  1 0  1  0  -|L       2 |  7  4 12  3    3 |    384   1152  0/384
  0 1  1  0  OP|L      4 |  7  2 10  5   10 |    112   1120  112/0
  0 1  1  0  P|LO      4 |  7  2 10  5   10 |    112   1120  112/0
  1 2  1  0  PP|L      6 |  5  0  6  7   35 |     32   1120  0/32
  0 0  0  1  P|L       3 |  7  4 12  4    4 |    256   1024  64/192
  0 1  0  1  -|L       3 |  8  2 12  3    3 |    256    768  128/128
  1 0  0  0  OP|LO     4 |  8  2 10  4    6 |    128    768  128/0
  1 1  0  0  OP|L      4 |  8  1 10  4    6 |    128    768  128/0
  1 1  0  0  P|LO      4 |  8  1 10  4    6 |    128    768  128/0
  2 0  1  0  -|L       3 |  6  3 10  4    6 |    128    768  32/96
  3 0  0  0  -|L       3 |  7  2 10  3    3 |    256    768  128/128
  1 1  0  0  PP|L      4 |  7  2 10  4    6 |    112    672  80/32
  1 0  1  0  OP|LO     5 |  6  2  8  6   20 |     32    640  32/0
  2 0  1  0  PP|L      5 |  4  3  8  6   20 |     32    640  16/16
  0 1  0  0  P|LP      3 |  8  3 12  3    3 |    192    576  192/0
  2 0  0  0  P|LO      4 |  7  2 10  4    6 |     96    576  96/0
  1 0  2  0  OP|L      5 |  4  3  8  7   35 |     16    560  16/0
  3 0  1  0  PP|L      6 |  3  2  6  7   35 |     16    560  0/16
  2 0  1  0  O|L       4 |  6  2  8  5   10 |     48    480  48/0
  0 0  0  1  O|L       3 |  8  3 12  3    3 |    128    384  128/0
  0 1  0  1  O|L       4 |  8  1 10  4    6 |     64    384  64/0
  1 0  0  0  P|LP      3 |  7  4 12  3    3 |    128    384  0/128
  2 0  0  0  PP|L      4 |  6  3 10  4    6 |     64    384  16/48
  0 2  0  1  PP|L      6 |  6  0  8  6   20 |     16    320  16/0
  1 0  0  1  OP|L      5 |  6  2 10  5   10 |     32    320  32/0
  1 0  1  0  P|LO      4 |  6  3 10  5   10 |     32    320  32/0
  2 1  0  0  PP|L      5 |  6  1  8  5   10 |     32    320  0/32
  3 0  0  0  PP|L      5 |  5  2  8  5   10 |     32    320  16/16
  0 1  0  0  PP|L      3 |  8  3 12  3    3 |     96    288  96/0
  2 0  0  0  OP|L      4 |  7  2 10  4    6 |     48    288  48/0
  0 2  1  0  PP|LO     6 |  6  0  6  7   35 |      8    280  8/0
  0 0  1  0  OP|L      3 |  7  4 12  4    4 |     64    256  64/0
  0 0  1  0  P|LO      3 |  7  4 12  4    4 |     64    256  64/0
  2 1  0  0  O|L       4 |  8  0  8  4    4 |     64    256  64/0
  3 0  0  0  O|L       4 |  7  1  8  4    4 |     64    256  64/0
  0 0  0  0  OP|LO     3 |  9  3 12  3    3 |     64    192  64/0
  0 0  0  1  -|L       2 |  8  4 14  2    1 |    192    192  64/128
  0 1  0  0  OP|LP     4 |  8  2 10  4    6 |     32    192  32/0
  1 0  0  0  PP|L      3 |  7  4 12  3    3 |     64    192  0/64
  2 0  0  0  P|LP      4 |  6  3 10  4    6 |     32    192  0/32
  0 0  0  0  OP|LP     3 |  8  4 12  3    3 |     32     96  32/0
  0 1  0  0  PP|LO     4 |  8  2 10  4    6 |     16     96  16/0
  2 0  0  0  PP|LO     5 |  6  2  8  5   10 |      8     80  8/0
  0 0  0  0  PP|LO     3 |  8  4 12  3    3 |     16     48  16/0
  CROSSFOOT: classes 11808  ways 99512
```


## Provenance addendum (audit pass, 2026-06-12)

The independent adversarial audit (3-way: hand re-derivation of every [PROVEN] lemma,
independent sigma-rank engine over all 8,736 geometries, full record-classification of all
11,808 classes) PASSED with zero fatal/major mathematical findings; the [PROVEN]/[P-m]/[E]
tags were verified accurate. Two provenance notes it requires:

1. **The s = 64 and s = 128 kernel rows (section 11) are builder-logged runs**
   (`run_64_7.txt`, `run_128_5.txt`, 2026-06-11). The s = 64 totals match the in-tree
   ground truth measured independently on 2026-06-10 (`../RESULTS-GENERAL-LAW.md`), and the
   kernel reproduces all 9 small-s rungs from source under the auditor's hands with a
   line-by-line s-dependence review finding no hazard up to s = 128 (no O-bitmask shifts;
   the known UB trap is structurally absent). **Independent re-execution DONE
   (2026-06-12, fresh compile, auditor-independent hands): (64,5) = 2,212,000 /
   141,450,979,280 and (64,7) = 3,300,096 / 1,586,840,480 — both EXACT vs the
   independently-enumerated anchors; (128,3) = 310,248 / 5,479,419,333,117,151,127,552
   and (128,5) = 148,012,704 / 11,414,927,180,313,095,025,440 reproduce the builder's
   logs exactly.** The s = 64 rows are now fully DERIVED-672-grade; the s = 128 rows
   are kernel-derived predictions awaiting an independent-ALGORITHM enumeration.
2. **The general-r form of the feasibility threshold:** the section-7 inequality
   `X + F ≥ 18 − m` is the r = 5 instance of `X + F ≥ T′ − b`, `T′ = C(r,2) + r + 1`,
   `b = (s+1−r)/2` — i.e. `(r+1)² − s ≤ 2(X+F)`. It is NECESSARY only (the exclusion
   lane measured that 100% of pure deaths at zero strata are per-axis capacity, which
   this aggregate count cannot see); see `../exclusion/REPORT.md`.
