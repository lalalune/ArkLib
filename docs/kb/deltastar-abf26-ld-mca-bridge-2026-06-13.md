# ABF26 §5 — the LD⇒MCA bridge, exact, and why the prize regime is unblocked (2026-06-13)

Extracted verbatim from the prize paper ABF26 (ePrint 2026/680) §§4.4, 5, 6. This is the
connective tissue that makes a **single conjecture solve both grand challenges**, plus the precise
reason the known obstruction does *not* apply in the prize regime.

## 1. The two challenges share one object (confirmed from the source)

- **Strengthening chain:** `ε_pg(C,δ) ≤ ε_ca(C,δ) ≤ ε_mca(C,δ)` (each a strict strengthening).
- **Grand MCA challenge (Ch.1):** pin `ε_mca(RS[F,L,k], δ)` for `L` a 2-power multiplicative
  subgroup, family `F_lines`, `ε*=2^{-128}`.
- **Grand LD challenge (Ch.2):** pin `Λ(C^{≡m}, δ)` (interleaved RS) — "for what `δ` is the list
  small," with the field-size list bound `|Λ| ≤ ε*|F|`.
- **Toy protocol (§6)** needs *both* an MCA bound *and* a list-decoding bound simultaneously — the
  prize is explicitly the conjunction, bridged by §5.

## 2. The exact bridge — Theorem 5.1 (GCXK25 Thm 3): **LD ⟹ MCA**

> If `Λ(C,δ) ≤ L`, then for `η∈(0,1)`
> `ε_mca(C, 1 − √(1−δ+η)) ≤ (L²·δ·n + 1/η)/|F| = O_δ(L²n/(η|F|))`.

So a **list bound `L` at radius `δ`** yields **MCA at the Johnson-transformed radius
`δ_mca = 1 − √(1−δ)`** with error `≈ L²n/(η|F|)`. Two consequences pinned to numbers:

- **The `√`-loss.** The MCA radius is the Johnson transform of the LD radius; ABF26 notes this
  "implies MCA up to the 2-Johnson regime for all codes," and *up to capacity for **random** RS*.
  Removing the `√`-loss would reestablish everything — but **cannot hold in general** (Thm 5.4),
  so the open question is whether it holds for the *special* smooth-subgroup RS.
- **The budget = the field-size lever (matches `FieldSizeThresholdReduction.lean`).**
  `ε_mca ≤ ε*` ⟺ `L²n/(η|F|) ≲ 2^{-128}` ⟺ **`L² ≲ η·|F|/(n·2^{128})`**. Plugging the regimes:
  - deployed `|F| ≈ n·2^{128}` ⇒ `L² ≲ η` ⇒ `L = O(1)` (need a *tiny* list — the hard case);
  - large `|F| ≈ 2^{256}`, `n=2^{30}` ⇒ `L ≲ 2^{49}√η` (an `n^{1.5}` list already clears it).
  This is exactly the field-size separation proven in `censusDomination_pin_largeField`.

## 3. CA ⟹ LD (the converse, the necessity direction)
- **Thm 5.2 (BCHKS25 Thm 1.9):** `ε_ca(C, δ+2/n) < 1/(2n)` ⇒ `|Λ(C,δ)| < |F|`. So a *very small*
  CA error forces a small list — proving small-error CA *requires* proving an LD bound. The two
  directions (5.1, 5.2) make LD and MCA **inter-reducible up to the `√`-loss and the `1/n` vs `ε*`
  error scale** — one closed `L(C,δ)` law settles both.
- **Thm 5.3 (CS25 Thm 2):** dimension-bumped list transfer `|Λ(C⁺,δ)| ≤ ⌈|F|/(1−η)·ε_ca⌉`.

## 4. WHY THE PRIZE REGIME IS UNBLOCKED — the obstruction is full-domain (key finding)

> **Thm 5.4 (BGKS20 Lemma 3.3):** for char-2, `C = RS[F, F, |F|/8]` (rate 1/8), `ε_ca(C,1−ρ^{1/3})
> ≥ 1 − 1/|F|` — a code that *is* list-decodable (list ≈40 at that radius by Johnson) yet has **no**
> CA at radius `1−ρ^{1/3}=0.5`.

This is the standard "LD does not tightly imply CA" counterexample. **But ABF26 states the crucial
caveat verbatim:** *"the code is full-domain (the evaluation domain is the entire field)… one could
still hope for such a relationship for codes where the field size and evaluation domain size are
large (in the SNARK use-case `|F|` is very large compared to `n`)."*

> **The counterexample needs `n = |F|`. The prize has `n = 2^μ ≪ |F|`. So the obstruction to a
> tight (no-`√`-loss) LD⇒MCA implication DOES NOT APPLY in the prize regime.** Tight LD⇒MCA for
> smooth subgroup RS is *open and unrefuted* — a live, prize-regime-specific target.

This is the cleanest "true statement that fails outside the prize regime" filter (per the workbench
mandate): the LD⇏CA wall is a *full-domain* phenomenon, silent on smooth subgroups.

## 5. The unified program (what a single closed conjecture must do)
1. **Pin `L = Λ(RS[F,μ_n,k], δ)`** in the window (Ch.2). This is the additive-energy /
   curve-irreducibility core (faces (i)/(v)); `CensusDomination` is its in-tree form.
2. **Apply Thm 5.1** to get `ε_mca` at `1−√(1−δ)` (Ch.1), with the field-size budget `L²≲η|F|/(n2^{128})`.
3. **The prize-regime opening:** prove the **tight (no-`√`-loss)** LD⇒MCA for `n≪|F|` smooth RS —
   unblocked by Thm 5.4. If the `√`-loss is removable here, the MCA radius equals the LD radius and
   the two challenges collapse to a *single* `δ*(ρ)` law, with the field-size lever supplying the
   budget. **This is the most promising never-closed direction: a regime-restricted LD⇒MCA
   equivalence, plus the explicit smooth-RS list bound.**

## 6. Line-decoding (§4.4) — the even-stronger handle
`Λ`-decodable ⟹ `(δ,a,n+1)` line-decodable (GG25 Def 3.1) ⟹ `ε_mca(C,δ) ≤ a/|F|` (Thm 4.21). So
**line-decodability is a third equivalent face**, and `a` (the line-decoding list parameter) plays
the role of `L`. The in-tree GG25 curve-decodability bricks target exactly this. Carmon–Goldberg–
Haböck–Lerer–Lesokhin [CGHLL26, App. A] is flagged for further line-decoding conjectures (fetch).
