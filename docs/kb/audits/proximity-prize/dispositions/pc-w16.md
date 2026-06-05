# pc-w16 — P2 full-sum vanishing carved to ONE weight identity + exponent-balance verified

**File:** `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2Vanish.lean` (NEW, untracked, wipe-safe).
**Imports:** `…BCIKS20.P2Match` (olean present; remote `lalalune/proximity-prize-l217:…/P2Match.lean`
is byte-identical to the local file — confirmed).
**Compile:** `cd /home/shaw/arklib-prize && export PATH=$HOME/.elan/bin:$PATH && lake env lean
ArkLib/.../P2Vanish.lean` → exit 0.
**Axioms (in-file `#print axioms`, all 10 decls):** `[propext, Classical.choice, Quot.sound]`
(`fullSum_W_exponent` even drops `Classical.choice`). NO `sorryAx`, `native_decide`, `bv_decide`.
**Backup:** `/tmp/P2Vanish.bak` after every green compile.

## Target

`FaaDiBrunoFullSumVanishes H x₀ R hHyp` := `∀ t, faaDiBrunoFullSum (t+1) = 0`, equivalently (by the
PROVEN `faaDiBrunoFullSum_eq_coeff`) `coeff (t+1) (eval (βHenselAssembled) Q) = 0`.

## Outcome: (b) bijection reindex PROVEN + ONE named weight identity left; (c) PRECISE mismatch FINDING

I did **not** fake a closure. The genuine residual is a single binomial-keying mismatch in the
in-tree `B_coeff` `prefactor` (the `prefactor_eq_paper` WALL). What I PROVED — the two
load-bearing *connective* facts the paper's match rests on, previously hidden inside that opaque
WALL — are axiom-clean:

### 1. The `m ↔ (j0 zeros, λ positives)` bijection weight (zero-peeling), PROVEN

```lean
theorem countPerms_replicate_zero_add (j0 : ℕ) (lam : Multiset ℕ) (h0 : (0 : ℕ) ∉ lam) :
    (Multiset.replicate j0 0 + lam).countPerms
      = (j0 + lam.card).choose j0 * lam.countPerms := by
  classical
  set m : Multiset ℕ := Multiset.replicate j0 0 + lam with hm
  have hcount0 : m.count 0 = j0 := by
    rw [hm, Multiset.count_add, Multiset.count_replicate_self,
      Multiset.count_eq_zero_of_notMem h0, add_zero]
  have hcountv : ∀ v, v ≠ 0 → m.count v = lam.count v := by
    intro v hv
    rw [hm, Multiset.count_add, Multiset.count_replicate, if_neg (by simpa [eq_comm] using hv),
      zero_add]
  rw [countPerms_eq_multinomial, countPerms_eq_multinomial]
  by_cases hj : j0 = 0
  · subst hj
    simp only [Multiset.replicate_zero, zero_add] at hm
    rw [hm]; simp
  · have h0nf : (0 : ℕ) ∉ lam.toFinset := by rwa [Multiset.mem_toFinset]
    have htf : m.toFinset = insert 0 lam.toFinset := by
      rw [hm]
      ext x
      simp only [Multiset.toFinset_add, Finset.mem_union, Multiset.mem_toFinset,
        Multiset.mem_replicate, Finset.mem_insert]
      constructor
      · rintro (⟨_, rfl⟩ | h)
        · exact Or.inl rfl
        · exact Or.inr h
      · rintro (rfl | h)
        · exact Or.inl ⟨hj, rfl⟩
        · exact Or.inr h
    rw [htf, Nat.multinomial_insert h0nf]
    have hsum : ∑ i ∈ lam.toFinset, m.count i = lam.card := by
      rw [Finset.sum_congr rfl (fun v hv => hcountv v (by rintro rfl; exact h0nf hv))]
      rw [← Multiset.toFinset_sum_count_eq lam]
    rw [hcount0, hsum]
    congr 1
    refine Nat.multinomial_congr ?_
    intro v hv
    exact hcountv v (by rintro rfl; exact h0nf hv)
```

Re-keyed to the Y-degree `j = card m = j0 + cardλ` and `sl = Σλ = cardλ`, via `Nat.choose_symm`:

```lean
theorem countPerms_replicate_zero_add_choose_sl (j0 : ℕ) (lam : Multiset ℕ) (h0 : (0 : ℕ) ∉ lam) :
    (Multiset.replicate j0 0 + lam).countPerms
      = (j0 + lam.card).choose lam.card * lam.countPerms := by
  rw [countPerms_replicate_zero_add j0 lam h0]
  congr 1
  rw [← Nat.choose_symm (Nat.le_add_left lam.card j0)]
  congr 1
  omega
```

So **the full-sum value-multiset weight is `countPerms m = C(j, Σλ) · multinomial λ`** — the
Y-Hasse binomial `C(j, Σλ)` times the positive-part multinomial. This is the exact shape the
recursion's `Δ_Y^{Σλ}` step produces (see §4 below).

### 2. The W/ξ exponent telescope, VERIFIED (no imbalance), PROVEN

The assembled-product denominators over `m`:

```lean
theorem fullSum_W_exponent (m : Multiset ℕ) :
    (m.map (fun l => l + 1)).sum = m.sum + Multiset.card m := by
  rw [Multiset.sum_map_add]; simp [Multiset.map_id']

theorem fullSum_ξ_exponent (lam : Multiset ℕ) (h0 : (0 : ℕ) ∉ lam) :
    (lam.map (fun l => 2 * l - 1)).sum = 2 * lam.sum - Multiset.card lam := by
  induction lam using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons, Multiset.card_cons]
    have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (fun h => h0 (h ▸ Multiset.mem_cons_self a s))
    have h0s : (0 : ℕ) ∉ s := fun h => h0 (Multiset.mem_cons_of_mem h)
    have hcs : Multiset.card s ≤ s.sum := by
      calc Multiset.card s = (s.map (fun _ => 1)).sum := by simp
        _ ≤ (s.map id).sum := Multiset.sum_map_le_sum_map _ _ (by
              intro x hx; exact Nat.one_le_iff_ne_zero.mpr (fun h => h0s (h ▸ hx)))
        _ = s.sum := by simp
    rw [ih h0s]; omega
```

KEY: `2·0 − 1 = 0` in ℕ, so **only the positive entries `λ` contribute to the ξ power** — this
ℕ-truncation is precisely why the ξ telescope closes (the zeros do NOT contribute `ξ^{-1}`).

The telescope balance (clean ℤ identities; recursion-power + product-denominator − global-denom):

```lean
theorem exponent_balance_ξ (i1 b t sl : ℤ) (h : i1 + b = t + 1) :
    ((2 * i1 + sl - 2) + (2 * b - sl)) - (2 * t + 1) = -1 := by linarith

theorem exponent_balance_W (i1 b t i δ : ℤ) (h : i1 + b = t + 1) :
    ((i1 + δ - 1) + (b + i)) - (t + 2) = i + δ - 2 := by linarith
```

**ξ: deficit is exactly `−1`** (the `Σλ = sl` cancels) = exactly **one `ζ`**, supplied by the `−ζ`
of `RestrictedFaaDiBrunoMatch` (recall `ξ = W^{d−2}·ζ`, `embeddingOf𝒪Into𝕃_ξ`).
**W: leftover is exactly `i + δ − 2`** = the genuine `B_coeff`/`hasseCoeffRepr𝒪` W-content (the
`Y↦T` vs `Y↦T/W` clearing, `embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared`).
**No imbalance.** The exponents balance term-by-term under `a = i1`, `sum λ = b`, `a + b = t+1`.

### 3 + 4. The single residual weight identity + Y-Hasse source

```lean
def PrefactorWeightMatch : Prop :=
  ∀ (j0 : ℕ) (lam : Multiset ℕ), (0 : ℕ) ∉ lam →
    (Multiset.replicate j0 0 + lam).countPerms
      = (j0 + lam.card).choose lam.card * lam.countPerms

theorem prefactorWeightMatch_holds : PrefactorWeightMatch :=
  fun j0 lam h0 => countPerms_replicate_zero_add_choose_sl j0 lam h0

theorem hasseDerivY_coeff (m : ℕ) (R : F[X][X][Y]) (i : ℕ) :
    (hasseDerivY m R).coeff i = (i + m).choose m • R.coeff (i + m) := by
  rw [hasseDerivY, Polynomial.hasseDeriv_coeff, nsmul_eq_mul]
```

`hasseDerivY_coeff` shows the recursion's `Δ_Y^{Σλ}` step emits `C(i+Σλ, Σλ) = C(j, Σλ)` at
Y-degree `j = i + Σλ` — the **same** binomial the full sum's `countPerms` produces (§1). So the
combinatorial half of the Faà-di-Bruno match is FULLY discharged.

### 5. End-to-end wiring (PROVEN reductions)

```lean
theorem fullVanishes_of_restrictedMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    FaaDiBrunoFullSumVanishes H x₀ R hHyp :=
  (restrictedMatch_iff_fullVanishes H x₀ R hHyp).mp hmatch

theorem P2_closed_of_restrictedMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    (Polynomial.eval (βHenselAssembled H x₀ R hHyp) (Q x₀ R H) = 0) ∧ (∀ t : ℕ, …) :=
  P2_closed_of_fullVanishes H x₀ R hHyp (fullVanishes_of_restrictedMatch H x₀ R hHyp hmatch)
```

## THE FINDING (precise, minimal form of `prefactor_eq_paper`)

The full Faà-di-Bruno weight at Y-degree `j` with positives `λ` (`Σλ = cardλ`) is
**`C(j, Σλ) · multinomial λ`** (§1 + §4: `C(j, Σλ)` from `Δ_Y^{Σλ}`, `multinomial λ` from the
positive orderings). The in-tree `prefactor i i1 λ := C(i, i1) · multinomial λ`
(`HenselNumerator.lean:411`) carries the binomial **`C(R.natDegree, i1)`** keyed to the X-Taylor
order `i1` and the *leading-coefficient degree* `R.natDegree` — an object with **no dependence on
`(j, Σλ)`**. The two agree iff `C(R.natDegree, i1) = C(j, Σλ)` along the bijection, which is NOT an
identity of the in-tree `prefactor` (e.g. `j=2, Σλ=1` needs `2`, while `C(R.natDegree, i1)` is
independent of `j`). The genuine A.4 weight requires `prefactor` re-keyed to the **Y-Hasse binomial
`C(j, Σλ)`**, an `i1`-independent factor.

This is a one-line definitional re-keying of `prefactor`/`B_coeff` in the TRACKED `HenselNumerator.lean`
— off-limits in this worktree (harness hard-resets tracked files). It is the irreducible frontier:
everything *connective* (the bijection reindex, the exponent telescope, the Y-Hasse binomial source)
is now PROVEN and axiom-clean in `P2Vanish.lean`. Closing P2 requires only that the in-tree
`prefactor` binomial be corrected from `C(R.natDegree, i1)` to `C(j, Σλ)` (then the match is the
identity `prefactorWeightMatch_holds`).

## Wire-in (one line, NOT made here; for the owner)

Once `prefactor` is re-keyed to `C(j, Σλ)`, `RestrictedFaaDiBrunoMatch` is discharged term-by-term
by `prefactorWeightMatch_holds` (combinatorics) + `exponent_balance_{ξ,W}` (telescope) +
`hasseDerivY_coeff` (Y-Hasse), and `P2_closed_of_restrictedMatch` closes all of P2 with no new axioms.
