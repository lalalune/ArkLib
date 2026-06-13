/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The degree-`t` supply = elementary-symmetric fiber (#389)

The reformulated deep-band supply (`Σ_c C(a_c,t)`) is, for the lowest non-trivial
degree (a word that is the evaluation of a polynomial of degree exactly `t=k+m+1`),
an **exact elementary-symmetric-function fiber count**.

For such a word `w = eval W`, a codeword `c` of `rsCode dom k` agrees with `w` on a
`t`-core `T` iff the forced polynomial `W − W_t·∏_{i∈T}(X−dom i)` has degree `< k`:
`W − c` is divisible by the monic degree-`t` vanishing polynomial of `dom(T)`, and
both have leading coefficient `W_t`, so they are equal up to that scalar; the explainer
is therefore unique and equals that polynomial.  By Vieta the coefficients of
`∏_{i∈T}(X−dom i)` are the elementary symmetric functions of `dom(T)`, so the
degree-`<k` condition reads `e_j(dom(T)) = (−1)^j W_{t−j}/W_t`, `j=1..m+1`.

Hence the explainable `t`-cores of a degree-`t` word are EXACTLY the `t`-subsets of
the domain whose first `m+1` elementary symmetric functions hit the values forced by
`W`'s top coefficients — turning the deep-band supply (for degree-`t` words) into a
pure symmetric-function/subset-sum fiber count.  This isolates the domain-dependence
of the sub-Johnson wall: additively-concentrated domains (arithmetic progressions)
give large fibers, multiplicatively-structured domains (`μ_n`) spread them.

Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.EsymmFiber

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The monic degree-`|T|` vanishing polynomial of the domain image of `T`. -/
noncomputable def coreVanish (dom : Fin n ↪ F) (T : Finset (Fin n)) : Polynomial F :=
  ∏ i ∈ T, (X - C (dom i))

theorem coreVanish_monic (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    (coreVanish dom T).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (dom i))

theorem coreVanish_degree (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    (coreVanish dom T).degree = (T.card : WithBot ℕ) := by
  classical
  rw [coreVanish, degree_prod]
  rw [Finset.sum_congr rfl (fun i _ => degree_X_sub_C (dom i))]
  simp [Finset.sum_const, nsmul_eq_mul]

theorem coreVanish_eval_zero (dom : Fin n ↪ F) {T : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ T) : (coreVanish dom T).eval (dom i) = 0 := by
  classical
  rw [coreVanish, eval_prod]
  exact Finset.prod_eq_zero hi (by simp)

/-- The forced explainer polynomial of a degree-`t` word `W` on a core `T`. -/
noncomputable def forcedPoly (dom : Fin n ↪ F) (k m : ℕ) (W : Polynomial F)
    (T : Finset (Fin n)) : Polynomial F :=
  W - C (W.coeff (k + m + 1)) * coreVanish dom T

/-- **The core identity (#389).**  For a degree-`t` word `w = eval W`
(`W.degree = k+m+1`) and a `t`-core `T`, a codeword of `rsCode dom k` explains `T`
iff the forced explainer polynomial `W − W_t·∏_{i∈T}(X−dom i)` has degree `< k`.  The
explainer is unique and equals that polynomial. -/
theorem explainable_iff_forcedPoly_degree
    (dom : Fin n ↪ F) {k m : ℕ} (W : Polynomial F)
    (hWdeg : W.degree = ((k + m + 1 : ℕ) : WithBot ℕ))
    {T : Finset (Fin n)} (hT : T.card = k + m + 1) :
    (∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)), ∀ i ∈ T, c i = W.eval (dom i))
      ↔ (forcedPoly dom k m W T).degree < (k : WithBot ℕ) := by
  classical
  have hWne : W ≠ 0 := by
    rintro rfl; rw [degree_zero] at hWdeg; exact absurd hWdeg WithBot.bot_ne_coe
  have hWnat : W.natDegree = k + m + 1 := natDegree_eq_of_degree_eq_some hWdeg
  have hWtne : W.coeff (k + m + 1) ≠ 0 := by
    rw [← hWnat]; exact leadingCoeff_ne_zero.mpr hWne
  have hCVdeg : (coreVanish dom T).degree = ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rw [coreVanish_degree, hT]
  have hCmuldeg :
      (C (W.coeff (k + m + 1)) * coreVanish dom T).degree
        = ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_C hWtne, hCVdeg, zero_add]
  -- the forced poly has degree < t (leading terms cancel)
  have hForcedlt :
      (forcedPoly dom k m W T).degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
    rw [forcedPoly, ← hWdeg]
    refine degree_sub_lt ?_ hWne ?_
    · rw [hWdeg, hCmuldeg]
    · rw [leadingCoeff_mul, leadingCoeff_C, (coreVanish_monic dom T).leadingCoeff, mul_one]
      rw [show W.leadingCoeff = W.coeff (k + m + 1) from by rw [← hWnat]; rfl]
  -- the forced poly agrees with W on dom(T)
  have hForcedeval : ∀ i ∈ T, (forcedPoly dom k m W T).eval (dom i) = W.eval (dom i) := by
    intro i hi
    rw [forcedPoly, eval_sub, eval_mul, eval_C, coreVanish_eval_zero dom hi, mul_zero, sub_zero]
  constructor
  · rintro ⟨c, hc, hagree⟩
    obtain ⟨P, hPdeg, rfl⟩ := hc
    have hsub : (forcedPoly dom k m W T - P).degree < ((k + m + 1 : ℕ) : WithBot ℕ) := by
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt hForcedlt ?_)
      exact lt_of_lt_of_le hPdeg (by exact_mod_cast (show k ≤ k + m + 1 by omega))
    have hvan : ∀ x ∈ T.image dom, (forcedPoly dom k m W T - P).eval x = 0 := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hpa : P.eval (dom i) = W.eval (dom i) := hagree i hi
      rw [eval_sub, hForcedeval i hi, hpa, sub_self]
    have hzero : forcedPoly dom k m W T - P = 0 :=
      Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := T.image dom)
        (by rw [Finset.card_image_of_injective _ dom.injective, hT]; exact hsub) hvan
    rw [sub_eq_zero.mp hzero]; exact hPdeg
  · intro hdeg
    refine ⟨fun i => (forcedPoly dom k m W T).eval (dom i),
      ⟨forcedPoly dom k m W T, hdeg, rfl⟩, fun i hi => hForcedeval i hi⟩

/-! ## The dyadic coset-union construction: exponential supply on smooth domains

If the domain has a `μ_d`-subgroup structure, a union of `μ_d`-cosets `A` has vanishing
polynomial `∏_{i∈A}(X − dom i) = expand_d Q` (a polynomial in `X^d`), so its top `d−1`
sub-leading coefficients vanish.  For the word `w = wt·X^t + (deg<k)` this forces the
explainer to have degree `≤ t − d ≤ k − 1 < k` (using `d ≥ m+2`), so `A` is an
explainable `t`-core.  There are `C(n/d, t/d)` such unions — exponential. -/

open Polynomial in
/-- **Coset-union ⟹ explainable core.**  If `∏_{i∈A}(X − dom i) = expand_d Q` (i.e. `A`
is a union of `μ_d`-cosets) with `|A| = t = k+m+1`, `d ≥ m+2`, and `w = wt·X^t + lowPart`
(`lowPart` of degree `< k`, `wt ≠ 0`), then a codeword of `rsCode dom k` explains `A`. -/
theorem explainable_of_expand
    (dom : Fin n ↪ F) {k m d : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d)
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F)
    (hlow : lowPart.degree < (k : WithBot ℕ))
    {A : Finset (Fin n)} (hAcard : A.card = k + m + 1)
    (Q : Polynomial F)
    (hAexp : (∏ i ∈ A, (X - C (dom i))) = Polynomial.expand F d Q) :
    ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
       ∀ i ∈ A, c i = (C wt * X ^ (k + m + 1) + lowPart).eval (dom i) := by
  classical
  have hd0 : 0 < d := by omega
  set t := k + m + 1 with ht
  set W : Polynomial F := C wt * X ^ t + lowPart with hWdef
  -- degree of `C wt * X^t` is t
  have hCXt : (C wt * X ^ t).degree = (t : WithBot ℕ) := degree_C_mul_X_pow t hwt
  have hlowlt : lowPart.degree < (t : WithBot ℕ) :=
    lt_of_lt_of_le hlow (by exact_mod_cast (show k ≤ t by omega))
  have hWdeg : W.degree = (t : WithBot ℕ) := by
    rw [hWdef, degree_add_eq_left_of_degree_lt (by rw [hCXt]; exact hlowlt), hCXt]
  -- the leading coefficient of W (at t) is wt
  have hWcoeff : W.coeff t = wt := by
    rw [hWdef, coeff_add, coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one,
      Polynomial.coeff_eq_zero_of_degree_lt hlowlt, add_zero]
  -- ∏_A is the monic degree-t coreVanish; identify it with `expand_d Q`
  have hCV : (∏ i ∈ A, (X - C (dom i))) = coreVanish dom A := rfl
  have hCVmonic : (coreVanish dom A).Monic := coreVanish_monic dom A
  have hCVdeg2 : (coreVanish dom A).degree = (t : WithBot ℕ) := by
    rw [coreVanish_degree, hAcard]
  have hCVnat : (coreVanish dom A).natDegree = t := natDegree_eq_of_degree_eq_some hCVdeg2
  have hCVexp : coreVanish dom A = Polynomial.expand F d Q := hCV ▸ hAexp
  set s := Q.natDegree with hs
  -- Q is monic (its expand is the monic coreVanish), so s·d = t
  have hQmonic : Q.Monic := (Polynomial.monic_expand_iff hd0).mp (hCVexp ▸ hCVmonic)
  have hsdt : s * d = t := by
    have h := hCVnat; rw [hCVexp, Polynomial.natDegree_expand] at h; exact h
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exfalso; rw [h, Nat.zero_mul] at hsdt; omega
    · exact h
  -- X^t = expand_d (X^s), hence X^t − coreVanish = expand_d (X^s − Q)
  have hXt : (X : Polynomial F) ^ t = Polynomial.expand F d (X ^ s) := by
    rw [map_pow, Polynomial.expand_X, ← pow_mul, mul_comm, hsdt]
  have hdiff : (X : Polynomial F) ^ t - coreVanish dom A
      = Polynomial.expand F d (X ^ s - Q) := by
    rw [map_sub, ← hXt, hCVexp]
  -- natDegree (X^s − Q) ≤ s − 1 (monic minus monic of equal degree)
  have hsubnat : ((X : Polynomial F) ^ s - Q).natDegree ≤ s - 1 := by
    have e2 : Q.degree = (s : WithBot ℕ) := Polynomial.degree_eq_natDegree hQmonic.ne_zero
    have hsublt : ((X : Polynomial F) ^ s - Q).degree < (s : WithBot ℕ) := by
      have hlt := Polynomial.degree_sub_lt (p := (X : Polynomial F) ^ s) (q := Q)
        (by rw [degree_X_pow, e2]) (pow_ne_zero s X_ne_zero)
        (by rw [(monic_X_pow s).leadingCoeff, hQmonic.leadingCoeff])
      rwa [degree_X_pow] at hlt
    by_cases h0 : (X : Polynomial F) ^ s - Q = 0
    · rw [h0, natDegree_zero]; omega
    · have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hsublt; omega
  -- hence natDegree (X^t − coreVanish) ≤ t − d
  have hdiffnat : ((X : Polynomial F) ^ t - coreVanish dom A).natDegree ≤ t - d := by
    rw [hdiff, Polynomial.natDegree_expand]
    calc ((X : Polynomial F) ^ s - Q).natDegree * d ≤ (s - 1) * d :=
          Nat.mul_le_mul hsubnat le_rfl
      _ = s * d - d := by rw [Nat.sub_one_mul]
      _ = t - d := by rw [hsdt]
  -- forcedPoly = lowPart + wt·(X^t − coreVanish), so degree < k
  rw [explainable_iff_forcedPoly_degree dom W hWdeg hAcard]
  have hforced : forcedPoly dom k m W A = lowPart + C wt * (X ^ t - coreVanish dom A) := by
    rw [forcedPoly, hWcoeff, hWdef, coreVanish]; ring
  rw [hforced]
  have hdk : t - d ≤ k - 1 := by omega
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt hlow ?_)
  rw [degree_mul, degree_C hwt, zero_add]
  calc ((X : Polynomial F) ^ t - coreVanish dom A).degree
      ≤ ((t - d : ℕ) : WithBot ℕ) := Polynomial.degree_le_of_natDegree_le hdiffnat
    _ ≤ ((k - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast hdk
    _ < (k : WithBot ℕ) := by exact_mod_cast (by omega : k - 1 < k)

open Polynomial in
/-- **Exponential supply on smooth dyadic domains (#389).**  Suppose the domain is
partitioned into `r` blocks, each a `μ_d`-coset — i.e. `(block j).card = d`, the blocks
are pairwise disjoint, and `∏_{i∈block j}(X − dom i) = X^d − C (β j)`.  If `d ≥ m+2` and
`s·d = k+m+1`, then the word `w = wt·X^t + lowPart` (`lowPart` of degree `< k`) has at
least `C(r, s)` explainable `(k+m+1)`-cores — the `s`-fold unions of blocks.

For a 2-adic smooth domain `μ_{2^μ}` (`d = 2^j`, `r = n/d`) and constant rate, `C(r, s) =
C(n/d, t/d)` is **exponential in `n`**: explicit smooth (FFT) Reed–Solomon codes have
exponential sub-Johnson supply / list size — the multiplicative-subgroup analogue of the
Ben-Sasson–Kopparty–Radhakrishnan subspace-polynomial limit, refuting any subexponential
uniform supply bound on such domains. -/
theorem smooth_dyadic_supply_lower_bound
    (dom : Fin n ↪ F) {k m d r : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d)
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F)
    (hlow : lowPart.degree < (k : WithBot ℕ))
    (block : Fin r → Finset (Fin n)) (hbcard : ∀ j, (block j).card = d)
    (hbdisj : ∀ j j', j ≠ j' → Disjoint (block j) (block j'))
    (β : Fin r → F)
    (hbcoset : ∀ j, (∏ i ∈ block j, (X - C (dom i))) = X ^ d - C (β j))
    {s : ℕ} (hsd : s * d = k + m + 1) :
    r.choose s ≤
      (((Finset.univ : Finset (Fin n)).powersetCard (k + m + 1)).filter
        (fun T => ∃ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
            ∀ i ∈ T, c i = (C wt * X ^ (k + m + 1) + lowPart).eval (dom i))).card := by
  classical
  -- recover membership in S from the union (blocks disjoint and nonempty)
  have hmemiff : ∀ (T : Finset (Fin r)) (j : Fin r),
      j ∈ T ↔ block j ⊆ T.biUnion block := by
    intro T j
    refine ⟨fun hj => Finset.subset_biUnion_of_mem block hj, fun hsub => ?_⟩
    have hne : (block j).Nonempty := by rw [← Finset.card_pos, hbcard]; omega
    obtain ⟨i, hi⟩ := hne
    obtain ⟨j', hj', hij'⟩ := Finset.mem_biUnion.mp (hsub hi)
    by_cases hjj' : j = j'
    · rwa [hjj']
    · exact absurd hij' (Finset.disjoint_left.mp (hbdisj j j' hjj') hi)
  have hcard_ps : ((Finset.univ : Finset (Fin r)).powersetCard s).card = r.choose s := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hcard_ps]
  refine Finset.card_le_card_of_injOn (fun S => S.biUnion block) ?_ ?_
  · -- the union of `s` blocks is an explainable `t`-core
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨-, hScard⟩ := hS
    have hfcard : (S.biUnion block).card = k + m + 1 := by
      rw [Finset.card_biUnion (fun a _ b _ hab => hbdisj a b hab),
        Finset.sum_congr rfl (fun j _ => hbcard j), Finset.sum_const, hScard,
        smul_eq_mul, hsd]
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, hfcard⟩, ?_⟩
    have hAexp : (∏ i ∈ S.biUnion block, (X - C (dom i)))
        = Polynomial.expand F d (∏ j ∈ S, (X - C (β j))) := by
      rw [Finset.prod_biUnion (fun a _ b _ hab => hbdisj a b hab),
        Finset.prod_congr rfl (fun j _ => by
          rw [hbcoset j, map_sub, Polynomial.expand_X, Polynomial.expand_C]),
        ← map_prod]
    exact explainable_of_expand dom hk hd wt hwt lowPart hlow hfcard _ hAexp
  · -- injectivity: `S` is recoverable from its union of blocks
    intro S _ S' _ heq
    ext j
    rw [hmemiff S j, hmemiff S' j, heq]

end ProximityGap.EsymmFiber

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.EsymmFiber.explainable_iff_forcedPoly_degree
#print axioms ProximityGap.EsymmFiber.explainable_of_expand
#print axioms ProximityGap.EsymmFiber.smooth_dyadic_supply_lower_bound
