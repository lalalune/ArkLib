import Mathlib

/-!
Exact preservation of a scalar list budget under positive interleaving arity.
The field-size gate is choose(B+1,2) <= |F|. This does not prove the required
scalar decoding estimate or identify an MCA bad set with a scalar list.

The covering proof adapts the existing ArkLib theorem
ProximityGap.exists_nonzero_notMem_of_proper_family to an arbitrary finite
index type, keeping zero outside the chosen projection as well.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace AstraExactListProjection

open Finset
open scoped BigOperators

theorem avoid_proper_subspaces {F κ : Type*} [Field F] [Fintype F] [Fintype κ]
    {m : ℕ} (hm : 1 ≤ m) (hκ : Fintype.card κ ≤ Fintype.card F)
    (K : κ → Submodule F (Fin m → F)) (hK : ∀ i, K i ≠ ⊤) :
    ∃ lam : Fin m → F, lam ≠ 0 ∧ ∀ i, lam ∉ K i := by
  classical
  set q : ℕ := Fintype.card F
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hcardType : Fintype.card (Fin m → F) = q ^ m := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hfrTop : Module.finrank F (Fin m → F) = m := by
    rw [Module.finrank_pi, Fintype.card_fin]
  set d : ℕ := q ^ (m - 1)
  have hd1 : 1 ≤ d := Nat.one_le_pow _ _ (by omega)
  have hcardK : ∀ i, Fintype.card (K i) ≤ d := by
    intro i
    have hfr : Module.finrank F (K i) < m := by
      have := Submodule.finrank_lt (s := K i) (hK i)
      rwa [hfrTop] at this
    have heq : Fintype.card (K i) = q ^ Module.finrank F (K i) :=
      Module.card_eq_pow_finrank
    rw [heq]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  let B : Finset (Fin m → F) :=
    insert 0 (univ.biUnion (fun i => (K i : Set (Fin m → F)).toFinset.erase 0))
  have hcardErase : ∀ i, ((K i : Set (Fin m → F)).toFinset.erase 0).card ≤ d - 1 := by
    intro i
    have h0 : (0 : Fin m → F) ∈ (K i : Set (Fin m → F)).toFinset := by
      rw [Set.mem_toFinset]
      exact Submodule.zero_mem _
    rw [card_erase_of_mem h0, Set.toFinset_card]
    have hcg : Fintype.card (↑(K i) : Set (Fin m → F)) = Fintype.card (K i) := rfl
    have := hcardK i
    omega
  have hcardB : B.card ≤ 1 + q * (d - 1) := by
    have hbu : (univ.biUnion (fun i => (K i : Set (Fin m → F)).toFinset.erase 0)).card
        ≤ q * (d - 1) := by
      refine le_trans card_biUnion_le ?_
      refine le_trans (Finset.sum_le_sum (fun i _ => hcardErase i)) ?_
      simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using
        Nat.mul_le_mul_right (d - 1) hκ
    have hins := card_insert_le (0 : Fin m → F)
      (univ.biUnion (fun i => (K i : Set (Fin m → F)).toFinset.erase 0))
    dsimp [B]
    omega
  have hqd : q * (d - 1) + q = q ^ m := by
    have hstep : d - 1 + 1 = d := Nat.sub_add_cancel hd1
    calc
      q * (d - 1) + q = q * (d - 1 + 1) := by ring
      _ = q * d := by rw [hstep]
      _ = q ^ m := by
        dsimp [d]
        rw [← pow_succ']
        congr 1
        omega
  have hBlt : B.card < q ^ m := by omega
  have hBne : B ≠ univ := by
    intro h
    rw [h, card_univ, hcardType] at hBlt
    exact (lt_irrefl _ hBlt)
  rw [Ne, eq_univ_iff_forall, not_forall] at hBne
  obtain ⟨lam, hlam⟩ := hBne
  have hlam0 : lam ≠ 0 := by
    intro h
    apply hlam
    rw [h]
    exact mem_insert_self 0 _
  refine ⟨lam, hlam0, ?_⟩
  intro i hi
  apply hlam
  apply mem_insert_of_mem
  rw [mem_biUnion]
  refine ⟨i, mem_univ i, ?_⟩
  rw [mem_erase, Set.mem_toFinset]
  exact ⟨hlam0, hi⟩

variable {F : Type*} [Field F] [Fintype F]

def project {m : ℕ} {W : Type*} [AddCommGroup W] [Module F W]
    (lam : Fin m → F) (v : Fin m → W) : W := ∑ j, lam j • v j

def projectLinear {m : ℕ} {W : Type*} [AddCommGroup W] [Module F W]
    (v : Fin m → W) : (Fin m → F) →ₗ[F] W where
  toFun := fun lam => project lam v
  map_add' := by
    intro a b
    simp [project, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a b
    simp [project, Finset.smul_sum, smul_smul]

theorem project_sub {m : ℕ} {W : Type*} [AddCommGroup W] [Module F W]
    (lam : Fin m → F) (v z : Fin m → W) :
    project lam (v - z) = project lam v - project lam z := by
  simp [project, smul_sub, Finset.sum_sub_distrib]

theorem exists_separating_projection {α W : Type*} [Fintype α]
    [AddCommGroup W] [Module F W] {m : ℕ} (hm : 1 ≤ m)
    (v : α → Fin m → W) (hinj : Function.Injective v)
    (hgate : (Fintype.card α).choose 2 ≤ Fintype.card F) :
    ∃ lam : Fin m → F, lam ≠ 0 ∧ Function.Injective (fun i => project lam (v i)) := by
  classical
  let pairs : Finset (Finset α) := (univ : Finset α).powersetCard 2
  have htwo : ∀ p : pairs, p.val.card = 2 := by
    intro p
    exact (mem_powersetCard.mp p.property).2
  choose a b hab hp using fun p : pairs => card_eq_two.mp (htwo p)
  let K : pairs → Submodule F (Fin m → F) :=
    fun p => LinearMap.ker (projectLinear (v (a p) - v (b p)))
  have hK : ∀ p, K p ≠ ⊤ := by
    intro p htop
    apply hab p
    apply hinj
    funext j
    have hmem : (fun i : Fin m => if i = j then (1 : F) else 0) ∈ K p := by
      rw [htop]
      trivial
    have hzero := LinearMap.mem_ker.mp hmem
    have hdiff : v (a p) j - v (b p) j = 0 := by
      simpa [K, projectLinear, project, ite_smul] using hzero
    exact sub_eq_zero.mp hdiff
  have hpairCard : Fintype.card pairs ≤ Fintype.card F := by
    simpa only [Fintype.card_coe, pairs, Finset.card_powersetCard, Finset.card_univ] using hgate
  obtain ⟨lam, hlam0, havoid⟩ := avoid_proper_subspaces hm hpairCard K hK
  refine ⟨lam, hlam0, ?_⟩
  intro i j heq
  by_contra hij
  let p : pairs := ⟨{i, j}, mem_powersetCard.mpr ⟨subset_univ _, by simp [hij]⟩⟩
  have ha : a p = i ∨ a p = j := by
    have h : a p ∈ p.val := by rw [hp p]; simp
    simpa [p] using h
  have hb : b p = i ∨ b p = j := by
    have h : b p ∈ p.val := by rw [hp p]; simp
    simpa [p] using h
  have heqab : project lam (v (a p)) = project lam (v (b p)) := by
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · rw [ha, hb]
      · simpa [ha, hb] using heq
    · rcases hb with hb | hb
      · simpa [ha, hb] using heq.symm
      · rw [ha, hb]
  apply havoid p
  apply LinearMap.mem_ker.mpr
  change project lam (v (a p) - v (b p)) = 0
  rw [project_sub, heqab, sub_self]

noncomputable def agreements {ι A : Type*} [Fintype ι] (u v : ι → A) : ℕ := by
  classical
  exact (univ.filter fun x => u x = v x).card

noncomputable def jointAgreements {ι : Type*} [Fintype ι] {m : ℕ}
    (u v : Fin m → ι → F) : ℕ := by
  classical
  exact (univ.filter fun x => ∀ j, u j x = v j x).card

theorem joint_agreements_le_projected {ι : Type*} [Fintype ι] {m : ℕ}
    (lam : Fin m → F) (u v : Fin m → ι → F) :
    jointAgreements u v ≤ agreements (project lam u) (project lam v) := by
  classical
  apply Finset.card_le_card
  intro x hx
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  change (∑ j, lam j • u j) x = (∑ j, lam j • v j) x
  simp only [Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hx j]

noncomputable def scalarList {ι : Type*} [Fintype ι]
    (C : Submodule F (ι → F)) (u : ι → F) (A : ℕ) : Finset (ι → F) := by
  classical
  exact univ.filter fun f => f ∈ C ∧ A ≤ agreements f u

noncomputable def interleavedList {ι : Type*} [Fintype ι] {m : ℕ}
    (C : Submodule F (ι → F)) (u : Fin m → ι → F) (A : ℕ) :
    Finset (Fin m → ι → F) := by
  classical
  exact univ.filter fun f => (∀ j, f j ∈ C) ∧ A ≤ jointAgreements f u

theorem scalar_budget_to_interleaved {ι : Type*} [Fintype ι] {m B A : ℕ}
    (C : Submodule F (ι → F)) (hm : 1 ≤ m)
    (hgate : (B + 1).choose 2 ≤ Fintype.card F)
    (hscalar : ∀ u, (scalarList C u A).card ≤ B) :
    ∀ u : Fin m → ι → F, (interleavedList C u A).card ≤ B := by
  classical
  intro u
  by_contra hbad
  have hbig : B + 1 ≤ (interleavedList C u A).card := by omega
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hbig
  have hSgate : (Fintype.card S).choose 2 ≤ Fintype.card F := by
    simpa only [Fintype.card_coe, hScard] using hgate
  obtain ⟨lam, _, hinj⟩ := exists_separating_projection hm
    (fun f : S => f.val) Subtype.val_injective hSgate
  have himage : S.image (project lam) ⊆ scalarList C (project lam u) A := by
    intro f hf
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hf
    have hmem := hSsub hv
    simp only [interleavedList, mem_filter, mem_univ, true_and] at hmem
    simp only [scalarList, mem_filter, mem_univ, true_and]
    refine ⟨C.sum_mem (fun j _ => C.smul_mem (lam j) (hmem.1 j)), ?_⟩
    exact le_trans hmem.2 (joint_agreements_le_projected lam v u)
  have hinjOn : Set.InjOn (project lam) S := by
    intro v hv z hz heq
    have h : (⟨v, hv⟩ : S) = ⟨z, hz⟩ := hinj heq
    exact congrArg Subtype.val h
  have hcard := Finset.card_le_card himage
  rw [Finset.card_image_of_injOn hinjOn, hScard] at hcard
  have hbound := hscalar (project lam u)
  omega

theorem interleaved_budget_to_scalar {ι : Type*} [Fintype ι] {m B A : ℕ}
    (C : Submodule F (ι → F)) (hm : 1 ≤ m)
    (hinter : ∀ u : Fin m → ι → F, (interleavedList C u A).card ≤ B) :
    ∀ u, (scalarList C u A).card ≤ B := by
  classical
  let j0 : Fin m := ⟨0, by omega⟩
  have hdiag : ∀ f u : ι → F,
      jointAgreements (fun _ : Fin m => f) (fun _ : Fin m => u) = agreements f u := by
    intro f u
    unfold jointAgreements agreements
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => h j0, fun h _ => h⟩
  intro u
  have himage : (scalarList C u A).image (fun f => fun _ : Fin m => f) ⊆
      interleavedList C (fun _ : Fin m => u) A := by
    intro v hv
    obtain ⟨f, hf, rfl⟩ := mem_image.mp hv
    simp only [scalarList, mem_filter, mem_univ, true_and] at hf
    simp only [interleavedList, mem_filter, mem_univ, true_and, hdiag]
    exact ⟨fun _ => hf.1, hf.2⟩
  have hinj : Function.Injective (fun f : ι → F => fun _ : Fin m => f) := by
    intro f g h
    exact congrFun h j0
  have hcard := Finset.card_le_card himage
  rw [Finset.card_image_of_injective _ hinj] at hcard
  exact le_trans hcard (hinter (fun _ : Fin m => u))

theorem exact_budget_iff {ι : Type*} [Fintype ι] {m B A : ℕ}
    (C : Submodule F (ι → F)) (hm : 1 ≤ m)
    (hgate : (B + 1).choose 2 ≤ Fintype.card F) :
    (∀ u, (scalarList C u A).card ≤ B) ↔
      (∀ u : Fin m → ι → F, (interleavedList C u A).card ≤ B) :=
  ⟨scalar_budget_to_interleaved C hm hgate, interleaved_budget_to_scalar C hm⟩

theorem grand_field_gate :
    Nat.choose (1073741824 + 1) 2 ≤ 365375409332725729550921208179070755120141565953 := by
  norm_num [Nat.choose_two_right]

theorem companion_field_gate :
    Nat.choose (274980728111395087 + 1) 2 ≤ 2130706433 ^ 6 := by
  norm_num [Nat.choose_two_right]

theorem scalar_carrier_field_gate :
    Nat.choose (12546010856 + 1) 2 ≤ 2130706433 ^ 6 := by
  norm_num [Nat.choose_two_right]

#print axioms avoid_proper_subspaces
#print axioms exists_separating_projection
#print axioms joint_agreements_le_projected
#print axioms scalar_budget_to_interleaved
#print axioms interleaved_budget_to_scalar
#print axioms exact_budget_iff
#print axioms grand_field_gate
#print axioms companion_field_gate
#print axioms scalar_carrier_field_gate

end AstraExactListProjection
