import ArkLib.Data.CodingTheory.ProximityGap.Errors

namespace CodingTheory
open scoped NNReal
open ProximityGap Code

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

set_option linter.unusedSectionVars false in
theorem epsCA_le_one (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) :
    epsCA (F := F) C δ_fld δ_int ≤ 1 := by
  classical
  unfold epsCA
  apply iSup_le
  intro u
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp]; exact zero_le _
  · rw [if_neg hjp]; exact PMF.coe_le_one _ _

set_option linter.unusedSectionVars false in
theorem epsMCA_le_one (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) C δ ≤ 1 := by
  classical
  unfold epsMCA
  apply iSup_le
  intro u
  exact PMF.coe_le_one _ _

set_option linter.unusedSectionVars false in
theorem epsCA_curves_le_one (C : Set (ι → A)) (k : ℕ) (δ_fld δ_int : ℝ≥0) :
    epsCA_curves (F := F) C k δ_fld δ_int ≤ 1 := by
  classical
  unfold epsCA_curves
  apply iSup_le
  intro u
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp]; exact zero_le _
  · rw [if_neg hjp]; exact PMF.coe_le_one _ _

end CodingTheory
