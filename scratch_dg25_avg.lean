import ArkLib.Data.Probability.Notation

open scoped ProbabilityTheory NNReal ENNReal BigOperators
open ProbabilityTheory

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Nonempty F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

-- sanity checks on the API we will use
#check @Pr_eq_tsum_indicator
#check (PMF.uniformOfFintype (ι → F))
#check @PMF.uniformOfFintype_apply
example (w : ι → F) (γ : F) : (ι → F) ≃ (ι → F) := Equiv.addRight (γ • w)
#check @Equiv.sum_comp
#check @tsum_fintype
