import ArkLib.OracleReduction.BCS.Basic
import ArkLib.CommitmentScheme.Transparent
open OracleSpec OracleComp ProtocolSpec Commitment
namespace T
variable {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι} [oSpec.Fintype]
    {Data : Type} [O : OracleInterface Data] [∀ q : O.Query, DecidableEq (O.Response q)]
abbrev srcPSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Data]⟩
instance instM : ∀ i, OracleInterface ((srcPSpec (Data := Data)).Message i) | ⟨0, _⟩ => O
abbrev CommitmentType : (srcPSpec (Data := Data)).MessageIdx → Type := fun _ => Data
-- Is renameMessage CommitmentType defeq to srcPSpec?
example : (srcPSpec (Data := Data)).renameMessage (CommitmentType (Data := Data)) = srcPSpec := rfl
end T
