import ArkLib.ProofSystem.ProtocolSpec

open ProtocolSpec

variable {R : Type} [CommRing R]
#synth ∀ i, OracleInterface (!p[].Message i)
