import ArkLib.ProofSystem.ToyProblem.Leaderboard
import ArkLib.ToMathlib.KoalaBearField
import ArkLib.ToMathlib.KoalaBearCode

open ToyProblem KoalaBear

-- Field-theory layer
#print axioms KoalaBear.card_sextic
#print axioms KoalaBear.card_sextic_le_186
#print axioms KoalaBear.card_sextic_ge
#print axioms KoalaBear.card_sextic_ge_180
-- Code layer
#print axioms KoalaBear.rsEncoder
#print axioms KoalaBear.rsCode_isLinear
-- Numeric anchors (the deliverable)
#print axioms ToyProblem.two_rpow_neg_natCast
#print axioms ToyProblem.winningSetSoundness_concrete_ge_of_card
#print axioms ToyProblem.fenziSanso_upperBound_attack_concrete
#print axioms ToyProblem.spotCheck_le_two_pow_neg_64
#print axioms ToyProblem.koalaIRSConcrete
#print axioms ToyProblem.card_koalaIRSConcrete_F
