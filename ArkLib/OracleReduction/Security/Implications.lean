/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.Security.ImplicationsCore

/-!
# Implications between security notions

This compatibility module keeps the historical import target available.  The implication
theorems of the security-notion lattice now live in `Security/ImplicationsCore.lean`
(re-exported here):

* `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness` (⚠ see the vacuity note there:
  the scalar `knowledgeSoundness` definition is trivially satisfiable; the genuine
  extractor-exhibiting bound is `…_genuine_of_marginal` / `…_genuine`);
* `Verifier.rbrKnowledgeSoundness_implies_rbrSoundness`;
* `Verifier.rbrSoundness_implies_soundness_of_marginal` (the unconditional form is false
  under the current definitions);
* `knowledgeSoundness → soundness` remains documented-open (false as literally stated; see
  the obstruction list in `ImplicationsCore`).
-/

noncomputable section

namespace Verifier

section Implications

end Implications

end Verifier
