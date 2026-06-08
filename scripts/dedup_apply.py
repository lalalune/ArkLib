#!/usr/bin/env python3
"""Apply the actionable de-duplication / de-LARP changes from issue #257 in one pass.

This is the companion *write* script to the read-only `dedup_audit.py` /
`dedup_classify.py`.  It performs every change that was verified safe-to-automate by
manual + import-graph inspection, then leaves the remaining Lean-semantic fallout to be
fixed by hand with a compiler in the loop (see issue #257).

Run from the repo root:  `python scripts/dedup_apply.py`         (apply)
                         `python scripts/dedup_apply.py --check`  (dry-run / report)

Every transformation is idempotent: re-running is a no-op once applied.

Worklist implemented here
-------------------------
A1  Delete the superseded 1954-line monolith
    `Data/CodingTheory/ReedSolomon/FftDomain.lean` and migrate its sole importer
    `ProximityGap/Folding.lean` onto the refactored `Data/Domain/CosetFftDomain/*`
    split (a rename-and-rewire: monolith `subdomainNatReversed` == split `subdomain`,
    and the `subdomainNatReversed_*` lemma family maps signature-for-signature onto the
    split's `card_roots` / `square_roots_explicit` / `mem_subdomain_*`).  Also drops the
    monolith's `ArkLib.lean` umbrella import.

A2  De-duplicate the two `simulateQ_simOracle2_*` lemmas copy-pasted in
    `RingSwitching/BatchingPhase.lean`.  Their proofs are byte-identical to the originals in
    `RingSwitching/Prelude.lean` (imported by BatchingPhase).  We CANNOT just delete the local
    copies: an in-file `rw [simulateQ_simOracle2_query]` matches the goal only against a lemma
    elaborated in BatchingPhase's local context (the `OptionT (OracleComp …) _` placeholder),
    so deleting regresses that proof site.  Instead we keep the local statements as thin
    re-exports and replace the duplicated *proof bodies* with one-line delegations to the
    Prelude originals -- removing the real duplication without the regression.

    (NB: BatchingPhase.lean is independently red on unfinished issue-#29 WIP -- a missing
    `rbrExtractionFailureEvent` def, the unimplemented `ProbabilityTheory.prStx` notation, and a
    forward-ref to `batching_doom_escape_probability_bound`.  Those are out of scope here; this
    transform leaves the file no worse and is verified to elaborate past the simOracle2 site.)

C   Resolve the one remaining duplicate fully-qualified name
    `CodingTheory.qEntropy_mul_log_eq_qaryEntropy` (a hard umbrella-build clash): keep the
    canonical copy in `ProximityPrizeLeaves.lean` (4 importers) and re-export it from
    `ProximityPrizeLeaves2.lean` (3 importers) via import.

D   Annotate the intentional "do-NOT-dedup" files (mathlib-only worktree-resilience copies
    and audit witnesses) with a machine-readable marker so future dedup passes skip them.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


# --------------------------------------------------------------------------- helpers
class Changes:
    def __init__(self, check: bool):
        self.check = check
        self.touched: list[str] = []
        self.notes: list[str] = []

    def write(self, path: Path, new: str, old: str, label: str):
        rel = path.relative_to(ROOT).as_posix()
        if new == old:
            self.notes.append(f"  [skip] {label}: already applied ({rel})")
            return
        if not self.check:
            path.write_text(new, encoding="utf-8", newline="\n")
        self.touched.append(rel)
        self.notes.append(f"  [{'would-edit' if self.check else 'edit'}] {label}: {rel}")

    def delete(self, path: Path, label: str):
        rel = path.relative_to(ROOT).as_posix()
        if not path.exists():
            self.notes.append(f"  [skip] {label}: already deleted ({rel})")
            return
        if not self.check:
            path.unlink()
        self.touched.append(rel)
        self.notes.append(f"  [{'would-delete' if self.check else 'delete'}] {label}: {rel}")


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


ANNOTATION_TAG = "dedup-audit(#257):"


def annotate(c: Changes, rel: str, reason: str):
    """Insert a one-line de-LARP marker just after the copyright header block."""
    path = ROOT / rel
    if not path.exists():
        c.notes.append(f"  [skip] annotate: missing {rel}")
        return
    text = read(path)
    if ANNOTATION_TAG in text:
        c.notes.append(f"  [skip] annotate: already marked {rel}")
        return
    marker = f"-- {ANNOTATION_TAG} {reason}\n"
    lines = text.splitlines(keepends=True)
    # Insert after the first closing `-/` of the leading copyright comment, else at top.
    insert_at = 0
    if lines and lines[0].lstrip().startswith("/-"):
        for i, ln in enumerate(lines):
            if ln.strip() == "-/":
                insert_at = i + 1
                break
    new = "".join(lines[:insert_at]) + marker + "".join(lines[insert_at:])
    c.write(path, new, text, f"annotate ({reason.split(';')[0]})")


# --------------------------------------------------------------------------- A1
FOLDING = ROOT / "ArkLib/Data/CodingTheory/ProximityGap/Folding.lean"
MONOLITH = ROOT / "ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean"
ARKLIB_UMBRELLA = ROOT / "ArkLib.lean"

# Order matters: the four suffixed `*subdomainNatReversed*` names MUST be rewritten before
# the bare `subdomainNatReversed -> subdomain` rename (they contain it as a substring).
FOLDING_RENAMES: list[tuple[str, str]] = [
    ("CosetFftDomain.subdomainNatReversed_square_roots_explicit",
     "CosetFftDomainClass.square_roots_explicit"),
    ("CosetFftDomain.subdomainNatReversed_roots_card",
     "CosetFftDomainClass.card_roots"),
    ("CosetFftDomain.subdomainNatReversed_zero",
     "CosetFftDomainClass.mem_subdomain_0_iff_mem"),
    ("CosetFftDomain.mem_subdomainNatReversed_of_eq",
     "CosetFftDomainClass.mem_subdomain_of_eq_vals"),
    # bare function/method name (monolith subdomainNatReversed == split subdomain)
    ("subdomainNatReversed", "subdomain"),
    # namespace moves (class-level lemmas live under CosetFftDomainClass in the split)
    ("CosetFftDomain.mem_coset_finset_iff_mem_coset_domain",
     "CosetFftDomain.mem_toFinset_iff_mem"),
    ("CosetFftDomain.mem_coset_def", "CosetFftDomainClass.mem_def"),
    # NB: `injOn` / `injective` keep the concrete `CosetFftDomain.*` namespace -- the split
    # exposes both there (implicit `ω`), matching the monolith call sites verbatim.
    ("CosetFftDomain.subdomain_implies_char_ne_2",
     "CosetFftDomainClass.domain_implies_char_ne_2"),
    ("CosetFftDomain.size_of_smooth_coset_domain_eq_pow_of_2",
     "size_of_smooth_coset_domain_eq_pow_of_2"),
    # `toFinset` as an explicit simp-unfold target moves to the class namespace (the split's
    # `size_of_smooth_coset_domain_eq_pow_of_2` is stated via `CosetFftDomainClass.toFinset`).
    ("CosetFftDomain.toFinset", "CosetFftDomainClass.toFinset"),
]

OLD_IMPORT = "import ArkLib.Data.CodingTheory.ReedSolomon.FftDomain\n"
NEW_IMPORTS = (
    "import ArkLib.Data.Domain.CosetFftDomain.Subdomain\n"
    "import ArkLib.Data.Domain.CosetFftDomain.Log\n"
)
OLD_OPEN = "open Code Affine ReedSolomon\n"
NEW_OPEN = "open Code Affine ReedSolomon Domain\n"


def apply_a1(c: Changes):
    # 1. Migrate Folding.lean.
    text = read(FOLDING)
    new = text
    if OLD_IMPORT in new:
        new = new.replace(OLD_IMPORT, NEW_IMPORTS)
    if OLD_OPEN in new:
        new = new.replace(OLD_OPEN, NEW_OPEN)
    for old, repl in FOLDING_RENAMES:
        new = new.replace(old, repl)
    c.write(FOLDING, new, text, "A1 migrate Folding.lean onto Domain split")

    # 2. Delete the monolith.
    c.delete(MONOLITH, "A1 delete FftDomain monolith")

    # 3. Drop the umbrella import.
    text = read(ARKLIB_UMBRELLA)
    new = text.replace(OLD_IMPORT, "")
    c.write(ARKLIB_UMBRELLA, new, text, "A1 drop monolith import from ArkLib.lean")


# --------------------------------------------------------------------------- A2
BATCHING = ROOT / "ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean"

# The two duplicated proof BODIES (matched from their `:=`-tails so we keep each statement).
A2_MSGQ_OLD = '''      = (pure (OracleInterface.answer (t₂ qm.1) qm.2) : OracleComp oSpec _) := by
  change simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM ((oSpec + ([T₁]ₒ + [T₂]ₒ)).query (Sum.inr (Sum.inr qm)))) = _
  rw [simulateQ_spec_query]
  simp only [OracleInterface.simOracle2, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply]
  change liftM (OracleInterface.simOracle0 T₂ t₂ qm) = _
  simp only [OracleInterface.simOracle0]
  rfl'''

A2_MSGQ_NEW = '''      = (pure (OracleInterface.answer (t₂ qm.1) qm.2) : OracleComp oSpec _) :=
  -- dedup-audit(#257): delegate to the canonical proof in `RingSwitching/Prelude.lean`. The
  -- statement is kept as a local re-export so in-file `rw`s resolve it in local context.
  RingSwitching.simulateQ_simOracle2_messageQuery t₁ t₂ qm'''

A2_QUERY_OLD = '''      = (OptionT.lift (pure (OracleInterface.answer (t₂ qm.1) qm.2))
          : OptionT (OracleComp oSpec) _) := by
  rw [show (query (spec := [T₂]ₒ) qm : OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) _)
        = OptionT.lift (liftM (([T₂]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _) from rfl]
  rw [simulateQ_optionT_lift, simulateQ_simOracle2_messageQuery]
  rfl'''

A2_QUERY_NEW = '''      = (OptionT.lift (pure (OracleInterface.answer (t₂ qm.1) qm.2))
          : OptionT (OracleComp oSpec) _) :=
  -- dedup-audit(#257): delegate to the canonical proof in `RingSwitching/Prelude.lean`.
  RingSwitching.simulateQ_simOracle2_query t₁ t₂ qm'''


def apply_a2(c: Changes):
    text = read(BATCHING)
    new = text
    for old, repl, name in [(A2_MSGQ_OLD, A2_MSGQ_NEW, "messageQuery"),
                            (A2_QUERY_OLD, A2_QUERY_NEW, "query")]:
        if old in new:
            new = new.replace(old, repl)
        elif repl in new:
            c.notes.append(f"  [skip] A2 {name}: already delegated")
        else:
            c.notes.append(f"  [WARN] A2 {name}: proof body not found verbatim -- inspect manually")
    c.write(BATCHING, new, text,
            "A2 delegate duplicated simOracle2 proofs to Prelude (keep local statements)")


# --------------------------------------------------------------------------- C (qEntropy)
LEAVES2 = ROOT / "ArkLib/Data/CodingTheory/ProximityPrizeLeaves2.lean"

QENTROPY_DOC = '''/-- **Base-change bridge for the `q`-ary entropy** (re-proven locally so that this file
is self-contained). For `q ≥ 2`, ArkLib's `qEntropy` (base-`q` logs `Real.logb q`) times
`Real.log q` equals Mathlib's `Real.qaryEntropy` (natural logs).

The hypothesis `2 ≤ q` is necessary: for `q ∈ {0, 1}` we have `Real.log q = 0`, so the
LHS collapses to `0` while `qaryEntropy q x` is generally nonzero. -/
theorem qEntropy_mul_log_eq_qaryEntropy {q : ℕ} (hq : 2 ≤ q) (x : ℝ) :
    qEntropy q x * Real.log q = Real.qaryEntropy q x := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlog : Real.log q ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by
      intro h; rw [h] at hq1; exact lt_irrefl _ hq1)
  unfold qEntropy Real.qaryEntropy Real.binEntropy
  rw [Real.logb, Real.logb, Real.logb]
  push_cast
  rw [Real.log_inv, Real.log_inv]
  field_simp
  ring

'''

QENTROPY_REPLACEMENT = (
    "-- " + ANNOTATION_TAG + " `qEntropy_mul_log_eq_qaryEntropy` removed here to resolve the\n"
    "-- duplicate fully-qualified name (umbrella-build clash). Canonical copy lives in\n"
    "-- `ProximityPrizeLeaves.lean` and is re-exported via the import added above.\n\n"
)
LEAVES_IMPORT = "import ArkLib.Data.CodingTheory.ProximityPrizeLeaves\n"


def apply_c(c: Changes):
    text = read(LEAVES2)
    if QENTROPY_DOC not in text:
        if ANNOTATION_TAG in text:
            c.notes.append("  [skip] C: already applied (ProximityPrizeLeaves2.lean)")
        else:
            c.notes.append("  [WARN] C: qEntropy theorem block not found verbatim -- inspect Leaves2")
        return
    new = text.replace(QENTROPY_DOC, QENTROPY_REPLACEMENT)
    # Add the re-export import (after the last existing ArkLib import line for tidiness).
    if LEAVES_IMPORT not in new:
        lines = new.splitlines(keepends=True)
        last = max((i for i, ln in enumerate(lines)
                    if ln.startswith("import ArkLib.")), default=None)
        if last is not None:
            lines.insert(last + 1, LEAVES_IMPORT)
            new = "".join(lines)
    c.write(LEAVES2, new, text, "C dedup qEntropy_mul_log_eq_qaryEntropy (keep Leaves, re-export)")


# --------------------------------------------------------------------------- D annotations
INTENTIONAL = {
    # A5: mathlib-only Newton/Hensel worktree-resilience copies (do NOT re-import).
    "ArkLib/Data/Polynomial/NewtonLinearization.lean":
        "intentional mathlib-only origin for coeff_pow_sub_*; copies in Hensel* are deliberate "
        "worktree-resilience re-derivations -- do not re-import. See issue #257 A5.",
    "ArkLib/Data/Polynomial/HenselExistence.lean":
        "intentional mathlib-only re-derivation (self-contained, no ArkLib oleans). #257 A5.",
    "ArkLib/Data/Polynomial/HenselSeriesCoeff.lean":
        "intentional mathlib-only re-derivation (self-contained, no ArkLib oleans). #257 A5.",
    # A3: mathlib-only GS index re-derivation; unique MvPolynomial packaging is the real content.
    "ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean":
        "multIdx/mem_multIdx/card_multIdx are intentional local re-derivations; the "
        "MvPolynomial interpolant packaging is unique. Do not delete. #257 A3.",
    # A4: documented consolidation target; migrate consumers ONTO it (build-gated), don't delete.
    "ArkLib/ToMathlib/FinSumMvPolyBricks.lean":
        "intended consolidation target for finSumFinEquiv_symm_dite; also holds the unique "
        "degreeOf_sum_mul_prod_erase_le_card. Do not delete. #257 A4.",
    # D: deliberate audit witness.
    "ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean":
        "deliberate kernel-clean witness artifact for audit #49; fuller proof in "
        "FamilyRefutationComplete.lean. Not duplication. #257 D.",
}


def apply_d(c: Changes):
    for rel, reason in INTENTIONAL.items():
        annotate(c, rel, reason)


# --------------------------------------------------------------------------- main
def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true",
                    help="dry-run: report what would change without writing")
    args = ap.parse_args()

    c = Changes(check=args.check)
    print("=" * 72)
    print(f"  dedup_apply.py (#257)  {'[DRY-RUN]' if args.check else '[APPLY]'}")
    print("=" * 72)
    for name, fn in [("A1 FftDomain monolith", apply_a1),
                     ("A2 BatchingPhase simOracle2", apply_a2),
                     ("C  qEntropy FQN dedup", apply_c),
                     ("D  intentional-file annotations", apply_d)]:
        print(f"\n[{name}]")
        before = len(c.notes)
        fn(c)
        for n in c.notes[before:]:
            print(n)

    print("\n" + "-" * 72)
    uniq = sorted(set(c.touched))
    print(f"Files {'to change' if args.check else 'changed'}: {len(uniq)}")
    for f in uniq:
        print(f"  {f}")
    print("\nNext: build the affected targets and fix Lean fallout by hand, e.g.")
    print("  lake build ArkLib.Data.CodingTheory.ProximityGap.Folding")
    print("  lake build ArkLib.ProofSystem.RingSwitching.BatchingPhase")
    print("  lake build ArkLib.Data.CodingTheory.ProximityPrizeLeaves2")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
