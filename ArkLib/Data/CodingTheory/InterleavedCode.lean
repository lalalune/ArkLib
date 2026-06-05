/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import ArkLib.Data.Fin.Basic
import ArkLib.Data.CodingTheory.Prelims
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENat.Lattice
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Qify
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Data.NNReal.Defs

/-!
## Main definitions

Interleaved codes for generic codes over a semiring, with **unified global APIs**.

### Core Data Types
1. **Single vector data structure**: used for computation
  - **Word**: `(ι → A)` - a word
  - **Codeword**: `(C : Set (ι → A))` - a codeword in base code `C`
2. **Horizontal interleaved data structure**: used for computation, the underlying data structure is
  `Matrix κ ι A`
  - **WordStack**: `Matrix κ ι A` - each row is a word
  - **CodewordStack**: `codewordStackSet (κ := κ) (C := C)` - each row is a codeword in C
3. **Vertical interleaved data structure**: used for security (e.g. Δ₀, δᵣ, ...), the underlying
  data structure is `Matrix ι κ A`
  `(κ → A)`.
  - **InterleavedWord**: `Matrix ι κ A`
  - **InterleavedCodeword**: `interleavedCodeSet (κ := κ) (C := C)`

### Global Unified APIs (Type Classes)
- **`GetRow α RowIdx RowType`** - extract rows uniformly across structures
- **`GetSymbol α SymbolIdx SymbolType`** - extract symbols uniformly
- **`GetCell α RowIdx SymbolIdx CellTy`** - extract individual cells
- **`Interleavable α β`** - interleave structures (notation: `⋈|u`)
- **`Interleavable₂ α β`** - interleave two structures (notation: `u ⋈₂ v`)
- **`CodeInterleavable Code InterleavedCode`** - interleave codes (notation: `C^⋈κ`)
- **`Stackifiable α β`** - inverse of interleaving (notation: `⋈⁻¹|v`)

### Key Set
- **`interleavedCodeSet C`** - set of interleaved codewords for code `C`
- **`codewordStackSet C`** - set of codeword stacks for code `C`
- **`ModuleCode.moduleInterleavedCode`** - interleaved code as
  `ModuleCode ι F (InterleavedSymbol A κ)` (preserves submodule; used with `C^⋈κ`)
- **`ModuleCode.codewordStackSubmodule`** - codeword stack as
  `Submodule F (WordStack A κ ι)` (preserves submodule for horizontal interleaving)

### Joint Proximity & Agreement (Consequent of Proximity Gap)
- **`jointProximity u δ`** - interleaved `u` within relative distance `δ` of `C^⋈κ`
- **`jointProximityNat u e`** - interleaved `u` within concrete distance `e` of `C^⋈κ`
- **`jointProximity₂ u₀ u₁ δ`** - interleaved pair within relative distance `δ` of `C^⋈(Fin 2)`
- **`jointProximityNat₂ u₀ u₁ e`** - interleaved pair within concrete distance `e` of `C^⋈(Fin 2)`
- **`pairJointProximity u v e`** - two interleaved stacks within distance `e` of each other
- **`pairJointProximity₂ u₀ u₁ v₀ v₁ e`** - two interleaved pairs within distance `e` of each other
- **`jointAgreement C δ W`** - words collectively agree on large set with `C`
  (equivalent to `jointProximity`)

## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]
    * NB we use version 20210703:203025

* [Ames, S., Hazay, C., Ishai, Y., and Venkitasubramaniam, M., *Ligero: Lightweight sublinear
    arguments without a trusted setup*][AHIV22]

* [Diamond, B. E. and Gruen, A., *Proximity Gaps in Interleaved Codes*, In: IACR
  Communications in Cryptology 1.4 (Jan. 13, 2025). issn: 3006-5496. doi: 10.62056/a0ljbkrz.][DG25]
-/

section InterleavedCodeDefinitions
variable (F : Type*) [Semiring F]
variable (A : Type*) [AddCommMonoid A] [Module F A]
variable (κ ι : Type*) [Fintype κ] [Fintype ι]
variable (MC : ModuleCode ι F A)
variable (C : Set (ι → A))

open NNReal
namespace Code

/-- A word is a vector (ι → A) -/
@[simp]
abbrev Word := ι → A

/-- A codeword is a vector (ι → A) that belongs to the base module code MC -/
@[simp]
abbrev Codeword := MC

@[simp]
abbrev InterleavedSymbol := κ → A

/-- A word stack is a (row-wise) matrix (κ → ι → A) where each ROW is a word -/
@[simp]
abbrev WordStack := Matrix κ ι A

@[simp]
def WordStack.getRowWord {A : Type*} {κ : Type*} {ι : Type*} (u : WordStack A κ ι)
    (k : κ) : Word A ι := u k

@[simp]
def WordStack.getSymbol {A : Type*} {κ : Type*} {ι : Type*} (u : WordStack A κ ι)
    (i : ι) : InterleavedSymbol A κ := u.transpose i

/-- An interleaved word is a (column-wise) matrix (ι → (κ → A)) where each ROW is a word, each
  column i is a symbol (κ → A) for the interleaved code MC^⋈ κ. -/
@[simp]
abbrev InterleavedWord := Matrix ι κ A

@[simp]
def InterleavedWord.getRowWord {A : Type*} {κ : Type*} {ι : Type*}
    (v : InterleavedWord A κ ι) (k : κ) : Word A ι := v.transpose k

@[simp]
def InterleavedWord.getSymbol {A : Type*} {κ : Type*} {ι : Type*}
    (v : InterleavedWord A κ ι) (i : ι) : InterleavedSymbol A κ := v i

/-- The set of interleaved words where each row belongs to a code C.
    This is a generic version that works for any code represented as a Set. -/
@[simp]
def interleavedCodeSet {A : Type*} {κ ι : Type*}
    (C : Set (ι → A)) : Set (Matrix ι κ A) :=
  { V : Matrix ι κ A | ∀ k : κ, V.transpose k ∈ C }

/-- If C is finite and membership is decidable, then interleavedCodeSet C is finite. -/
@[simp]
noncomputable instance interleavedCodeSet_fintype {A : Type*} {κ ι : Type*}
    [Fintype κ] [Fintype ι] [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) :
    Fintype (interleavedCodeSet (κ := κ) (ι := ι) C) := by
  exact Fintype.ofFinite (interleavedCodeSet C)

/-- Interleaved code submodule of any `ModuleCode`, where each row belongs to the code. -/
@[simp]
instance ModuleCode.moduleInterleavedCode : ModuleCode ι F (InterleavedSymbol A κ) := {
  -- Simple condition wrapping over Matrix
  carrier := interleavedCodeSet (C := (MC : Set (ι → A)))
  add_mem' hU hV i := MC.add_mem (hU i) (hV i)
  zero_mem' _ := MC.zero_mem
  smul_mem' a _ hV i := MC.smul_mem a (hV i)
}

-- Note: lift these to CodeInterleavable
omit [Fintype κ] [Fintype ι] [AddCommMonoid A] in
@[simp]
lemma mem_interleavedCode_iff (v : InterleavedWord A κ ι) : -- column-wise matrix
    v ∈ interleavedCodeSet (C := C) ↔ ∀ k, InterleavedWord.getRowWord v k ∈ C := by rfl

omit [Fintype κ] [Fintype ι] in
lemma mem_moduleInterleavedCode_iff (v : InterleavedWord A κ ι) :
    v ∈ ModuleCode.moduleInterleavedCode (F := F) (A := A) (κ := κ) (ι := ι) (MC := MC)
    ↔ ∀ k, InterleavedWord.getRowWord v k ∈ MC := by exact Eq.to_iff rfl

@[simp]
def codewordStackSet {A : Type*} {κ ι : Type*} (C : Set (ι → A)) : Set (WordStack A κ ι) :=
  { V : WordStack A κ ι | ∀ k, V.getRowWord k ∈ C }

@[simp]
instance ModuleCode.codewordStackSubmodule : Submodule F (WordStack A κ ι) := {
  -- Simple condition wrapping over Matrix
  carrier := codewordStackSet (C := (MC : Set (ι → A)))
  add_mem' hU hV i := MC.add_mem (hU i) (hV i)
  zero_mem' _ := MC.zero_mem
  smul_mem' a _ hV i := MC.smul_mem a (hV i)
}

omit [Fintype κ] [Fintype ι] in
lemma codewordStackSubmodule_eq_codewordStackSet (MC : ModuleCode ι F A) :
    ((ModuleCode.codewordStackSubmodule (MC := MC) F A κ ι) : Set (WordStack A κ ι))
      = codewordStackSet (MC : Set (ι → A)) := rfl

instance instMembershipWordStackCodewordStackSet : Membership (α := WordStack A κ ι)
  (γ := codewordStackSet (κ := κ) (C := C)) where
  mem u := by exact fun a ↦ PEmpty.{0}

instance instMembershipInterleavedWordInterleavedCodeSet :
  Membership (InterleavedWord A κ ι) (interleavedCodeSet (κ := κ) (C := C)) where
  mem u := by exact fun a ↦ PEmpty.{0}

omit [Fintype κ] [Fintype ι] [AddCommMonoid A] in
@[simp]
lemma mem_codewordStack_iff (u : WordStack A κ ι) : -- row-wise matrix
    u ∈ codewordStackSet (κ := κ) (C := C) ↔ ∀ k, u.getRowWord k ∈ C := by rfl

omit [Fintype κ] [Fintype ι] in
@[simp]
lemma mem_moduleCodewordStack_iff (u : WordStack A κ ι) : -- might rename this
    u ∈ ModuleCode.codewordStackSubmodule (F := F) (A := A) (κ := κ) (ι := ι) (MC := MC)
    ↔ ∀ k, u.getRowWord k ∈ MC := by exact Eq.to_iff rfl

/-- An interleaved codeword is a (column-wise) matrix (ι → (κ → A)) where each ROW is a codeword
  of the base module code MC. -/
@[simp]
abbrev InterleavedCodeword := interleavedCodeSet (κ := κ) (C := C)

/-- A codeword stack is a (row-wise) matrix (κ → ι → A) where each ROW is a codeword of MC. -/
@[simp]
abbrev CodewordStack := codewordStackSet (κ := κ) (C := C)

-- Note: mem of Module interleaved code, Module codeword stack

@[simp]
def interleaveWordStack {A : Type*} {κ ι : Type*} (u : WordStack A κ ι) : InterleavedWord A κ ι
    := u.transpose

/-- Interleave a codeword stack into an interleaved codeword. -/
@[simp]
def interleaveCodewordStack (u : CodewordStack A κ ι C) : InterleavedCodeword A κ ι C :=
  ⟨interleaveWordStack u.val, by
    rw [mem_interleavedCode_iff]
    let h_u_mem := u.property
    rw [mem_codewordStack_iff] at h_u_mem
    intro k
    exact h_u_mem k
  ⟩

@[simp]
def finMapTwoWords {A : Type*} {ι : Type*} (u₀ u₁ : Word A ι)
    : WordStack A (κ := Fin 2) (ι := ι)
    := fun rowIdx =>
  match rowIdx with
  | ⟨0, _⟩ => u₀
  | ⟨1, _⟩ => u₁

@[simp]
def finMapTwoCodewords (u₀ u₁ : C) :
    CodewordStack A (κ := Fin 2) (ι := ι) C :=
  ⟨finMapTwoWords u₀ u₁, by
    simp only [WordStack, CodewordStack, codewordStackSet, Word, WordStack.getRowWord,
      Set.mem_setOf_eq, finMapTwoWords]
    intro k
    match k with
    | 0 => simp only [Subtype.coe_prop]
    | 1 => simp only [Subtype.coe_prop]
  ⟩

/-- Interleave two codewords u₀ and u₁ into a single interleaved codeword -/
@[simp]
def interleaveTwoWords (u₀ u₁ : Word A ι) : InterleavedWord A (Fin 2) ι :=
  interleaveWordStack (κ := Fin 2) (ι := ι) (u := finMapTwoWords u₀ u₁)

@[simp]
def interleaveTwoCodewords (u₀ u₁ : C) : InterleavedCodeword A (κ := Fin 2) ι C :=
  interleaveCodewordStack A (κ := Fin 2) (ι := ι) (u := finMapTwoCodewords A ι C u₀ u₁)

/-- Combine two codeword stacks with different κ types by stacking vertically -/
@[simp]
def finMapCodewordStacksAppend {κ₁ κ₂ : Type*}
    (u : CodewordStack A κ₁ ι C) (v : CodewordStack A κ₂ ι C) :
    CodewordStack A (Sum κ₁ κ₂) ι C :=
  ⟨fun s =>
    match s with
    | Sum.inl k₁ => u.val k₁
    | Sum.inr k₂ => v.val k₂, by
    simp only [WordStack, CodewordStack, mem_codewordStack_iff]
    intro s
    match s with
    | Sum.inl k₁ =>
      have h_u := u.property
      rw [mem_codewordStack_iff] at h_u
      simp only [WordStack.getRowWord]
      exact h_u k₁
    | Sum.inr k₂ =>
      have h_v := v.property
      rw [mem_codewordStack_iff] at h_v
      simp only [WordStack.getRowWord]
      exact h_v k₂
  ⟩

/-- Type class for overloading the interleave notation.
Interleaving a word stack -> interleaved word
Interleaving a codeword stack -> interleaved codeword -/
class Interleavable (α : Type*) (β : outParam Type*) where
  interleave : α → β
notation:65 "⋈|" u => Interleavable.interleave u

class Interleavable₂ (α : Type*) (β : outParam Type*) where
  interleave₂ : α → α → β
notation:65 u "⋈₂" v => Interleavable₂.interleave₂ u v

/-- Typeclass for interleaving codes (preserving their structure).
    For Set → Set, for ModuleCode → ModuleCode, etc. -/
class CodeInterleavable.{u, v} (Code : Type*) (InterleavedCode : outParam (Type u → Type v)) where
  interleaveCode : Code → (κ : Type u) → InterleavedCode κ

notation:20 C "^⋈" κ => @CodeInterleavable.interleaveCode _ _ _ C κ

@[simp]
instance : Interleavable (α := WordStack A κ ι) (β := InterleavedWord A κ ι) where
  interleave := interleaveWordStack

@[simp]
instance : Interleavable (α := CodewordStack A κ ι C) (β := InterleavedCodeword A κ ι C) where
  interleave u := ⟨interleaveWordStack u.val, by
    rw [mem_interleavedCode_iff]
    let h_u_mem := u.property
    rw [mem_codewordStack_iff] at h_u_mem
    intro k
    exact h_u_mem k
  ⟩

@[simp]
instance : Interleavable (α := ModuleCode.codewordStackSubmodule F A κ ι (MC := MC))
    (β := ModuleCode.moduleInterleavedCode F A κ ι (MC := MC)) where
  interleave u := interleaveCodewordStack (κ := κ) (ι := ι) (u := u)

@[simp]
instance : Interleavable₂ (α := Word A ι) (β := InterleavedWord A (Fin 2) ι) where
  interleave₂ u₀ u₁ := interleaveTwoWords A ι u₀ u₁

@[simp]
instance : Interleavable₂ (α := C) (β := InterleavedCodeword A (κ := (Fin 2)) ι C) where
  interleave₂ u₀ u₁ := interleaveTwoCodewords A ι C u₀ u₁

/-- Interleave a Set-based code into an interleaved code set. -/
@[simp]
instance : CodeInterleavable (Code := Set (ι → A))
    (InterleavedCode := fun κ => Set (Matrix ι κ A)) where
  interleaveCode C := fun κ => interleavedCodeSet (κ := κ) C

/-- Interleave a ModuleCode into an interleaved ModuleCode (preserving submodule structure). -/
@[simp]
instance : CodeInterleavable (Code := ModuleCode ι F A)
    (InterleavedCode := fun κ => ModuleCode ι F (InterleavedSymbol A κ)) where
  interleaveCode MC := fun κ => ModuleCode.moduleInterleavedCode
    (F := F) (A := A) (κ := κ) (ι := ι) (MC := MC)

omit [AddCommMonoid A] [Fintype κ] [Fintype ι] in
@[simp]
lemma interleave_wordStack_eq (u : WordStack A κ ι) : (⋈|u) = u.transpose := rfl

omit [AddCommMonoid A] [Fintype κ] [Fintype ι] in
@[simp]
lemma interleave_codewordStack_val_eq (u : CodewordStack A κ ι C) :
    (⋈| u).val = u.val.transpose := rfl

@[simp]
noncomputable instance instFintypeInterleavedModuleCode [Fintype A] : Fintype (MC ^⋈ κ) := by
  exact Fintype.ofFinite ((MC ^⋈ κ) : Set (ι → (κ → A)))

@[simp]
lemma interleavedCode_eq_interleavedCodeSet {A : Type*} {ι : Type*} {κ : Type*} {C : Set (ι → A)} :
    (C ^⋈ κ) = interleavedCodeSet (κ := κ) C:= by rfl

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
-- Column projection shrinks relative Hamming distance for interleaved words.
lemma relHammingDist_transpose_le {F : Type*} [DecidableEq F] [Fintype ι] [Nonempty ι] {m : ℕ}
    (f V : Matrix ι (Fin m) F) (k : Fin m) :
    δᵣ(V.transpose k, f.transpose k) ≤ δᵣ(V, f) := by
  unfold relHammingDist
  have h : hammingDist (V.transpose k) (f.transpose k) ≤ hammingDist V f := by
    have := hammingDist_comp_le_hammingDist (γ := fun _ : ι => Fin m → F)
      (β := fun _ : ι => F) (fun (_ : ι) (row : Fin m → F) => row k) (x := V) (y := f)
    simpa [Matrix.transpose] using this
  gcongr

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- A close interleaved codeword projects, column-wise, to a codeword of the base code. -/
lemma closeCodewordsRel_interleaved_transpose_mem_code {F : Type*}
    {m : ℕ} {C : Set (ι → F)} {δ : ℝ}
    {f V : Matrix ι (Fin m) F}
    (hV : V ∈ ListDecodable.closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ)
    (k : Fin m) :
    V.transpose k ∈ C :=
  hV.1 k

@[simp]
lemma interleavedCode_eq_interleavedCodeSet_of_moduleCode {F A : Type*} {κ ι : Type*} [Semiring F]
    [AddCommMonoid A] [Module F A] {MC : ModuleCode ι F A} :
    ((MC ^⋈ κ) : Set (ι → (κ → A))) = interleavedCodeSet (κ := κ) (C := (MC : Set (ι → A)))
    := by rfl

@[simp]
instance {κ₁ κ₂ : Type*} :
    HAppend (WordStack A κ₁ ι) (WordStack A κ₂ ι) (WordStack A (Sum κ₁ κ₂) ι) where
  hAppend u v := fun s =>
    match s with
    | Sum.inl k₁ => u k₁
    | Sum.inr k₂ => v k₂

@[simp]
instance {κ₁ κ₂ : Type*} :
    HAppend (CodewordStack A κ₁ ι C) (CodewordStack A κ₂ ι C)
      (CodewordStack A (Sum κ₁ κ₂) ι C) where
  hAppend u v := finMapCodewordStacksAppend A ι C (κ₁ := κ₁) (κ₂ := κ₂) u v


namespace InterleavedCode

/-!
  ## Interleaved Code Structure
  Implementation of the 7-step blueprint for Interleaved Codes.
-/

variable (RowIdx SymbolIdx : Type*)
variable (RowType SymbolType CellTy : Type*)

/-! ### 1, 2, 3. Accessors -/

/-- 1. GetRow -/
class GetRow (α : Type*) (RowIdx RowType : outParam Type*) where
  getRow : (u : α) → (rowIdx : RowIdx) → RowType

/-- 2. GetSymbol -/
class GetSymbol (α : Type*) (SymbolIdx SymbolType : outParam Type*) where
  getSymbol : (u : α) → (symbolIdx : SymbolIdx) → SymbolType

/-- 3. GetCell -/
class GetCell (α : Type*) (RowIdx SymbolIdx : Type*) (CellTy : outParam Type*) where
  getCell : (u : α) → (rowIdx : RowIdx) → (symbolIdx : SymbolIdx) → CellTy

export GetRow (getRow)
export GetSymbol (getSymbol)
export GetCell (getCell)

/-- 6. InterleavedStructure: Extends accessors and defines equality via rows/symbols/cells.
    Applied to the InterleavedElementType. -/
class InterleavedStructure (α : Type*) (RowIdx SymbolIdx : outParam Type*)
    (RowType SymbolType CellTy : outParam Type*)
    extends GetRow α RowIdx RowType,
            GetSymbol α SymbolIdx SymbolType,
            GetCell α RowIdx SymbolIdx CellTy where
  eq_iff_all_rows_eq {u v : α} : u = v ↔ ∀ i, getRow u i = getRow v i
  eq_iff_all_symbols_eq {u v : α} : u = v ↔ ∀ k, getSymbol u k = getSymbol v k
  eq_iff_all_cells_eq {u v : α} : u = v ↔ ∀ i k, getCell u i k = getCell v i k

export InterleavedStructure (eq_iff_all_rows_eq eq_iff_all_symbols_eq eq_iff_all_cells_eq)

-- WordStack
@[simp] instance (priority := 500) instInterleavedStructureWordStack :
    InterleavedStructure (α := WordStack A κ ι) (RowIdx := κ) (SymbolIdx := ι)
      (RowType := Word A ι) (SymbolType := InterleavedSymbol A κ) (CellTy := A) where
  getRow u k := WordStack.getRowWord u k
  getSymbol u i := WordStack.getSymbol u i
  getCell u k i := (WordStack.getRowWord u k) i
  eq_iff_all_rows_eq := by
    intro u v; constructor
    · intro h; exact fun i ↦ congrFun h i
    · intro h; ext i k; exact congrFun (h i) k
  eq_iff_all_symbols_eq := by
    intro u v; constructor
    · intro h; exact fun k ↦ congrFun (congrArg Matrix.transpose h) k
    · intro h; ext i k; exact congrFun (h k) i
  eq_iff_all_cells_eq := by
    intro u v; constructor
    · intro h; exact fun i k ↦ congrFun (congrFun h i) k
    · intro h; ext i k; exact h i k

-- CodewordStack
@[simp] instance instInterleavedStructureCodewordStack :
    InterleavedStructure (α := CodewordStack A κ ι C) (RowIdx := κ)
  (SymbolIdx := ι) (RowType := C) (SymbolType := InterleavedSymbol A κ) (CellTy := A) where
  getRow u k := ⟨u.val k, by -- No separate functions because CodewordStack is a subtype
    have h_u_mem := u.property
    rw [mem_codewordStack_iff] at h_u_mem
    exact h_u_mem k
  ⟩
  getSymbol u i := u.val.transpose i
  getCell u k i := u.val k i
  eq_iff_all_rows_eq := by
    intro u v; constructor
    · intro h; rw [h]; exact fun i ↦ rfl
    · intro h; ext i k;
      let res := h i; simp only [WordStack, codewordStackSet, Word, WordStack.getRowWord,
        Set.mem_setOf_eq, Subtype.mk.injEq] at res; exact congrFun res k
  eq_iff_all_symbols_eq := by
    intro u v; constructor
    · intro h; rw [h]; exact fun k ↦ rfl
    · intro h; ext i k;
      let res := h k; simp only [WordStack, codewordStackSet, Word,
        Set.mem_setOf_eq] at res; exact congrFun res i
  eq_iff_all_cells_eq := by
    intro u v; constructor
    · intro h; rw [h]; exact fun i k ↦ rfl
    · intro h; ext i k;
      let res := h i k; simp only [WordStack, codewordStackSet, Word,
        Set.mem_setOf_eq] at res; exact res

-- InterleavedWord
@[simp] instance instInterleavedStructureInterleavedWord :
    InterleavedStructure (α := InterleavedWord A κ ι) (RowIdx := κ)
  (SymbolIdx := ι) (RowType := Word A ι) (SymbolType := InterleavedSymbol A κ) (CellTy := A) where
  getRow u i := InterleavedWord.getRowWord u i
  getSymbol u k := InterleavedWord.getSymbol u k
  getCell u i k := (InterleavedWord.getRowWord u i) k
  eq_iff_all_rows_eq := by
    intro u v; constructor
    · intro h; exact fun k ↦ congrFun (congrArg Matrix.transpose h) k
    · intro h; ext i k; exact congrFun (h k) i
  eq_iff_all_symbols_eq := by
    intro u v; constructor
    · intro h; exact fun k ↦ congrFun h k
    · intro h; ext i k; exact congrFun (h i) k
  eq_iff_all_cells_eq := by
    intro u v; constructor
    · intro h; exact fun i k ↦ congrFun (congrFun h k) i
    · intro h; ext k i; exact h i k

-- InterleavedCodeword
@[simp] instance instInterleavedStructureInterleavedCodeword :
    InterleavedStructure (α := InterleavedCodeword A κ ι C) (RowIdx := κ)
  (SymbolIdx := ι) (RowType := C) (SymbolType := InterleavedSymbol A κ) (CellTy := A) where
  -- No separate functions cuz InterleavedCodeword is a subtype
  getRow u k := ⟨(Matrix.transpose u) k, by
    have h_u_mem := u.property
    rw [mem_interleavedCode_iff] at h_u_mem
    exact h_u_mem k
  ⟩
  getSymbol u colIdx := u.val colIdx
  getCell u k i := Matrix.transpose u k i
  eq_iff_all_rows_eq := by
    intro u v; constructor
    · intro h; rw [h]; exact fun i ↦ rfl
    · intro h; ext i k;
      let res := h k; simp only [Subtype.mk.injEq] at res; exact congrFun res i
  eq_iff_all_symbols_eq := by
    intro u v; constructor
    · intro h; rw [h]; exact fun k ↦ rfl
    · intro h; ext i k;
      let res := h i; simp only at res; exact congrFun res k
  eq_iff_all_cells_eq := by
    intro u v; constructor
    · intro h; rw [h]; exact fun i k ↦ rfl
    · intro h; ext i k; exact h k i

class Stackifiable (α : Type*) (β : outParam Type*) where
  stackify : α → β

notation:65 "⋈⁻¹|" u => Stackifiable.stackify u

@[simp]
instance : Stackifiable (α := InterleavedWord A κ ι) (β := WordStack A κ ι) where
  stackify u := u.transpose

@[simp]
instance : Stackifiable (α := InterleavedCodeword A κ ι C) (β := CodewordStack A κ ι C) where
  stackify u := ⟨u.val.transpose, by
    rw [mem_codewordStack_iff]
    let h_u_mem := u.property
    rw [mem_interleavedCode_iff] at h_u_mem
    intro k
    exact h_u_mem k
  ⟩

omit [AddCommMonoid A] [Fintype κ] [Fintype ι] in
/-- Used to getRow at u.val instead of getRow u -/
@[simp]
lemma getRowOfInterleavedCodeword_mem_code (C : Set (ι → A))
    (u : CodeInterleavable.interleaveCode (C) κ) (rowIdx : κ) :
    getRow (u.val) rowIdx ∈ C := by
  let getRowAsIC := getRow (show InterleavedCodeword A κ ι C from u) rowIdx
  exact getRowAsIC.property

omit [AddCommMonoid A] [Fintype κ] [Fintype ι] in
/-- Used to getRow at u.val instead of getRow u -/
@[simp]
lemma getRowOfCodewordStack_mem_code (C : Set (ι → A))
    (u : CodewordStack A κ ι C) (rowIdx : κ) :
    u.val rowIdx ∈ C := by
  have := u.property
  rw [mem_codewordStack_iff] at this
  exact this rowIdx

/-- Notation for stacking one stack on top of another -/
infixl:65 " ++ₕ " => HAppend.hAppend

@[simp]
instance instNonemptyInterleavedCode [Nonempty C] :
    Nonempty (C ^⋈ κ) := by
  let c : C := Classical.arbitrary C
  use fun i k => c.val i
  intro k
  exact c.property

example (C : Set (ι → A)) : ((C ^⋈ (Fin 2))) = interleavedCodeSet (κ := Fin 2) C
    := by rfl
example (MC : ModuleCode ι F A) : (MC ^⋈ (Fin 2))
    = ModuleCode.moduleInterleavedCode (F := F) (A := A) (κ := Fin 2) (ι := ι) (MC := MC)
    := by rfl
example (u : CodewordStack A κ ι C) :
  let iuCodewords: InterleavedCodeword A κ ι C := ⋈|u
  let iuWords: InterleavedWord A κ ι := ⋈|u.val
  iuCodewords.val = iuWords := by rfl
example (v₀ v₁ : C) :
  let iv_codeword : InterleavedWord A (Fin 2) ι := v₀.val ⋈₂ v₁.val
  let iv_word : InterleavedCodeword A (Fin 2) ι C := v₀ ⋈₂ v₁
  iv_codeword = iv_word := by rfl

end InterleavedCode

/-! ### Distance Properties for Interleaved Codes
**Naming conventions**:
- by default, when we say "interleaved word", it means the interleaved word of a
  `WordStack` (i.e. using notation `⋈|`).
- if the definition has `₂` at the end of its name, it means the interleaved word is of two
  `Word`s (i.e. using notation `⋈₂`).
- prefix `joint` or `pairjoint` :
  + `joint`: involves distance **from an interleaved word to the interleaved code `C^⋈ κ`**
  + `pairJoint`: involves distance **between two interleaved words**
- suffix `Nat` : the proximity is represented in terms of concrete distance (`Δ₀`),
  without this suffix, relative distance (`δᵣ`) is used instead.
-/
section JointProximityDefinitions

-- variable [DecidableEq A] [DecidableEq ι]

variable {κ ι : Type*} [Fintype ι] [Fintype κ]
  {A : Type*} (C : Set (ι → A)) [DecidableEq A]

/-- `jointProximity u δ` means the interleaved word stack `u` is within relative distance `δ` of
the interleaved code `MC^⋈ κ`. -/
def jointProximity (u : WordStack A κ ι) (δ : NNReal) : Prop :=
  let u_interleaved : InterleavedWord A κ ι := ⋈|u
  δᵣ(u_interleaved, interleavedCodeSet C) ≤ δ

/-- `jointProximity₂ u₀ u₁ e` means the interleaved pair `(u₀, u₁)` is within distance
`e` of the interleaved code `MC^⋈ (Fin 2)`. -/
def jointProximity₂ (u₀ u₁ : Word A ι) (δ : NNReal) : Prop :=
  let u_stack : WordStack A (Fin 2) ι := finMapTwoWords u₀ u₁
  jointProximity C (u := u_stack) δ

/-- `jointProximityNat u e` means the interleaved word stack `u` is within distance `e` of
the interleaved code `MC^⋈ κ`. Can use `distFromCode_le_iff_relDistFromCode_le` and
`relDistFromCode_le_iff_distFromCode_le` to prove equivalence with `jointProximity`. -/
def jointProximityNat (u : WordStack A κ ι) (e : ℕ) : Prop :=
  let u_interleaved : InterleavedWord A κ ι := ⋈|u
  Δ₀(u_interleaved, (interleavedCodeSet C)) ≤ e

/-- `jointProximityNat₂ u₀ u₁ e` means the interleaved pair `(u₀, u₁)` is within distance
`e` of the interleaved code `MC^⋈ (Fin 2)`. -/
def jointProximityNat₂ (u₀ u₁ : Word A ι) (e : ℕ) : Prop :=
  let u_stack : WordStack A (Fin 2) ι := finMapTwoWords u₀ u₁
  jointProximityNat C (u := u_stack) e

/-- `pairJointProximity u v e` means the two interleaved word stacks `u` and `v`
are within distance `e` of each other. -/
def pairJointProximity (u v : WordStack A κ ι) (e : ℕ) : Prop :=
  let u_interleaved : InterleavedWord A κ ι := ⋈|u
  let v_interleaved : InterleavedWord A κ ι := ⋈|v
  Δ₀(u_interleaved, v_interleaved) ≤ e

/-- `pairJointProximity₂ u₀ u₁ v₀ v₁ e` means the interleaved pairs `(u₀, u₁)` and `(v₀, v₁)`
  are within distance `e` of each other. -/
def pairJointProximity₂ (u₀ u₁ v₀ v₁ : Word A ι) (e : ℕ) : Prop :=
  let u_interleaved : InterleavedWord A (Fin 2) ι := u₀ ⋈₂ u₁
  let v_interleaved : InterleavedWord A (Fin 2) ι := v₀ ⋈₂ v₁
  Δ₀(u_interleaved, v_interleaved) ≤ e

theorem jointProximityNat_iff_closeToInterleavedCodeword (u : WordStack A κ ι) (e : ℕ) :
    jointProximityNat C (u := u) e ↔ ∃ (v : InterleavedCodeword A κ ι C),
      let u_interleaved : InterleavedWord A κ ι := ⋈|u
      Δ₀(u_interleaved, v.val) ≤ e := by
  unfold jointProximityNat
  let u_interleaved : InterleavedWord A κ ι := ⋈|u
  have h := Code.closeToCode_iff_closeToCodeword_of_minDist
    (C := (interleavedCodeSet C)) (u := u_interleaved) (e := e)
  constructor
  · -- Direction 1: correlatedAgreement u e → ∃ v, Δ₀(⋈|u, v) ≤ e
    intro h_corr_agree
    have res := h.mp h_corr_agree
    rcases res with ⟨v, hv_Mem, hv_dist_le_e⟩
    use ⟨v, hv_Mem⟩
  · -- Direction 2: (∃ v, Δ₀(⋈|u, v) ≤ e) → correlatedAgreement u e
    intro h_exists_v
    rcases h_exists_v with ⟨v, hvClose⟩
    have res := h.mpr (by
      use v.val
      constructor
      · exact v.property
      · exact hvClose
    )
    exact res

/-- The consequent of correlated agreement: Words collectively agree on the same set of coordinates
`S` with the base code `C`.
Variants of this definition should follow the naming conventions of `jointProximity`
if possible, for consistency.
This can generalize further to support the consequent of mutual correlated agreement. -/
def jointAgreement {F κ ι : Type*} [Fintype ι] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ≥0) (W : κ → ι → F) : Prop :=
  ∃ S : Finset ι, S.card ≥ (1 - δ) * (Fintype.card ι) ∧
      ∃ v : κ → ι → F, ∀ i, v i ∈ C ∧ S ⊆ Finset.filter (fun j => v i j = W i j) Finset.univ

open InterleavedCode in
/-- Equivalence between the agreement-based definition `jointAgreement` and
the distance/proximity-based definition `jointProximity` (the latter is represented in
upperbound of interleaved-code distance). -/
@[simp]
theorem jointAgreement_iff_jointProximity
    {F : Type*} {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι] [DecidableEq F]
    (C : Set (ι → F)) (u : WordStack F κ ι) (δ : ℝ≥0) :
    jointAgreement (C := C) (δ := δ) (W := u)  ↔ jointProximity (C := C) (u := u) (δ := δ) := by
  classical
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  constructor
  · -- Forward direction: jointAgreement → jointProximity
    intro h_words
    rcases h_words with ⟨S, hS_card, v, hv⟩
    -- We have: |S| ≥ (1-δ)*|ι| and ∀ i, v i ∈ MC and S ⊆ {j | v i j = u i j}
    -- Need to show: δᵣ(u_interleaved, MC.interleavedCode) ≤ δ
    -- Define interleaved word from u
    let u_interleaved : InterleavedWord F κ ι := ⋈|u
    -- Construct interleaved codeword from v
    let v_interleaved : InterleavedWord F κ ι := interleaveWordStack v
    have hv_interleaved_mem : v_interleaved ∈ interleavedCodeSet C := by
      rw [mem_interleavedCode_iff]
      intro k
      exact (hv k).1
    -- Now show that u_interleaved and v_interleaved agree on S
    -- This gives us the distance bound
    have h_agree_on_S : ∀ j ∈ S, u_interleaved j = getSymbol v_interleaved j := by
      intro j hj
      ext k
      -- u_interleaved j k = u k j, v_interleaved j k = v k j; Need: u k j = v k j
      have h_agree := (hv k).2
      have hj_in_filter : j ∈ Finset.filter (fun j => v k j = u k j) Finset.univ := by
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ j
        · -- v k j = u k j
          have h_subset := Finset.subset_iff.mp h_agree
          have hj_mem : j ∈ S := hj
          let res := h_subset (x := j) hj_mem
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at res
          exact res
      simp only [Finset.mem_filter] at hj_in_filter
      exact hj_in_filter.2.symm
    -- From agreement on S, we get distance bound
    have h_dist : δᵣ(u_interleaved, v_interleaved) ≤ δ := by
      rw [relCloseToWord_iff_exists_agreementCols]
      use S
      rw [relDist_floor_bound_iff_complement_bound]
      constructor
      · exact hS_card
      · intro j
        constructor
        · intro hj_in_S
          have h_agree := h_agree_on_S j hj_in_S
          exact h_agree
        · intro hj_not_in_S
          by_contra hj_in_S
          exact hj_not_in_S (h_agree_on_S j hj_in_S)
    rw [←ENNReal.coe_le_coe] at h_dist
    -- Since v_interleaved ∈ MC.interleavedCode, we have δᵣ(u_interleaved, MC.interleavedCode) ≤ δ
    unfold jointProximity
    have h_min_dist :
        δᵣ(u_interleaved, interleavedCodeSet C) ≤ δᵣ(u_interleaved, v_interleaved)
      := by
      apply relDistFromCode_le_relDist_to_mem (u := u_interleaved) (C := interleavedCodeSet C)
        (v := v_interleaved) (hv := hv_interleaved_mem)
    exact le_trans h_min_dist h_dist
  · -- Backward direction: jointProximity → jointAgreement
    intro h_joint
    unfold jointProximity at h_joint
    let u_interleaved : InterleavedWord F κ ι := ⋈|u
    -- h_joint says: δᵣ(u_interleaved, MC.interleavedCode) ≤ δ
    -- This means there exists v in the interleaved code with δᵣ(u_interleaved, v) ≤ δ
    have h_close := Code.closeToCode_iff_closeToCodeword_of_minDist
      (C := (interleavedCodeSet C)) (u := u_interleaved)
    -- Convert relative distance to natural distance
    -- Key: if δᵣ(u, C) ≤ δ, there exists a codeword v with δᵣ(u, v) ≤ δ
    have h_rel_to_nat : δᵣ(u_interleaved, interleavedCodeSet C) ≤ δ →
        ∃ v ∈ (interleavedCodeSet C), δᵣ(u_interleaved, v) ≤ δ := by
      intro h_rel
      rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at h_rel
      exact h_rel
    have h_exists_v := h_rel_to_nat h_joint
    rcases h_exists_v with ⟨v, hv_mem, hv_dist⟩
    -- Now convert relative distance to agreement set
    -- We need: δᵣ(u_interleaved, v) ≤ δ → ∃ S, |S| ≥ (1-δ)*|ι| and agreement
    -- Convert relative distance δ to natural distance e
    have h_nat_dist : Δ₀(u_interleaved, v) ≤ e := by
      rw [pairRelDist_le_iff_pairDist_le (δ := δ)] at hv_dist
      exact hv_dist
    have h_agree := Code.closeToWord_iff_exists_agreementCols
      (u := u_interleaved) (v := v) (e := e)
    have h_agree_nat := h_agree.mp h_nat_dist
    rcases h_agree_nat with ⟨S, hS_card, h_agree_S⟩
    -- Now extract rows from v to get v : κ → ι → F
    let v_rows : κ → ι → F := fun k => getRow v k
    use S
    constructor
    · -- Prove |S| ≥ (1-δ)*|ι|
      rw [ge_iff_le]
      rw [relDist_floor_bound_iff_complement_bound] at hS_card
      exact hS_card
    · -- Prove agreement
      use v_rows
      intro i
      constructor
      · -- v_rows i ∈ MC
        simp only [interleavedCodeSet, Set.mem_setOf_eq] at hv_mem
        exact hv_mem i
      · -- S ⊆ {j | v_rows i j = u i j}
        simp only [Finset.subset_iff]
        intro j hj_mem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] -- ⊢ v_rows i j = u i j
        have h_agree := h_agree_S (colIdx := j).1 hj_mem
        apply congrArg (fun x => x i) at h_agree
        exact id (Eq.symm h_agree)

/-- The list of `κ`-fold codeword stacks whose interleaved codeword forms are
(less-than)-`δ`-close to `⋈|u`. -/
def relHammingBallInterleavedCode (u : WordStack A κ ι) (δ : ℝ≥0) : Set (CodewordStack A κ ι C) :=
  {v : CodewordStack A κ ι (C := C) | δᵣ(⋈|u, (⋈|v).val) < δ}

/-- `Λᵢ(u, C, δ)` denotes the list of `κ`-fold codeword stacks whose interleaved codeword forms are
(less-than)-`δ`-close to `⋈|u`. -/
notation "Λᵢ(" u "," C "," δ ")" => relHammingBallInterleavedCode C u δ

end JointProximityDefinitions

end Code
end InterleavedCodeDefinitions

namespace InterleavedCode

open ListDecodable Code

/-- **Lemma 2.10 of [ABF26]** (= **[GGR11]**) — interleaved-code
list-size bound.

Let `C` be a code with relative minimum distance `δ_C := δ_min(C) / |ι|`,
and let `δ ∈ [0, δ_C)`. Define
  `η := δ_C - δ`,
  `b := ⌈δ / η⌉`,
  `r := ⌈log₂(δ_C / η)⌉`.
Then for every `m ≥ 1`,

  `|Λ(C^{≡m}, δ)| ≤ (b+r choose r) · |Λ(C, δ)|^r`.

The key feature is that the bound's dependence on the interleaving
factor `m` is hidden inside the constant `(b+r choose r)` — once `δ`
is fixed, the list size of `C^{≡m}` grows as a *polynomial in*
`|Λ(C, δ)|` of degree `r`, **independent of `m`**. Used in ABF26 §3
list-decoding analyses and §6.3.

## Disposition: REDUCED to the external GGR11 list-size recursion.

All *in-tree* infrastructure this statement rests on is proven sorry-free in this
file and in `ListDecodability.lean`: the interleaved-code carrier
(`interleavedCodeSet`, with its `Fintype` instance `interleavedCodeSet_fintype`),
the maximised list size `Lambda` (= `ListDecodability.Lambda`) and its monotonicity
(`Lambda_mono`), and the row-projection characterisation `mem_interleavedCode_iff`
(`V ∈ C^{≡m} ↔ ∀ k, V.transpose k ∈ C`).  In particular,
`closeCodewordsRel_interleaved_transpose_mem_code` proves that any interleaved
codeword in a relative Hamming ball projects, row-wise, to a codeword of `C`.

The residual is the **Gopalan–Guruswami–Raghavendra (GGR11)** combinatorial
list-recovery recursion (RANDOM 2011, "List Decoding Tensor Products and Interleaved
Codes"; ABF26 Lemma 2.10): given that every column of an interleaved word lies in a
list of size ≤ `|Λ(C,δ)|`, a budget/covering argument over the columns selects `r`
"pivot" columns and shows the joint list embeds into the product of the per-pivot
lists, yielding the `(b+r choose r)·|Λ(C,δ)|^r` bound with `b,r` as defined. This
recursion has **no in-tree analogue** — ArkLib presently has neither a list-recovery
primitive nor the column-pruning / iterated-projection lemmas it needs — so the full
port is *not reachable* from current in-tree leaf lemmas; it is a genuine
external-paper obstruction, not a missing local proof.

Note also `F` is only `[Field F]` (not `[Fintype F]`), so over an infinite field
`Lambda C δ` can be `⊤`, in which case the RHS is `⊤` and the bound is trivially true;
but the universally-quantified statement is governed by the finite-list case, which is
exactly the GGR11 recursion above. The `sorry` below is therefore a precisely
characterised external wall.

Residual external lemma: GGR11 interleaved/tensor list-size recursion. -/
theorem lambda_le_ggr11 {ι F : Type} [Fintype ι] [Field F] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ) (m : ℕ) (_hm : 1 ≤ m)
    (_hδ_lb : 0 ≤ δ)
    (_hδ_ub : δ < (Code.minDist C : ℝ) / Fintype.card ι) :
    let η : ℝ := (Code.minDist C : ℝ) / Fintype.card ι - δ
    let b : ℕ := ⌈δ / η⌉₊
    let r : ℕ := ⌈Real.log ((Code.minDist C : ℝ) / Fintype.card ι / η) /
                  Real.log 2⌉₊
    Lambda (interleavedCodeSet (κ := Fin m) C) δ ≤
      ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r := by
  extract_lets η b r
  -- The infinite-list case is genuinely true and proven here; the finite case is the
  -- external GGR11 recursion. We discharge the `Lambda C δ = ⊤` case completely.
  have hn_pos : 0 < Fintype.card ι := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
    · exfalso; rw [h0, Nat.cast_zero, div_zero] at _hδ_ub; linarith
    · exact hpos
  haveI : Nonempty ι := Fintype.card_pos_iff.mp hn_pos
  rcases eq_or_ne (Lambda C δ) (⊤ : ℕ∞) with hT | hT
  · -- `Lambda C δ = ⊤`. We show this forces `δ > 0`, hence `r ≥ 1`, hence the RHS is `⊤`.
    -- `δ ≠ 0`: at `δ = 0` every per-word list is a subsingleton, so `Lambda C 0 ≤ 1 ≠ ⊤`.
    have hδ_pos : 0 < δ := by
      rcases lt_or_eq_of_le _hδ_lb with h | h
      · exact h
      · exfalso
        have hL0 : Lambda C 0 ≤ 1 := by
          refine iSup_le (fun f => ?_)
          have hsub : closeCodewordsRel C f 0 ⊆ {f} := by
            intro c hc
            obtain ⟨_, hball⟩ := hc
            rw [relHammingBall, Set.mem_setOf_eq] at hball
            have hz0 : (Code.relHammingDist f c : ℝ) = 0 :=
              le_antisymm (by convert hball using 3) (by positivity)
            have hz : Code.relHammingDist f c = 0 := by exact_mod_cast hz0
            have hd0 : hammingDist f c = 0 := by
              by_contra hne
              have hpos : (0 : ℚ≥0) < Code.relHammingDist f c := by
                unfold Code.relHammingDist; positivity
              exact absurd hz (ne_of_gt hpos)
            simpa [eq_comm] using (hammingDist_eq_zero.mp hd0)
          have h1 : (closeCodewordsRel C f 0).ncard ≤ 1 := by
            rw [← Set.ncard_singleton f]
            exact Set.ncard_le_ncard hsub (Set.finite_singleton f)
          exact_mod_cast h1
        rw [← h] at hT
        exact absurd (hT ▸ hL0) (by simp [top_le_iff])
    -- `r ≥ 1` since `δ_C / η > 1` (as `0 < η < δ_C`), so `log₂(δ_C/η) > 0`.
    have hη_pos : 0 < η := by simp only [η]; linarith [_hδ_ub]
    have hr_pos : 1 ≤ r := by
      simp only [r]
      rw [Nat.one_le_ceil_iff]
      apply div_pos
      · apply Real.log_pos
        rw [lt_div_iff₀ hη_pos, one_mul]
        simp only [η]; linarith [hδ_pos]
      · exact Real.log_pos (by norm_num)
    -- RHS `= binom * ⊤^r = ⊤`.
    rw [hT]
    have hbinom : ((b + r).choose r : ℕ∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact (Nat.choose_pos (Nat.le_add_left r b)).ne'
    have htop : (⊤ : ℕ∞) ^ r = ⊤ := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      rw [hk, pow_succ]; simp
    rw [htop]
    exact le_top.trans_eq (WithTop.mul_top hbinom).symm
  · -- REDUCED: the finite-list case is the external GGR11 list-recovery recursion
    -- (ABF26 L2.10): all in-tree infra is proven, but no in-tree list-recovery /
    -- column-pruning primitive exists to close it. Genuine external wall.
    sorry

end InterleavedCode
