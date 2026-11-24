import GroupWL.TensorGroup
import GroupWL.TensorGenerators
import GroupWL.Refinement
import GroupWL.Complexity
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Commutator.Basic

/-!
# The computational target

`FullClaim` specifies the fixed-prime theorem. The proof of the closed
statement over all odd primes is in `GroupWL.ManuscriptCertification`.
The dense input encoding lists tensor coefficients in the standard bases. Identification
uses the underlying group and quantifies over all finite comparison groups.
-/
namespace GroupWL.Statement

open Complexity Refinement
open scoped commutatorElement

variable (p : ℕ) [Fact p.Prime]

/-- Explicit standard bases, and the full alternating tensor in those bases. -/
structure TensorDescription where
  inputDimension : ℕ
  outputDimension : ℕ
  tensor : AlternatingBilinearMap (ZMod p)
    (Fin inputDimension → ZMod p) (Fin outputDimension → ZMod p)

abbrev TensorDescription.Carrier (T : TensorDescription p) := TensorGroup T.tensor

instance (T : TensorDescription p) : Fintype T.Carrier :=
  Fintype.ofEquiv ((Fin T.inputDimension → ZMod p) × (Fin T.outputDimension → ZMod p))
    TensorGroup.equivProd.symm

instance (T : TensorDescription p) : DecidableEq T.Carrier :=
  fun a b => decidable_of_iff (a.fst=b.fst ∧ a.snd=b.snd) (by
    constructor
    · rintro ⟨hf,hs⟩; exact TensorGroup.ext hf hs
    · intro h; cases h; exact ⟨rfl,rfl⟩)

/-- Dense coefficients, including redundant opposite-order and diagonal entries. -/
def TensorDescription.coefficient (T : TensorDescription p)
    (i j : Fin T.inputDimension) (l : Fin T.outputDimension) : ZMod p :=
  T.tensor (Pi.single i 1) (Pi.single j 1) l

def unary (n : ℕ) : BitString := List.replicate n true ++ [false]

/-- The fixed field's entries are delimited unary integers in `[0,p)`;
for fixed `p` this differs from fixed-width binary by a constant factor. -/
def TensorDescription.denseWord (T : TensorDescription p) : BitString :=
  unary T.inputDimension ++ unary T.outputDimension ++
    (List.ofFn (fun i : Fin T.inputDimension =>
      (List.ofFn (fun j : Fin T.inputDimension =>
        (List.ofFn (fun l : Fin T.outputDimension =>
          unary (T.coefficient p i j l).val)).flatten)).flatten)).flatten

def binaryValue : BitString → ℕ :=
  List.foldl (fun n b => 2 * n + if b then 1 else 0) 0

inductive DimensionEncoding where
  | binary | unary
  deriving DecidableEq, Fintype

/-- Canonical positive dimensions. The unary suffix has no terminating delimiter. -/
def DimensionEncoding.Represents : DimensionEncoding → BitString → ℕ → Prop
  | .binary, bits, k => (∃ tail, bits = true :: tail) ∧ binaryValue bits = k ∧ 0 < k
  | .unary, bits, k => bits = List.replicate k true ∧ 0 < k

/-- A malformed description has no witnessing tensor and positive dimension. -/
def identificationLanguage (version : Version) (encoding : DimensionEncoding) : Language :=
  {w | ∃ (T : TensorDescription p) (bits : BitString) (k : ℕ),
    encoding.Represents bits k ∧ w = T.denseWord p ++ bits ∧
      Identifies version k T.Carrier}

def equivalenceLanguage (version : Version) (encoding : DimensionEncoding) : Language :=
  {w | ∃ (T U : TensorDescription p) (bits : BitString) (k : ℕ),
    encoding.Represents bits k ∧ w = T.denseWord p ++ U.denseWord p ++ bits ∧
      GroupEquivalent version k T.Carrier U.Carrier}

/-- Exactly the stated class-two, exponent-p, special-group restrictions. -/
def HardGroup (T : TensorDescription p) : Prop :=
  (∀ g : T.Carrier, g ^ p = 1) ∧
  (∀ g h x : T.Carrier, Commute ⁅g, h⁆ x) ∧
  (∃ g h : T.Carrier, ¬ Commute g h) ∧
  Subgroup.center T.Carrier = commutator T.Carrier

/-- Valid reduction outputs for the restricted identification hardness claim. -/
def hardIdentificationInputs (encoding : DimensionEncoding) : Language :=
  {w | ∃ (T : TensorDescription p) (bits : BitString) (k : ℕ),
    encoding.Represents bits k ∧ w = T.denseWord p ++ bits ∧ HardGroup p T}

/-- The pair reduction must output nonisomorphic groups on every input. -/
def nonisomorphicPairInputs (encoding : DimensionEncoding) : Language :=
  {w | ∃ (T U : TensorDescription p) (bits : BitString) (k : ℕ),
    encoding.Represents bits k ∧ w = T.denseWord p ++ U.denseWord p ++ bits ∧
      ¬ Nonempty (T.Carrier ≃* U.Carrier)}

/-- The requirement on the reduction output is uniform over yes- and no-inputs. -/
def HardWithOutputs (target allowed : Language) : Prop :=
  ∀ source, InEXPTIME source →
    ∃ (M : Machine) (f : BitString → BitString) (c d : ℕ),
      ComputesBy M f (fun n => c * (n + 1) ^ d) ∧
      (∀ w, w ∈ source ↔ f w ∈ target) ∧ (∀ w, f w ∈ allowed)

/-- Fixed-prime target, to be used with the additional hypothesis that p is odd.
Includes both dimension encodings, all three versions,
and the requirements on every hardness-reduction output. -/
def FullClaim : Prop :=
  ∀ version encoding,
    EXPTIMEComplete (identificationLanguage p version encoding) ∧
    EXPTIMEComplete (equivalenceLanguage p version encoding) ∧
    HardWithOutputs (identificationLanguage p version encoding)
      (hardIdentificationInputs p encoding) ∧
    HardWithOutputs (equivalenceLanguage p version encoding)
      (nonisomorphicPairInputs p encoding)

/-- Dimensions remain charged even when every tensor entry vanishes. -/
theorem dimensions_le_encoded_length (T : TensorDescription p) (bits : BitString) :
    T.inputDimension + T.outputDimension ≤ (T.denseWord p ++ bits).length := by
  simp only [TensorDescription.denseWord, unary, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- The actual order of the group represented by the dense tensor. -/
theorem card_carrier (T : TensorDescription p) :
    Fintype.card T.Carrier = p ^ (T.inputDimension + T.outputDimension) := by
  rw [Fintype.card_congr (TensorGroup.equivProd (b := T.tensor))]
  simp [Fintype.card_prod, ZMod.card, pow_add]

/-- Version-II identification is automatic above the input coordinate dimension. -/
theorem identifiesII_at_input_cap [NeZero (2 : ZMod p)] (T : TensorDescription p) :
    IdentifiesII (max 1 (T.inputDimension + T.outputDimension)) T.Carrier := by
  simpa using (TensorGroup.identifiesII_at_dimension_cap (b := T.tensor))

/-- The closed proposition proved by `manuscriptClaim_proved`. -/
def ManuscriptClaim : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩; p ≠ 2 → FullClaim p

end GroupWL.Statement
