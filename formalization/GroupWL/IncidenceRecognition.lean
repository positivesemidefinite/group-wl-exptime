import GroupWL.IncidenceNames
import GroupWL.QuotientNaming
import GroupWL.CentralNaming
import GroupWL.OpponentRecognition

/-! Concrete reference anchors and opponent coordinates for the incidence
groups. Every retained opponent anchor is obtained by an actual game move. -/

namespace GroupWL.IncidenceRecognition

open IncidenceTensor IncidenceCoordinates FreeAnchors CoordinateNames CountingLogic PebbleGame Module

variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
  {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
  (A : AffineSystem (ZMod p) I J V) (q : ℕ) (hq : 0 < q)

abbrev X : Type := InputIndex.{0, 0} A q → ZMod p
abbrev Z : Type := OutputIndex.{0, 0} A q → ZMod p
abbrev G (ε : AlternatingBilinearMap (ZMod p) (X A q) (Z A q)) :=
  TensorGroup (evaluationTwist (operators A q hq) ε)

noncomputable def centralInputZeroLinear : Z A q →ₗ[ZMod p] X A q where
  toFun := IncidenceNames.centralInput₀ A q
  map_add' x y := by simp [IncidenceNames.centralInput₀]
  map_smul' r x := by simp [IncidenceNames.centralInput₀]

noncomputable def centralInputOneLinear : Z A q →ₗ[ZMod p] X A q where
  toFun := IncidenceNames.centralInput₁ A q
  map_add' x y := by
    simp only [IncidenceNames.centralInput₁, map_add, Prod.fst_add]
    rw [← map_add]
    congr 1
    simp
  map_smul' r x := by
    change (inputCoordinates A q) (0, ((outputCoordinates A q).symm (r • x)).1) =
      r • (inputCoordinates A q) (0, ((outputCoordinates A q).symm x).1)
    rw [← map_smul]
    congr 1
    simp

theorem centralInputs_exact (z : Z A q) :
    (identityAnchor A q hq : X A q →ₗ[ZMod p] Z A q) (centralInputZeroLinear A q z) +
      (outputAnchor A q hq : X A q →ₗ[ZMod p] Z A q) (centralInputOneLinear A q z) = z :=
  IncidenceNames.central_decomposition A q hq z

variable {d n : ℕ} (basis : Basis (Fin d) (ZMod p) (X A q))
  (ε : AlternatingBilinearMap (ZMod p) (X A q) (Z A q))
  (slot : Fin 9 → Fin n) (hslot : Function.Injective slot)

include hslot in
private theorem slot_ne {i j : Fin 9} (h : i ≠ j) : slot i ≠ slot j :=
  fun he => h (hslot he)

noncomputable def referenceAssignment : Fin n → G A q hq ε :=
  Function.update
    (Function.update
      (Function.update
        (Function.update (fun _ => 1) (slot 0) ⟨(0, identityAnchor A q hq), 0⟩)
        (slot 1) ⟨(0, endomorphismAnchor A q hq (shiftBasis basis)), 0⟩)
      (slot 2) ⟨(basisSeed basis, 0), 0⟩)
    (slot 3) ⟨(0, outputAnchor A q hq), 0⟩

include hslot in
theorem reference_zero :
    referenceAssignment A q hq basis ε slot (slot 0) = ⟨(0, identityAnchor A q hq), 0⟩ := by
  simp [referenceAssignment, slot_ne slot hslot (by decide : (0 : Fin 9) ≠ 3),
    slot_ne slot hslot (by decide : (0 : Fin 9) ≠ 2),
    slot_ne slot hslot (by decide : (0 : Fin 9) ≠ 1)]

include hslot in
theorem reference_one :
    referenceAssignment A q hq basis ε slot (slot 1) =
      ⟨(0, endomorphismAnchor A q hq (shiftBasis basis)), 0⟩ := by
  simp [referenceAssignment, slot_ne slot hslot (by decide : (1 : Fin 9) ≠ 3),
    slot_ne slot hslot (by decide : (1 : Fin 9) ≠ 2)]

include hslot in
theorem reference_seed :
    referenceAssignment A q hq basis ε slot (slot 2) = ⟨(basisSeed basis, 0), 0⟩ := by
  simp [referenceAssignment, slot_ne slot hslot (by decide : (2 : Fin 9) ≠ 3)]

theorem reference_output :
    referenceAssignment A q hq basis ε slot (slot 3) = ⟨(0, outputAnchor A q hq), 0⟩ := by
  simp [referenceAssignment]

variable {H : Type*} [Group H]

noncomputable def quotientContextOfTracks
    {pos : Position (n + 1) (G A q hq ε) H} (hp : Winning pos) (b : Fin n → H)
    (ht : Tracks pos (referenceAssignment A q hq basis ε slot) b) :
    QuotientNamingContext (operators A q hq) ε H n where
  slot := slot
  slot_injective := hslot
  reference := referenceAssignment A q hq basis ε slot
  opponent := b
  position := pos
  winning := hp
  anchors := fun i _ => ht (slot i)
  y₀ := identityAnchor A q hq
  y₁ := endomorphismAnchor A q hq (shiftBasis basis)
  injective_y₀ := identityAnchor_injective A q hq
  shift := shiftBasis basis
  shift_relation := endomorphismAnchor_apply A q hq (shiftBasis basis)
  anchor_zero := by rw [reference_zero A q hq basis ε slot hslot]
  anchor_one := by rw [reference_one A q hq basis ε slot hslot]
  code := coordinateCode basis
  code_exact := by
    intro x
    rw [reference_seed A q hq basis ε slot hslot]
    exact hornerValue_coordinateCode_all basis x

noncomputable def centralContextOfTracks
    {pos : Position (n + 1) (G A q hq ε) H} (hp : Winning pos) (b : Fin n → H)
    (ht : Tracks pos (referenceAssignment A q hq basis ε slot) b) :
    CentralNamingContext (operators A q hq) ε H n where
  toQuotientNamingContext := quotientContextOfTracks A q hq basis ε slot hslot hp b ht
  yb := outputAnchor A q hq
  anchor_b := by
    change (referenceAssignment A q hq basis ε slot (slot 3)).fst = _
    rw [reference_output]
  anchor_b_tracked := ht (slot 3)
  input₀ := centralInputZeroLinear A q
  input₁ := centralInputOneLinear A q
  output_exact := centralInputs_exact A q hq

/-- A winning game supplies all four concrete anchor mates, without any
structural assumption about the opponent. -/
theorem exists_reference_tracks
    {pos : Position (n + 1) (G A q hq ε) H} (hp : Winning pos) :
    ∃ (pos' : Position (n + 1) (G A q hq ε) H) (b : Fin n → H),
      Winning pos' ∧ Tracks pos' (referenceAssignment A q hq basis ε slot) b := by
  obtain ⟨pos', b, hp', ht, _⟩ := winning_complete_variables
    (a := referenceAssignment A q hq basis ε slot) (b := fun _ => (1 : H))
    (S := ∅) hp (by intro i hi; simp at hi)
  exact ⟨pos', b, hp', ht⟩

include hslot basis in
/-- Every finite opponent with a winning position has a full twisted
evaluation presentation over the actual incidence operator space. The four
anchors and all opponent coordinates are constructed within the proof. -/
theorem winning_implies_twisted_presentation_with_basis [Finite H]
    (hodd : Odd p) {pos : Position (n + 1) (G A q hq ε) H} (hp : Winning pos) :
    ∃ η : AlternatingBilinearMap (ZMod p) (X A q) (Z A q),
      Nonempty (H ≃* G A q hq η) := by
  obtain ⟨pos', b, hp', ht⟩ := exists_reference_tracks A q hq basis ε slot hp
  let C := centralContextOfTracks A q hq basis ε slot hslot hp' b ht
  exact C.isomorphic_to_twist hodd

/-- The reconstruction bound is ten pebble pairs (nine formula variables and
the after-pickup reserve), so it applies to all larger winning games. -/
theorem winning_implies_twisted_presentation [Finite H]
    (hodd : Odd p) (hn : 9 ≤ n)
    {pos : Position (n + 1) (G A q hq ε) H} (hp : Winning pos) :
    ∃ η : AlternatingBilinearMap (ZMod p) (X A q) (Z A q),
      Nonempty (H ≃* G A q hq η) := by
  let basis := Module.finBasis (ZMod p) (X A q)
  exact winning_implies_twisted_presentation_with_basis A q hq basis ε
    (Fin.castLE hn) (Fin.castLE_injective hn) hodd hp

include hslot basis in
/-- The retained naming context is exposed together with the reconstructed
isomorphism, so later continuations preserve the same input coordinates. -/
theorem winning_named_reconstruction_with_basis [Finite H]
    (hodd : Odd p) {pos : Position (n + 1) (G A q hq ε) H} (hp : Winning pos) :
    ∃ (C : CentralNamingContext (operators A q hq) ε H n)
      (η : AlternatingBilinearMap (ZMod p) (X A q) (Z A q))
      (f : H ≃* G A q hq η),
      C.slot = slot ∧
      (∀ h : H, (f h).fst.1 = C.toQuotientNamingContext.quotient h) ∧
      (∀ z : Z A q, f (C.center z) = ⟨0, z⟩) := by
  obtain ⟨pos', b, hp', ht⟩ := exists_reference_tracks A q hq basis ε slot hp
  let C := centralContextOfTracks A q hq basis ε slot hslot hp' b ht
  obtain ⟨η, f, hfq, hfc, _⟩ := C.reconstruct (C.toQuotientNamingContext.baerData hodd)
  exact ⟨C, η, f, rfl, hfq, hfc⟩

theorem winning_named_reconstruction [Finite H]
    (hodd : Odd p) (hn : 9 ≤ n)
    {pos : Position (n + 1) (G A q hq ε) H} (hp : Winning pos) :
    ∃ (C : CentralNamingContext (operators A q hq) ε H n)
      (η : AlternatingBilinearMap (ZMod p) (X A q) (Z A q))
      (f : H ≃* G A q hq η),
      C.slot = Fin.castLE hn ∧
      (∀ h : H, (f h).fst.1 = C.toQuotientNamingContext.quotient h) ∧
      (∀ z : Z A q, f (C.center z) = ⟨0, z⟩) := by
  exact winning_named_reconstruction_with_basis A q hq
    (Module.finBasis (ZMod p) (X A q)) ε (Fin.castLE hn) (Fin.castLE_injective hn) hodd hp

end GroupWL.IncidenceRecognition
