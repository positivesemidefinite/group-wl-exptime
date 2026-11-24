import GroupWL.CircuitReductionWords
import GroupWL.MachineCircuit

/-! Semantic correctness of the explicit per-machine reduction outputs.
This file does not assert their operational construction-time bound. -/
namespace GroupWL.MachineReduction

open Complexity AddressedCircuit Statement Refinement CircuitGroupReduction

def circuitIndex (c e n : ℕ) : ℕ :=
  MachineCircuit.addressBits c e n + MachineCircuit.addressBits c e n - 3

theorem circuitIndex_add_three (c e n : ℕ) :
    circuitIndex c e n + 3 =
      MachineCircuit.addressBits c e n + MachineCircuit.addressBits c e n := by
  unfold circuitIndex MachineCircuit.addressBits
  omega

def castCircuit {T : Type*} {r s : ℕ} (h : r=s) (C : Circuit T r) : Circuit T s := h ▸ C

@[simp] theorem castCircuit_accepts {T : Type*} {r s : ℕ} (h : r=s) (C : Circuit T r) :
    (castCircuit h C).Accepts ↔ C.Accepts := by subst s; rfl

def circuit (M : Machine) (c e : ℕ) (w : BitString) :
    Circuit (CellularTableau.Gate (MachineCellular.Cell M)) (circuitIndex c e w.length+3) :=
  castCircuit (circuitIndex_add_three c e w.length).symm
    (MachineCircuit.compile M w (MachineCircuit.addressBits c e w.length))

theorem circuit_accepts_iff (M : Machine) (L : Language) (c e : ℕ)
    (hM : DecidesBy M L (fun n => 2^(c*(n+1)^e))) (w : BitString) :
    (circuit M c e w).Accepts ↔ w ∈ L := by
  rw [circuit,castCircuit_accepts]
  exact MachineCircuit.compile_decider M L c e hM w

variable (p : ℕ) [Fact p.Prime] [NeZero (2 : ZMod p)]

noncomputable def identificationMap (M : Machine) (c e : ℕ)
    (version : Version) (encoding : DimensionEncoding) (w : BitString) : BitString :=
  identificationOutput p (circuit M c e w) version encoding

/-- Equivalence uses the same construction on the complemented machine. -/
noncomputable def equivalenceMap (M : Machine) (c e : ℕ)
    (version : Version) (encoding : DimensionEncoding) (w : BitString) : BitString :=
  equivalenceOutput p (circuit (complement M) c e w) version encoding

theorem identificationMap_correct (hodd : Odd p) (M : Machine) (L : Language) (c e : ℕ)
    (hM : DecidesBy M L (fun n => 2^(c*(n+1)^e)))
    (version : Version) (encoding : DimensionEncoding) (w : BitString) :
    w ∈ L ↔ identificationMap p M c e version encoding w ∈
      identificationLanguage p version encoding := by
  exact ((identificationOutput_mem_iff p (circuit M c e w) hodd version encoding).trans
    (circuit_accepts_iff M L c e hM w)).symm

theorem equivalenceMap_correct (hodd : Odd p) (M : Machine) (L : Language) (c e : ℕ)
    (hM : DecidesBy M L (fun n => 2^(c*(n+1)^e)))
    (version : Version) (encoding : DimensionEncoding) (w : BitString) :
    w ∈ L ↔ equivalenceMap p M c e version encoding w ∈
      equivalenceLanguage p version encoding := by
  change w ∈ L ↔ equivalenceOutput p (circuit (complement M) c e w) version encoding ∈ _
  rw [equivalenceOutput_mem_iff p _ hodd version encoding,
    circuit_accepts_iff (complement M) Lᶜ c e hM.complement w]
  simp

theorem identificationMap_hard (M : Machine) (c e : ℕ)
    (version : Version) (encoding : DimensionEncoding) (w : BitString) :
    identificationMap p M c e version encoding w ∈ hardIdentificationInputs p encoding :=
  identificationOutput_hard p (circuit M c e w) version encoding

theorem equivalenceMap_nonisomorphic (M : Machine) (c e : ℕ)
    (version : Version) (encoding : DimensionEncoding) (w : BitString) :
    equivalenceMap p M c e version encoding w ∈ nonisomorphicPairInputs p encoding :=
  equivalenceOutput_nonisomorphic p (circuit (complement M) c e w) version encoding

end GroupWL.MachineReduction
