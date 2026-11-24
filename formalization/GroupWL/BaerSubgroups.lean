import GroupWL.BaerGroup
import Mathlib.GroupTheory.Subgroup.Center

namespace GroupWL.Baer.Data

open scoped commutatorElement

variable {p : ℕ} {G : Type*} [Group G] (D : Baer.Data p G)

/-- Every subgroup is an additive subgroup of the odd-exponent Baer space. -/
def subgroupAddSubgroup (S : Subgroup G) : AddSubgroup (Vector D) where
  carrier := {a | a.val ∈ S}
  zero_mem' := S.one_mem
  add_mem' := by
    intro a b ha hb
    change a.val * b.val * ⁅a.val, b.val⁆ ^ (p / 2) ∈ S
    exact S.mul_mem (S.mul_mem ha hb)
      (S.pow_mem (S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)) _)
  neg_mem' := fun ha => S.inv_mem ha

/-- The prime-field submodule associated to a genuine group subgroup. -/
def subgroupSubmodule (S : Subgroup G) : Submodule (ZMod p) (Vector D) :=
  AddSubgroup.toZModSubmodule p (D.subgroupAddSubgroup S)

@[simp] theorem mem_subgroupSubmodule (S : Subgroup G) (a : Vector D) :
    a ∈ D.subgroupSubmodule S ↔ a.val ∈ S := Iff.rfl

def subgroupCarrierEquiv (S : Subgroup G) : D.subgroupSubmodule S ≃ S where
  toFun a := ⟨a.val.val, a.property⟩
  invFun a := ⟨⟨a.val⟩, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem subgroup_card (S : Subgroup G) : Nat.card (D.subgroupSubmodule S) = Nat.card S :=
  Nat.card_congr (D.subgroupCarrierEquiv S)

def centerSubmodule : Submodule (ZMod p) (Vector D) := D.subgroupSubmodule (Subgroup.center G)

@[simp] theorem mem_centerSubmodule (a : Vector D) :
    a ∈ D.centerSubmodule ↔ ∀ g : G, g * a.val = a.val * g :=
  Subgroup.mem_center_iff

theorem bracket_mem_center [Fact p.Prime] (a b : Vector D) :
    D.bracket a b ∈ D.centerSubmodule := by
  rw [D.mem_centerSubmodule]
  intro g
  exact (D.central a.val b.val g).eq.symm

theorem bracket_center_left [Fact p.Prime] {z : Vector D} (hz : z ∈ D.centerSubmodule)
    (a : Vector D) : D.bracket z a = 0 := by
  apply Vector.ext
  exact commutatorElement_eq_one_iff_mul_comm.mpr ((D.mem_centerSubmodule z).mp hz a.val).symm

theorem bracket_center_right [Fact p.Prime] {z : Vector D} (hz : z ∈ D.centerSubmodule)
    (a : Vector D) : D.bracket a z = 0 := by
  rw [D.bracket.skew, D.bracket_center_left hz, neg_zero]

theorem bracket_zero_iff_commute [Fact p.Prime] (a b : Vector D) :
    D.bracket a b = 0 ↔ Commute a.val b.val := by
  constructor
  · intro h
    exact commutatorElement_eq_one_iff_commute.mp (congrArg Vector.val h)
  · intro h
    exact Vector.ext h.commutator_eq

end GroupWL.Baer.Data
