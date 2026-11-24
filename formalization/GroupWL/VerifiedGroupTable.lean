import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Inv
import Mathlib.Tactic

/-! # Direct validation of finite multiplication tables -/
namespace GroupWL.VerifiedGroupTable

universe u
variable {K : Type u} [Fintype K]

/-- The finite checks used for a proposed table. In a finite monoid, left
cancellation supplies both inverse identities. -/
def Valid (one : K) (op : K → K → K) : Prop :=
  (∀ x,op one x=x) ∧ (∀ x,op x one=x) ∧
    (∀ x y z,op (op x y) z=op x (op y z)) ∧
      ∀ x,Function.Injective (op x)

def inverse [DecidableEq K] (one : K) (op : K → K → K) (h : Valid one op) (x : K) : K :=
  Fintype.bijInv ⟨h.2.2.2 x,Finite.surjective_of_injective (h.2.2.2 x)⟩ one

theorem mul_inverse [DecidableEq K] (one : K) (op : K → K → K) (h : Valid one op) (x : K) :
    op x (inverse one op h x)=one :=
  Fintype.rightInverse_bijInv ⟨h.2.2.2 x,Finite.surjective_of_injective (h.2.2.2 x)⟩ one

theorem inverse_mul [DecidableEq K] (one : K) (op : K → K → K) (h : Valid one op) (x : K) :
    op (inverse one op h x) x=one := by
  apply h.2.2.2 x
  rw [← h.2.2.1,mul_inverse one op h x,h.1,h.2.1]

/-- Every accepted table is an actual group of precisely the proposed carrier size. -/
@[reducible] def group [DecidableEq K] (one : K) (op : K → K → K) (h : Valid one op) : Group K where
  mul := op
  one := one
  inv := inverse one op h
  mul_assoc := h.2.2.1
  one_mul := h.1
  mul_one := h.2.1
  inv_mul_cancel := inverse_mul one op h

instance validDecidable [DecidableEq K] (one : K) (op : K → K → K) :
    Decidable (Valid one op) :=
  inferInstanceAs (Decidable ((∀ x,op one x=x) ∧ (∀ x,op x one=x) ∧
    (∀ x y z,op (op x y) z=op x (op y z)) ∧ ∀ x y z,op x y=op x z → y=z))

def check [DecidableEq K] (one : K) (op : K → K → K) : Bool := decide (Valid one op)

@[simp] theorem check_correct [DecidableEq K] (one : K) (op : K → K → K) :
    check one op=true ↔ Valid one op := by simp [check]

/-- A proposed table transported from an actual group passes every check. -/
theorem valid_of_transport {G : Type*} [Group G] (e : K ≃ G)
    (one : K) (op : K → K → K) (h1 : e one=1)
    (hm : ∀ x y,e (op x y)=e x*e y) : Valid one op := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x
    apply e.injective
    simp [hm,h1]
  · intro x
    apply e.injective
    simp [hm,h1]
  · intro x y z
    apply e.injective
    simp only [hm,mul_assoc]
  · intro x y z hyz
    apply e.injective
    apply mul_left_cancel (a := e x)
    simpa only [hm] using congrArg e hyz

end GroupWL.VerifiedGroupTable
