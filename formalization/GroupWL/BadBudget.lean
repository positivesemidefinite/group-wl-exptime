import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.SupIndep
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Tactic

/-! The dimension budget for bad vertices. The scalar-coordinate subspaces at
separate vertices form an independent family; each bad vertex consumes at least
`q-1` dimensions of the retained subspace. -/
namespace GroupWL
namespace BadBudget

open scoped BigOperators
variable {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Module.Finite F V]

/-- Finite sums of independent subspaces have the sum of their dimensions. -/
theorem finrank_biSup_eq_sum (S : I → Submodule F V) (hS : iSupIndep S)
    (s : Finset I) :
    Module.finrank F ↥(⨆ i ∈ s, S i) = ∑ i ∈ s, Module.finrank F (S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hdis : Disjoint (S i) (⨆ j ∈ s, S j) :=
      hS.disjoint_biSup (y := (s : Set I)) hi
    have heq := Submodule.finrank_sup_add_finrank_inf_eq (S i) (⨆ j ∈ s, S j)
    rw [hdis.eq_bot, finrank_bot, add_zero] at heq
    rw [Finset.iSup_insert i s S, Finset.sum_insert hi, ← ih]
    exact heq

/-- Every specified collection of bad vertices obeys the dimension budget. -/
theorem bad_budget (S : I → Submodule F V) (hS : iSupIndep S)
    (E : Submodule F V) (q : ℕ) (bad : Finset I)
    (hbad : ∀ i ∈ bad, q - 1 ≤ Module.finrank F ↥(E ⊓ S i)) :
    (q - 1) * bad.card ≤ Module.finrank F E := by
  classical
  have hind : iSupIndep (fun i => E ⊓ S i) := hS.mono (fun _ => inf_le_right)
  calc
    (q - 1) * bad.card = ∑ _i ∈ bad, (q - 1) := by simp [mul_comm]
    _ ≤ ∑ i ∈ bad, Module.finrank F ↥(E ⊓ S i) := Finset.sum_le_sum hbad
    _ = Module.finrank F ↥(⨆ i ∈ bad, E ⊓ S i) :=
      (finrank_biSup_eq_sum _ hind bad).symm
    _ ≤ Module.finrank F E := Submodule.finrank_mono
      (iSup_le fun _ => iSup_le fun _ => inf_le_left)

/-- A bad vertex is one whose retained intersection has codimension at most one
inside its `q` scalar coordinate directions. -/
noncomputable def badVertices [Fintype I] (S : I → Submodule F V)
    (E : Submodule F V) (q : ℕ) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => q - 1 ≤ Module.finrank F ↥(E ⊓ S i))

@[simp] theorem mem_badVertices [Fintype I] (S : I → Submodule F V)
    (E : Submodule F V) (q : ℕ) (i : I) :
    i ∈ badVertices S E q ↔ q - 1 ≤ Module.finrank F ↥(E ⊓ S i) := by
  classical
  simp [badVertices]

/-- The bad-vertex set is monotone in the retained space. -/
theorem badVertices_mono [Fintype I] (S : I → Submodule F V)
    {E E' : Submodule F V} (h : E ≤ E') (q : ℕ) :
    badVertices S E q ⊆ badVertices S E' q := by
  intro i hi
  rw [mem_badVertices] at hi ⊢
  exact hi.trans (Submodule.finrank_mono (inf_le_inf h le_rfl))

/-- The manuscript's bad-vertex bound. -/
theorem badVertices_budget [Fintype I] (S : I → Submodule F V)
    (hS : iSupIndep S) (E : Submodule F V) (q : ℕ) :
    (q - 1) * (badVertices S E q).card ≤ Module.finrank F E :=
  bad_budget S hS E q _ (fun i hi => (mem_badVertices S E q i).mp hi)

/-- Owners of bad equation or readout vertices.  Equations can be their own
owners; a readout is mapped to any fixed incident equation. -/
noncomputable def ownerSet {J : Type*} [Fintype I]
    (owner : I → J) (S : I → Submodule F V) (E : Submodule F V) (q : ℕ) : Finset J := by
  classical
  exact (badVertices S E q).image owner

/-- Passing from bad vertices to their owners cannot increase the count. -/
theorem ownerSet_card_le {J : Type*} [Fintype I]
    (owner : I → J) (S : I → Submodule F V) (E : Submodule F V) (q : ℕ) :
    (ownerSet owner S E q).card ≤ (badVertices S E q).card := by
  classical
  exact Finset.card_image_le

/-- The owner set is monotone in the retained space. -/
theorem ownerSet_mono {J : Type*} [Fintype I]
    (owner : I → J) (S : I → Submodule F V)
    {E E' : Submodule F V} (h : E ≤ E') (q : ℕ) :
    ownerSet owner S E q ⊆ ownerSet owner S E' q := by
  classical
  exact Finset.image_subset_image (badVertices_mono S h q)

/-- The precise floor bound used to select an exact local affine family. -/
theorem ownerSet_card_le_div {J : Type*} [Fintype I]
    (owner : I → J) (S : I → Submodule F V) (hS : iSupIndep S)
    (E : Submodule F V) (q : ℕ) (hq : 1 < q) :
    (ownerSet owner S E q).card ≤ Module.finrank F E / (q - 1) := by
  apply (Nat.le_div_iff_mul_le (by omega)).2
  calc
    (ownerSet owner S E q).card * (q - 1) ≤
        (badVertices S E q).card * (q - 1) :=
      Nat.mul_le_mul_right _ (ownerSet_card_le owner S E q)
    _ ≤ Module.finrank F E := by simpa [mul_comm] using badVertices_budget S hS E q

/-- At the stated pebble budget, every retained span uses at most `K` owners. -/
theorem ownerSet_card_le_of_budget {J : Type*} [Fintype I]
    (owner : I → J) (S : I → Submodule F V) (hS : iSupIndep S)
    (E : Submodule F V) (q K : ℕ) (hq : 1 < q)
    (hbudget : Module.finrank F E < (q - 1) * (K + 1)) :
    (ownerSet owner S E q).card ≤ K := by
  have hcard := ownerSet_card_le_div owner S hS E q hq
  have hdiv : Module.finrank F E / (q - 1) < K + 1 :=
    (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [mul_comm] using hbudget)
  omega

end BadBudget
end GroupWL
