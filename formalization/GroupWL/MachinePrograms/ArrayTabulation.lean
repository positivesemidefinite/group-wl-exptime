import GroupWL.MachinePrograms.NatArrayProofs
import Mathlib.Data.List.OfFn

/-! Prefix invariants for materializing a finite array one cell at a time. -/
namespace GroupWL.MachinePrograms.ArrayTabulation

def Prefix (f : ℕ → ℕ) (n i : ℕ) (xs : List ℕ) : Prop :=
  xs.length = n ∧ ∀ j < i, xs[j]? = some (f j)

theorem Prefix.zero (f : ℕ → ℕ) (n : ℕ) : Prefix f n 0 (List.replicate n 0) := by
  exact ⟨List.length_replicate, by omega⟩

theorem Prefix.write {f : ℕ → ℕ} {n i : ℕ} {xs : List ℕ}
    (h : Prefix f n i xs) (hi : i<n) : Prefix f n (i+1) (xs.set i (f i)) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro j hj
  by_cases he : j=i
  · subst j
    exact List.getElem?_set_self (by rw [h.1]; exact hi)
  · rw [List.getElem?_set_ne (Ne.symm he)]
    exact h.2 j (by omega)

theorem Prefix.complete {f : ℕ → ℕ} {n : ℕ} {xs : List ℕ}
    (h : Prefix f n n xs) : xs = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<n
  · rw [h.2 i hi]
    simp [hi]
  · have hx : xs[i]? = none := List.getElem?_eq_none (by rw [h.1]; omega)
    simp [hx,hi]

end GroupWL.MachinePrograms.ArrayTabulation
