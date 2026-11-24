import GroupWL.SourceLayout.System
import GroupWL.SourceLayout.ActiveLinks

namespace GroupWL.SourceLayout.ComparisonData

variable {F T E : Type*} [Field F] {r L : ℕ}
variable (C : ComparisonData F T E r)

def rowMarker (i : Fin r) : F := if i.val + 1 = r then 1 else 0

def sourceShift (b : E → F) : C.Block L → F
  | .inl _ => 0
  | .inr s => rowMarker s.2.1 * linkConstant b s.1

abbrev CornerPotential := ∀ c : C.Corner L, C.nodeSpace L c.1
abbrev TypeShift := ∀ t : Node T E L, C.nodeSpace L t

/-- The actual site/square assignment associated with corner potentials and
type shifts. This definition includes both signs of the odd-field formulas. -/
def potentialAssignment (h : C.TypeShift (L := L)) (M : C.CornerPotential (L := L)) : C.Assignment L
  | .inl q => M ⟨q.1, q.2.1, q.2.2.1⟩ - M ⟨q.1, finRotate r q.2.1, q.2.2.2⟩ +
      (rowMarker q.2.1 : F) • h q.1
  | .inr v => C.leftForm L v.1 (M (C.verticalStart L v)) -
      C.rightForm L v.1 (M (C.verticalEnd L v))

private theorem square_potential_identity {U W : Type*}
    [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]
    (f : U →ₗ[F] F) (g : W →ₗ[F] F) (a b h : U) (c d j : W) (δ : F) :
    f (a - b + δ • h) - g (c - d + δ • j) +
      (f b - g d) - (f a - g c) = δ * (f h - g j) := by
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  ring

theorem potentialAssignment_square (h : C.TypeShift (L := L))
    (M : C.CornerPotential (L := L)) (s : C.Square L) :
    C.blockEquation L (.inr s) (C.potentialAssignment h M) =
      rowMarker s.2.1 * (C.leftForm L s.1 (h (C.leftNode L s.1)) -
        C.rightForm L s.1 (h (C.rightNode L s.1))) := by
  exact square_potential_identity (C.leftForm L s.1) (C.rightForm L s.1)
    (M (C.verticalStart L (C.squareBefore L s)))
    (M (C.verticalStart L (C.squareAfter L s))) (h (C.leftNode L s.1))
    (M (C.verticalEnd L (C.squareBefore L s)))
    (M (C.verticalEnd L (C.squareAfter L s))) (h (C.rightNode L s.1)) (rowMarker s.2.1)

variable [Fintype T] [Fintype E]

theorem potentialAssignment_solvesOn (S : Finset (C.Block L)) (b : E → F)
    (h : C.TypeShift (L := L)) (M : C.CornerPotential (L := L))
    (hh : ∀ l ∈ C.activeLinks S,
      C.leftForm L l (h (C.leftNode L l)) - C.rightForm L l (h (C.rightNode L l)) =
        linkConstant b l) :
    (C.affineSystem (L := L)).SolvesOn (C.sourceShift b) S (C.potentialAssignment h M) := by
  intro B hB
  rw [C.affineSystem_equation]
  cases B with
  | inl q => rfl
  | inr s =>
    rw [C.potentialAssignment_square, hh s.1 (C.square_link_mem_active hB)]
    rfl

/-- Every block set smaller than a private wire has an actual affine solution.
The stronger exact-projection property requires the image-set constraints. -/
theorem exists_local_solution (S : Finset (C.Block L)) (hS : S.card < L + 2) (b : E → F) :
    ∃ z : C.Assignment L, (C.affineSystem (L := L)).SolvesOn (C.sourceShift b) S z := by
  let cut := C.cutsFor S hS
  let h := C.completedShift cut (fun _ => 0) b
  refine ⟨C.potentialAssignment h (fun _ => 0), C.potentialAssignment_solvesOn S b h _ ?_⟩
  intro l hl
  exact C.completedShift_equation cut _ b l (C.active_not_cut S hS l hl)

end GroupWL.SourceLayout.ComparisonData
