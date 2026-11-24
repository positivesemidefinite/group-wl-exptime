import GroupWL.SourceLayout.PotentialAssignments

namespace GroupWL.SourceLayout.ComparisonData

open scoped BigOperators

variable {F T E : Type*} [Field F] {r L : ℕ}
variable (C : ComparisonData F T E r)

abbrev NodeAddress (t : Node T E L) := ∀ i : Fin r, C.Label L t i
abbrev DomainAddress (e : E) := ∀ i : Fin r, C.DomainLabel e i

def ringReadout (t : Node T E L) (a : C.NodeAddress (L := L) t) (i : Fin r) : C.Horizontal L :=
  ⟨t, i, a i, a (finRotate r i)⟩

def ringValue (z : C.Assignment L) (t : Node T E L) (a : C.NodeAddress (L := L) t) :
    C.nodeSpace L t := ∑ i, z (.inl (C.ringReadout t a i))

def squareAt (l : Link E L) (a : C.DomainAddress l.comparison) (i : Fin r) : C.Square L :=
  ⟨l, i, a i, a (finRotate r i)⟩

def leftAddress (l : Link E L) (a : C.DomainAddress l.comparison) :
    C.NodeAddress (C.leftNode L l) := fun i => C.leftLabel L l i (a i)

def rightAddress (l : Link E L) (a : C.DomainAddress l.comparison) :
    C.NodeAddress (C.rightNode L l) := fun i => C.rightLabel L l i (a i)

/-- The telescoping row shift on a link. -/
def linkDelta (beta : C.Block L → F) (l : Link E L) (a : C.DomainAddress l.comparison) : F :=
  ∑ i, beta (.inr (C.squareAt l a i))

private theorem sum_squares_identity {U W : Type*}
    [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]
    (f : U →ₗ[F] F) (g : W →ₗ[F] F) (x : Fin r → U) (y : Fin r → W) (v : Fin r → F) :
    (∑ i, (f (x i) - g (y i) + v (finRotate r i) - v i)) =
      f (∑ i, x i) - g (∑ i, y i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Equiv.sum_comp (finRotate r) v, ← map_sum f, ← map_sum g]
  abel

theorem ring_equation_of_squares (z : C.Assignment L) (beta : C.Block L → F)
    (l : Link E L) (a : C.DomainAddress l.comparison)
    (h : ∀ i, C.blockEquation L (.inr (C.squareAt l a i)) z = beta (.inr (C.squareAt l a i))) :
    C.leftForm L l (C.ringValue z (C.leftNode L l) (C.leftAddress l a)) -
      C.rightForm L l (C.ringValue z (C.rightNode L l) (C.rightAddress l a)) =
        C.linkDelta beta l a := by
  calc
    _ = ∑ i, C.blockEquation L (.inr (C.squareAt l a i)) z :=
      (sum_squares_identity (C.leftForm L l) (C.rightForm L l)
        (fun i => z (.inl (C.ringReadout (C.leftNode L l) (C.leftAddress l a) i)))
        (fun i => z (.inl (C.ringReadout (C.rightNode L l) (C.rightAddress l a) i)))
        (fun i => z (.inr ⟨l, i, a i⟩))).symm
    _ = C.linkDelta beta l a := Finset.sum_congr rfl (fun i _ => h i)

variable [Fintype T] [Fintype E]

theorem ring_equation_of_solution (z : C.Assignment L) (beta : C.Block L → F)
    (hz : (C.affineSystem (L := L)).linearMap z = beta)
    (l : Link E L) (a : C.DomainAddress l.comparison) :
    C.leftForm L l (C.ringValue z (C.leftNode L l) (C.leftAddress l a)) -
      C.rightForm L l (C.ringValue z (C.rightNode L l) (C.rightAddress l a)) =
        C.linkDelta beta l a :=
  C.ring_equation_of_squares z beta l a (fun _i => (C.solves_iff beta z).mp hz _)

end GroupWL.SourceLayout.ComparisonData
