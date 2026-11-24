import GroupWL.Affine
import GroupWL.CyclicLifting
import GroupWL.GraphPotentials
import GroupWL.Wrapping

namespace GroupWL.SourceLayout

open scoped BigOperators

variable (F T E : Type*) [Field F] (r : ℕ)

/-- A comparison between scalar images at two real types. Product addresses
are transformed coordinatewise by permutations of the two labels. -/
structure ComparisonData where
  dim : T → ℕ
  source : E → T
  target : E → T
  domain : E → Fin r → Finset Bool
  domain_nonempty : ∀ e i, (domain e i).Nonempty
  permutation : E → Fin r → Equiv.Perm Bool
  sourceForm : ∀ e, (Fin (dim (source e)) → F) →ₗ[F] F
  targetForm : ∀ e, (Fin (dim (target e)) → F) →ₗ[F] F

/-- A wire with `L+1` internal nodes and `L+2` links. -/
inductive Link (E : Type*) (L : ℕ) where
  | first (e : E)
  | middle (e : E) (i : Fin L)
  | last (e : E)
  deriving DecidableEq, Fintype

def Link.comparison {E : Type*} {L : ℕ} : Link E L → E
  | .first e => e
  | .middle e _ => e
  | .last e => e

abbrev Node (T E : Type*) (L : ℕ) := T ⊕ (E × Fin (L + 1))

namespace ComparisonData

variable {F T E r} (C : ComparisonData F T E r) (L : ℕ)

abbrev nodeSpace : Node T E L → Type _
  | .inl t => Fin (C.dim t) → F
  | .inr _ => F

instance nodeSpaceAddCommGroup : (t : Node T E L) → AddCommGroup (C.nodeSpace L t)
  | .inl t => inferInstanceAs (AddCommGroup (Fin (C.dim t) → F))
  | .inr _ => inferInstanceAs (AddCommGroup F)

instance nodeSpaceModule : (t : Node T E L) → Module F (C.nodeSpace L t)
  | .inl t => inferInstanceAs (Module F (Fin (C.dim t) → F))
  | .inr _ => inferInstanceAs (Module F F)

def leftNode : Link E L → Node T E L
  | .first e => .inl (C.source e)
  | .middle e i => .inr (e, i.castSucc)
  | .last e => .inr (e, Fin.last L)

def rightNode : Link E L → Node T E L
  | .first e => .inr (e, 0)
  | .middle e i => .inr (e, i.succ)
  | .last e => .inl (C.target e)

def leftForm : (l : Link E L) → C.nodeSpace L (C.leftNode L l) →ₗ[F] F
  | .first e => C.sourceForm e
  | .middle _ _ => LinearMap.id
  | .last _ => LinearMap.id

def rightForm : (l : Link E L) → C.nodeSpace L (C.rightNode L l) →ₗ[F] F
  | .first _ => LinearMap.id
  | .middle _ _ => LinearMap.id
  | .last e => C.targetForm e

def labelDomain : Node T E L → Fin r → Finset Bool
  | .inl _, _ => Finset.univ
  | .inr (e, _), i => C.domain e i

abbrev Label (t : Node T E L) (i : Fin r) := {a : Bool // a ∈ C.labelDomain L t i}

abbrev DomainLabel (e : E) (i : Fin r) := {a : Bool // a ∈ C.domain e i}

def leftLabel (l : Link E L) (i : Fin r) (a : C.DomainLabel l.comparison i) :
    C.Label L (C.leftNode L l) i := by
  cases l with
  | first e => exact ⟨a.1, Finset.mem_univ _⟩
  | middle e j => exact a
  | last e => exact a

def rightLabel (l : Link E L) (i : Fin r) (a : C.DomainLabel l.comparison i) :
    C.Label L (C.rightNode L l) i := by
  cases l with
  | first e => exact a
  | middle e j => exact a
  | last e => exact ⟨C.permutation e i a.1, Finset.mem_univ _⟩

abbrev Corner := Σ t : Node T E L, Σ i : Fin r, C.Label L t i

abbrev Horizontal := Σ t : Node T E L, Σ i : Fin r,
  C.Label L t i × C.Label L t (finRotate r i)

abbrev Vertical := Σ l : Link E L, Σ i : Fin r, C.DomainLabel l.comparison i

abbrev Square := Σ l : Link E L, Σ i : Fin r,
  C.DomainLabel l.comparison i × C.DomainLabel l.comparison (finRotate r i)

abbrev Readout := C.Horizontal L ⊕ C.Vertical L
abbrev Block := C.Horizontal L ⊕ C.Square L

abbrev readoutSpace : C.Readout L → Type _
  | .inl h => C.nodeSpace L h.1
  | .inr _ => F

instance readoutSpaceAddCommGroup : (q : C.Readout L) → AddCommGroup (C.readoutSpace L q)
  | .inl h => C.nodeSpaceAddCommGroup L h.1
  | .inr _ => inferInstanceAs (AddCommGroup F)

instance readoutSpaceModule : (q : C.Readout L) → Module F (C.readoutSpace L q)
  | .inl h => C.nodeSpaceModule L h.1
  | .inr _ => inferInstanceAs (Module F F)

abbrev Assignment := ∀ q : C.Readout L, C.readoutSpace L q

def projection (q : C.Readout L) : C.Assignment L →ₗ[F] C.readoutSpace L q := LinearMap.proj q

def squareLeft (s : C.Square L) : C.Horizontal L :=
  ⟨C.leftNode L s.1, s.2.1, C.leftLabel L s.1 s.2.1 s.2.2.1,
    C.leftLabel L s.1 (finRotate r s.2.1) s.2.2.2⟩

def squareRight (s : C.Square L) : C.Horizontal L :=
  ⟨C.rightNode L s.1, s.2.1, C.rightLabel L s.1 s.2.1 s.2.2.1,
    C.rightLabel L s.1 (finRotate r s.2.1) s.2.2.2⟩

def squareBefore (s : C.Square L) : C.Vertical L := ⟨s.1, s.2.1, s.2.2.1⟩
def squareAfter (s : C.Square L) : C.Vertical L := ⟨s.1, finRotate r s.2.1, s.2.2.2⟩

/-- The actual signed square equation, as a linear map on all readouts. -/
def blockEquation : C.Block L → C.Assignment L →ₗ[F] F
  | .inl _ => 0
  | .inr s =>
      (C.leftForm L s.1).comp (C.projection L (.inl (C.squareLeft L s))) -
      (C.rightForm L s.1).comp (C.projection L (.inl (C.squareRight L s))) +
      C.projection L (.inr (C.squareAfter L s)) -
      C.projection L (.inr (C.squareBefore L s))

@[simp] theorem blockEquation_site (h : C.Horizontal L) (z : C.Assignment L) :
    C.blockEquation L (.inl h) z = 0 := rfl

@[simp] theorem blockEquation_square (s : C.Square L) (z : C.Assignment L) :
    C.blockEquation L (.inr s) z =
      C.leftForm L s.1 (z (.inl (C.squareLeft L s))) -
      C.rightForm L s.1 (z (.inl (C.squareRight L s))) +
      z (.inr (C.squareAfter L s)) - z (.inr (C.squareBefore L s)) := rfl

def horizontalStart (h : C.Horizontal L) : C.Corner L := ⟨h.1, h.2.1, h.2.2.1⟩
def horizontalEnd (h : C.Horizontal L) : C.Corner L := ⟨h.1, finRotate r h.2.1, h.2.2.2⟩
def verticalStart (v : C.Vertical L) : C.Corner L :=
  ⟨C.leftNode L v.1, v.2.1, C.leftLabel L v.1 v.2.1 v.2.2⟩
def verticalEnd (v : C.Vertical L) : C.Corner L :=
  ⟨C.rightNode L v.1, v.2.1, C.rightLabel L v.1 v.2.1 v.2.2⟩

def readoutStart : C.Readout L → C.Corner L
  | .inl h => C.horizontalStart L h
  | .inr v => C.verticalStart L v

def readoutEnd : C.Readout L → C.Corner L
  | .inl h => C.horizontalEnd L h
  | .inr v => C.verticalEnd L v

/-- Site scopes are retained even though their equation is zero. -/
noncomputable def scope (B : C.Block L) : Finset (C.Readout L) := by
  classical
  cases B with
  | inl h => exact {Sum.inl h}
  | inr s => exact {Sum.inl (C.squareLeft L s), Sum.inl (C.squareRight L s),
      Sum.inr (C.squareAfter L s), Sum.inr (C.squareBefore L s)}

@[simp] theorem scope_site (h : C.Horizontal L) : C.scope L (.inl h) = {.inl h} := rfl

end ComparisonData
end GroupWL.SourceLayout
