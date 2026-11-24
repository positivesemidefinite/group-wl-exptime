import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-!
# Markers on corner graphs and gauge corrections

The first theorem characterizes markers whose sum on every closed walk
vanishes, including disconnected graphs. The remaining theorems formalize
the correction of corner potentials in the exact-local-extension argument.
They do not assert the manuscript's layout-specific wrapping bounds.
-/

namespace GroupWL
namespace GraphPotentials

variable {V K : Type*} [AddCommGroup K] {G : SimpleGraph V}

/-- Signed marker sum along a walk. -/
def integral (m : V → V → K) : {u v : V} → G.Walk u v → K
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ p => m u v + integral m p

@[simp] theorem integral_nil (m : V → V → K) (u : V) :
    integral m (SimpleGraph.Walk.nil : G.Walk u u) = 0 := rfl

@[simp] theorem integral_cons (m : V → V → K) {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) :
    integral m (.cons h p) = m u v + integral m p := rfl

@[simp] theorem integral_append (m : V → V → K) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    integral m (p.append q) = integral m p + integral m q := by
  induction p with
  | nil => simp [integral]
  | cons h p ih => simp [integral, ih, add_assoc]

theorem integral_reverse (m : V → V → K)
    (hanti : ∀ u v, G.Adj u v → m v u = -m u v)
    {u v : V} (p : G.Walk u v) : integral m p.reverse = -integral m p := by
  induction p with
  | nil => simp [integral]
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.reverse_cons, integral_append]
    simp only [integral_cons, integral_nil, add_zero, ih, hanti u v h]
    abel

@[simp] theorem integral_copy (m : V → V → K) {u v u' v' : V}
    (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    integral m (p.copy hu hv) = integral m p := by
  subst u'
  subst v'
  rfl

/-- Zero closed-walk sums make the integral independent of the chosen walk. -/
theorem integral_path_independent (m : V → V → K)
    (hanti : ∀ u v, G.Adj u v → m v u = -m u v)
    (hzero : ∀ u, ∀ p : G.Walk u u, integral m p = 0)
    {u v : V} (p q : G.Walk u v) : integral m p = integral m q := by
  have h := hzero u (p.append q.reverse)
  rw [integral_append, integral_reverse m hanti] at h
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)

/-- A marker with zero sum on every closed walk is a difference of corner
potentials. A separate root is chosen in each connected component. -/
theorem exists_potential (m : V → V → K)
    (hanti : ∀ u v, G.Adj u v → m v u = -m u v)
    (hzero : ∀ u, ∀ p : G.Walk u u, integral m p = 0) :
    ∃ s : V → K, ∀ u v, G.Adj u v → m u v = s v - s u := by
  classical
  let root (v : V) : V := (G.connectedComponentMk v).out
  have hroot (v : V) : G.Reachable (root v) v := by
    apply SimpleGraph.ConnectedComponent.exact
    exact Quot.out_eq (G.connectedComponentMk v)
  let p (v : V) : G.Walk (root v) v := Classical.choice (hroot v)
  refine ⟨fun v => integral m (p v), ?_⟩
  intro u v huv
  have hroots : root u = root v :=
    congrArg (fun c : G.ConnectedComponent => c.out) (SimpleGraph.ConnectedComponent.sound huv.reachable)
  let q : G.Walk (root u) v := (p v).copy hroots.symm rfl
  have h := integral_path_independent m hanti hzero ((p u).append huv.toWalk) q
  simp only [integral_append, SimpleGraph.Adj.toWalk, integral_cons,
    integral_nil, add_zero, q, integral_copy] at h
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)

/-- Integrating potential differences telescopes along every walk. -/
theorem integral_potential (s : V → K) {u v : V} (p : G.Walk u v) :
    integral (fun u v => s v - s u) p = s v - s u := by
  induction p with
  | nil => simp [integral]
  | cons h p ih => simp only [integral_cons, ih]; abel

/-- The exact criterion for a component to have a marker potential. -/
theorem zero_closed_walks_iff (m : V → V → K)
    (hanti : ∀ u v, G.Adj u v → m v u = -m u v) :
    (∀ u, ∀ p : G.Walk u u, integral m p = 0) ↔
      ∃ s : V → K, ∀ u v, G.Adj u v → m u v = s v - s u := by
  constructor
  · exact exists_potential m hanti
  · rintro ⟨s, hs⟩ u p
    have hi {a b : V} (q : G.Walk a b) : integral m q = s b - s a := by
      induction q with
      | nil => simp [integral]
      | cons h q ih => simp only [integral_cons, hs _ _ h, ih]; abel
    simpa using hi p

/-- The two-edge closed walk already forces reversal to negate the marker. -/
theorem antisymmetric_of_zero_closed_walks (m : V → V → K)
    (hzero : ∀ u, ∀ p : G.Walk u u, integral m p = 0) :
    ∀ u v, G.Adj u v → m v u = -m u v := by
  intro u v huv
  have h := hzero u (.cons huv (.cons huv.symm .nil))
  simp only [integral_cons, integral_nil, add_zero] at h
  exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using h)

/-- No separate antisymmetry premise is necessary when every closed walk is tested. -/
theorem exists_potential_of_zero_closed_walks (m : V → V → K)
    (hzero : ∀ u, ∀ p : G.Walk u u, integral m p = 0) :
    ∃ s : V → K, ∀ u v, G.Adj u v → m u v = s v - s u :=
  exists_potential m (antisymmetric_of_zero_closed_walks m hzero) hzero

section Gauge

variable {R U W Z : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup W] [Module R W]
  [AddCommGroup Z] [Module R Z]

/-- The horizontal correction has the sign used in the manuscript:
`marker = s_w - s_v` and `M'_v = M_v + s_v • (h_new - h_old)`. -/
theorem horizontal_gauge_preserves (Mv Mw hOld hNew : U) (sv sw marker : R)
    (hmarker : marker = sw - sv) :
    (Mv + sv • (hNew - hOld)) - (Mw + sw • (hNew - hOld)) + marker • hNew =
      Mv - Mw + marker • hOld := by
  rw [hmarker]
  simp only [sub_smul, smul_sub]
  abel

/-- Subtracting two type-shift solutions gives homogeneous compatibility. -/
theorem shift_difference_compatible (L : U →ₗ[R] Z) (P : W →ₗ[R] Z)
    (uOld uNew : U) (wOld wNew : W) (b : Z)
    (hold : L uOld - P wOld = b) (hnew : L uNew - P wNew = b) :
    L (uNew - uOld) = P (wNew - wOld) := by
  apply sub_eq_zero.mp
  rw [map_sub, map_sub]
  calc
    L uNew - L uOld - (P wNew - P wOld) =
        (L uNew - P wNew) - (L uOld - P wOld) := by abel
    _ = 0 := by rw [hold, hnew, sub_self]

/-- A vertical edge has equal endpoint marker potentials, and the compatible
type-shift correction consequently leaves its readout unchanged. -/
theorem vertical_gauge_preserves (L : U →ₗ[R] Z) (P : W →ₗ[R] Z)
    (Mv : U) (Mw : W) (gu : U) (gw : W) (sv sw : R)
    (hs : sv = sw) (hg : L gu = P gw) :
    L (Mv + sv • gu) - P (Mw + sw • gw) = L Mv - P Mw := by
  simp only [map_add, map_smul, hs, hg]
  abel

end Gauge

end GraphPotentials
end GroupWL
