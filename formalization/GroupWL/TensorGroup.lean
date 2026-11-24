import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Data.Finite.Prod

/-! # Groups represented by alternating tensors

This file constructs the group, rather than assuming its group laws.
The field may have any characteristic for the construction. The identification
of its commutator with the supplied tensor requires characteristic different
from two, as in the manuscript.
-/

namespace GroupWL

universe u v w

/-- A bilinear map with zero diagonal. -/
structure AlternatingBilinearMap (F : Type u) (V : Type v) (Z : Type w)
    [Field F] [AddCommGroup V] [Module F V] [AddCommGroup Z] [Module F Z] where
  toLinearMap : V →ₗ[F] V →ₗ[F] Z
  map_self_eq_zero : ∀ x, toLinearMap x x = 0

namespace AlternatingBilinearMap

variable {F : Type u} {V : Type v} {Z : Type w}
variable [Field F] [AddCommGroup V] [Module F V] [AddCommGroup Z] [Module F Z]

instance : CoeFun (AlternatingBilinearMap F V Z) (fun _ => V → V → Z) :=
  ⟨fun b x y => b.toLinearMap x y⟩

@[simp] theorem self (b : AlternatingBilinearMap F V Z) (x : V) : b x x = 0 :=
  b.map_self_eq_zero x

@[simp] theorem add_left (b : AlternatingBilinearMap F V Z) (x y z : V) :
    b (x + y) z = b x z + b y z := by
  exact LinearMap.congr_fun (b.toLinearMap.map_add x y) z

@[simp] theorem add_right (b : AlternatingBilinearMap F V Z) (x y z : V) :
    b x (y + z) = b x y + b x z := (b.toLinearMap x).map_add y z

@[simp] theorem smul_left (b : AlternatingBilinearMap F V Z) (c : F) (x y : V) :
    b (c • x) y = c • b x y := by
  exact LinearMap.congr_fun (b.toLinearMap.map_smul c x) y

@[simp] theorem smul_right (b : AlternatingBilinearMap F V Z) (c : F) (x y : V) :
    b x (c • y) = c • b x y := (b.toLinearMap x).map_smul c y

@[simp] theorem zero_left (b : AlternatingBilinearMap F V Z) (x : V) : b 0 x = 0 := by
  exact LinearMap.congr_fun b.toLinearMap.map_zero x

@[simp] theorem zero_right (b : AlternatingBilinearMap F V Z) (x : V) : b x 0 = 0 :=
  (b.toLinearMap x).map_zero

@[simp] theorem neg_left (b : AlternatingBilinearMap F V Z) (x y : V) :
    b (-x) y = -b x y := by
  exact LinearMap.congr_fun (b.toLinearMap.map_neg x) y

@[simp] theorem neg_right (b : AlternatingBilinearMap F V Z) (x y : V) :
    b x (-y) = -b x y := (b.toLinearMap x).map_neg y

theorem skew (b : AlternatingBilinearMap F V Z) (x y : V) : b x y = -b y x := by
  have h : b x y + b y x = 0 := by
    calc
      _ = b (x + y) (x + y) := by
        rw [b.add_left, b.add_right, b.add_right, b.self, b.self]
        simp
      _ = 0 := b.self _
  exact eq_neg_of_add_eq_zero_left h

/-- The zero alternating tensor. -/
def zero : AlternatingBilinearMap F V Z where
  toLinearMap := 0
  map_self_eq_zero _ := rfl

@[simp] theorem zero_apply (x y : V) : (zero : AlternatingBilinearMap F V Z) x y = 0 := rfl

end AlternatingBilinearMap

/-- The tensor presentation has elements `(v,z)`; its multiplication is defined below. -/
@[ext]
structure TensorGroup {F : Type u} {V : Type v} {Z : Type w}
    [Field F] [AddCommGroup V] [Module F V] [AddCommGroup Z] [Module F Z]
    (b : AlternatingBilinearMap F V Z) where
  fst : V
  snd : Z

namespace TensorGroup

variable {F : Type u} {V : Type v} {Z : Type w}
variable [Field F] [AddCommGroup V] [Module F V] [AddCommGroup Z] [Module F Z]
variable {b : AlternatingBilinearMap F V Z}

instance : One (TensorGroup b) := ⟨⟨0, 0⟩⟩
instance : Mul (TensorGroup b) :=
  ⟨fun g h => ⟨g.fst + h.fst, g.snd + h.snd + (2 : F)⁻¹ • b g.fst h.fst⟩⟩
instance : Inv (TensorGroup b) := ⟨fun g => ⟨-g.fst, -g.snd⟩⟩

@[simp] theorem one_fst : (1 : TensorGroup b).fst = 0 := rfl
@[simp] theorem one_snd : (1 : TensorGroup b).snd = 0 := rfl
@[simp] theorem mul_fst (g h : TensorGroup b) : (g * h).fst = g.fst + h.fst := rfl
@[simp] theorem mul_snd (g h : TensorGroup b) :
    (g * h).snd = g.snd + h.snd + (2 : F)⁻¹ • b g.fst h.fst := rfl
@[simp] theorem inv_fst (g : TensorGroup b) : g⁻¹.fst = -g.fst := rfl
@[simp] theorem inv_snd (g : TensorGroup b) : g⁻¹.snd = -g.snd := rfl

instance : Group (TensorGroup b) where
  mul_assoc g h k := by
    ext <;> simp only [mul_fst, mul_snd, AlternatingBilinearMap.add_left,
      AlternatingBilinearMap.add_right, smul_add] <;> abel
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by ext <;> simp

/-- The tensor group is carried by precisely the displayed product space. -/
def equivProd : TensorGroup b ≃ V × Z where
  toFun g := (g.fst, g.snd)
  invFun g := ⟨g.1, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite V] [Finite Z] : Finite (TensorGroup b) :=
  Finite.of_equiv (V × Z) equivProd.symm

/-- Pure central vectors always commute, without a nondegeneracy hypothesis. -/
theorem central_mul_comm (z : Z) (g : TensorGroup b) :
    (⟨0, z⟩ : TensorGroup b) * g = g * ⟨0, z⟩ := by
  ext <;> simp [add_comm]

/-- Powers are scalar multiplication of both coordinates. -/
theorem pow_eq (g : TensorGroup b) (n : ℕ) :
    g ^ n = ⟨n • g.fst, n • g.snd⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext
    · simp [succ_nsmul]
    · simp only [mul_snd]
      simp [succ_nsmul]

/-- Over a field of characteristic `p`, every group element has `p`th power one. -/
theorem pow_char_eq_one (p : ℕ) [CharP F p] (g : TensorGroup b) : g ^ p = 1 := by
  rw [pow_eq]
  ext <;> simp only [one_fst, one_snd]
  · rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F p, zero_smul]
  · rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F p, zero_smul]

/-- The group commutator, before simplifying the factor `2/2`. -/
theorem commutator_eq_double (g h : TensorGroup b) :
    g * h * g⁻¹ * h⁻¹ =
      ⟨0, (2 : F)⁻¹ • b g.fst h.fst + (2 : F)⁻¹ • b g.fst h.fst⟩ := by
  ext
  · simp
  · simp only [mul_snd, mul_fst, inv_fst, inv_snd,
      AlternatingBilinearMap.add_left,
      AlternatingBilinearMap.neg_left, AlternatingBilinearMap.neg_right,
      AlternatingBilinearMap.self, smul_add, smul_neg, smul_zero]
    have hs := b.skew h.fst g.fst
    change b.toLinearMap h.fst g.fst = -b.toLinearMap g.fst h.fst at hs
    rw [hs, smul_neg]
    abel

/-- In odd characteristic the supplied tensor is exactly the commutator. -/
theorem commutator_eq [NeZero (2 : F)] (g h : TensorGroup b) :
    g * h * g⁻¹ * h⁻¹ = ⟨0, b g.fst h.fst⟩ := by
  rw [commutator_eq_double]
  congr 1
  rw [← add_smul, ← two_mul, mul_inv_cancel₀ (NeZero.ne (2 : F)), one_smul]

/-- Every commutator is central, so these groups have nilpotency class at most two. -/
theorem commutator_central (g h k : TensorGroup b) :
    (g * h * g⁻¹ * h⁻¹) * k = k * (g * h * g⁻¹ * h⁻¹) := by
  rw [commutator_eq_double]
  exact central_mul_comm _ _

/-- Commuting is exactly vanishing of the tensor. -/
theorem mul_comm_iff [NeZero (2 : F)] (g h : TensorGroup b) :
    g * h = h * g ↔ b g.fst h.fst = 0 := by
  constructor
  · intro hgh
    have hc : g * h * g⁻¹ * h⁻¹ = 1 := by rw [hgh]; simp [mul_assoc]
    rw [commutator_eq] at hc
    exact congrArg TensorGroup.snd hc
  · intro hb
    ext
    · simp [add_comm]
    · simp [hb, b.skew h.fst g.fst, add_comm]

/-- The center is the radical of the supplied tensor, times the output space. -/
theorem central_iff [NeZero (2 : F)] (g : TensorGroup b) :
    (∀ h : TensorGroup b, g * h = h * g) ↔ ∀ v : V, b g.fst v = 0 := by
  constructor
  · intro hg v
    exact (mul_comm_iff g ⟨v, 0⟩).mp (hg ⟨v, 0⟩)
  · intro hg h
    exact (mul_comm_iff g h).mpr (hg h.fst)

/-- A tensor with zero left radical has exactly the prescribed center. -/
theorem central_iff_fst_eq_zero [NeZero (2 : F)]
    (hrad : ∀ v : V, (∀ w : V, b v w = 0) → v = 0) (g : TensorGroup b) :
    (∀ h : TensorGroup b, g * h = h * g) ↔ g.fst = 0 := by
  rw [central_iff]
  exact ⟨hrad g.fst, fun h v => by simp [h]⟩

end TensorGroup

section Evaluation

variable {F : Type u} {X : Type v} {Z : Type w}
variable [Field F] [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]

/-- The evaluation bracket with its additional alternating input twist. -/
def evaluationTwist (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z) :
    AlternatingBilinearMap F (X × Y) Z where
  toLinearMap := LinearMap.mk₂ F
    (fun u v => (v.2 : X →ₗ[F] Z) u.1 - (u.2 : X →ₗ[F] Z) v.1 + ε u.1 v.1)
    (by intros; simp; abel)
    (by intros; simp [smul_sub, smul_add])
    (by intros; simp; abel)
    (by intros; simp [smul_sub, smul_add])
  map_self_eq_zero u := by simp

@[simp] theorem evaluationTwist_apply
    (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z) (u v : X × Y) :
    evaluationTwist Y ε u v =
      (v.2 : X →ₗ[F] Z) u.1 - (u.2 : X →ₗ[F] Z) v.1 + ε u.1 v.1 := rfl

/-- Antisymmetrization of an input-dependent evaluation operator. -/
def shearCoboundary (Y : Submodule F (X →ₗ[F] Z)) (α : X →ₗ[F] Y) :
    AlternatingBilinearMap F X Z where
  toLinearMap := LinearMap.mk₂ F
    (fun x x' => (α x : X →ₗ[F] Z) x' - (α x' : X →ₗ[F] Z) x)
    (by intros; simp; abel)
    (by intros; simp [smul_sub])
    (by intros; simp; abel)
    (by intros; simp [smul_sub])
  map_self_eq_zero x := by simp

@[simp] theorem shearCoboundary_apply (Y : Submodule F (X →ₗ[F] Z)) (α : X →ₗ[F] Y) (x x' : X) :
    shearCoboundary Y α x x' = (α x : X →ₗ[F] Z) x' - (α x' : X →ₗ[F] Z) x := rfl

/-- The input-dependent translation used in the manuscript's shear isomorphism. -/
def evaluationShear (Y : Submodule F (X →ₗ[F] Z)) (α : X →ₗ[F] Y)
    (ε : AlternatingBilinearMap F X Z) :
    TensorGroup (evaluationTwist Y AlternatingBilinearMap.zero) ≃
      TensorGroup (evaluationTwist Y ε) where
  toFun g := ⟨(g.fst.1, g.fst.2 + α g.fst.1), g.snd⟩
  invFun g := ⟨(g.fst.1, g.fst.2 - α g.fst.1), g.snd⟩
  left_inv g := by ext <;> simp
  right_inv g := by ext <;> simp

/-- A shear satisfying the coboundary equation gives an actual group isomorphism. -/
def evaluationShearMulEquiv (Y : Submodule F (X →ₗ[F] Z)) (α : X →ₗ[F] Y)
    (ε : AlternatingBilinearMap F X Z)
    (hα : ∀ x x', shearCoboundary Y α x x' = ε x x') :
    TensorGroup (evaluationTwist Y AlternatingBilinearMap.zero) ≃*
      TensorGroup (evaluationTwist Y ε) where
  toEquiv := evaluationShear Y α ε
  map_mul' g h := by
    ext
    · rfl
    · simp [evaluationShear, TensorGroup.mul_fst]
      abel
    · simp only [evaluationShear, TensorGroup.mul_snd,
        TensorGroup.mul_fst, evaluationTwist_apply, AlternatingBilinearMap.zero_apply]
      have ha := hα g.fst.1 h.fst.1
      change (α g.fst.1 : X →ₗ[F] Z) h.fst.1 -
        (α h.fst.1 : X →ₗ[F] Z) g.fst.1 = ε.toLinearMap g.fst.1 h.fst.1 at ha
      rw [← ha]
      simp only [Submodule.coe_add, LinearMap.add_apply]
      congr 2
      abel

/-- Multiplication is preserved on a pair as soon as the coboundary equation
holds on the two corresponding input vectors. -/
theorem evaluationShear_map_mul_of
    (Y : Submodule F (X →ₗ[F] Z)) (α : X →ₗ[F] Y)
    (ε : AlternatingBilinearMap F X Z)
    (g h : TensorGroup (evaluationTwist Y AlternatingBilinearMap.zero))
    (hα : shearCoboundary Y α g.fst.1 h.fst.1 = ε g.fst.1 h.fst.1) :
    evaluationShear Y α ε (g * h) =
      evaluationShear Y α ε g * evaluationShear Y α ε h := by
  ext
  · rfl
  · simp [evaluationShear, TensorGroup.mul_fst]
    abel
  · simp only [evaluationShear, Equiv.coe_fn_mk, TensorGroup.mul_snd,
      TensorGroup.mul_fst, evaluationTwist_apply, AlternatingBilinearMap.zero_apply]
    change (α g.fst.1 : X →ₗ[F] Z) h.fst.1 -
      (α h.fst.1 : X →ₗ[F] Z) g.fst.1 = ε.toLinearMap g.fst.1 h.fst.1 at hα
    rw [← hα]
    simp only [Submodule.coe_add, LinearMap.add_apply]
    congr 2
    abel

/-- The subgroup over a retained input subspace includes all operator and
central coordinates, as required for arbitrary group queries. -/
def inputSubgroup (Y : Submodule F (X →ₗ[F] Z))
    (ε : AlternatingBilinearMap F X Z) (E : Submodule F X) :
    Subgroup (TensorGroup (evaluationTwist Y ε)) where
  carrier := {g | g.fst.1 ∈ E}
  one_mem' := E.zero_mem
  mul_mem' hg hh := E.add_mem hg hh
  inv_mem' hg := E.neg_mem hg

@[simp] theorem mem_inputSubgroup (Y : Submodule F (X →ₗ[F] Z))
    (ε : AlternatingBilinearMap F X Z) (E : Submodule F X)
    (g : TensorGroup (evaluationTwist Y ε)) :
    g ∈ inputSubgroup Y ε E ↔ g.fst.1 ∈ E := Iff.rfl

/-- A coboundary equation on a retained subspace gives the actual isomorphism
of its full input/operator/output subgroups. -/
def localShearMulEquiv (Y : Submodule F (X →ₗ[F] Z)) (α : X →ₗ[F] Y)
    (ε : AlternatingBilinearMap F X Z) (E : Submodule F X)
    (hα : ∀ x ∈ E, ∀ x' ∈ E, shearCoboundary Y α x x' = ε x x') :
    inputSubgroup Y AlternatingBilinearMap.zero E ≃* inputSubgroup Y ε E where
  toFun g := ⟨evaluationShear Y α ε g.val, g.property⟩
  invFun g := ⟨(evaluationShear Y α ε).symm g.val, g.property⟩
  left_inv g := by
    apply Subtype.ext
    exact (evaluationShear Y α ε).left_inv g.val
  right_inv g := by
    apply Subtype.ext
    exact (evaluationShear Y α ε).right_inv g.val
  map_mul' g h := by
    apply Subtype.ext
    exact evaluationShear_map_mul_of Y α ε g.val h.val
      (hα g.val.fst.1 g.property h.val.fst.1 h.property)

@[simp] theorem localShearMulEquiv_apply_val
    (Y : Submodule F (X →ₗ[F] Z)) (α : X →ₗ[F] Y)
    (ε : AlternatingBilinearMap F X Z) (E : Submodule F X)
    (hα : ∀ x ∈ E, ∀ x' ∈ E, shearCoboundary Y α x x' = ε x x')
    (g : inputSubgroup Y AlternatingBilinearMap.zero E) :
    (localShearMulEquiv Y α ε E hα g).val = evaluationShear Y α ε g.val := rfl

/-- The coboundary equation is also necessary for a shear to be multiplicative. -/
theorem evaluationShear_multiplicative_iff [NeZero (2 : F)]
    (Y : Submodule F (X →ₗ[F] Z)) (α : X →ₗ[F] Y)
    (ε : AlternatingBilinearMap F X Z) :
    (∀ g h, evaluationShear Y α ε (g * h) =
      evaluationShear Y α ε g * evaluationShear Y α ε h) ↔
      ∀ x x', shearCoboundary Y α x x' = ε x x' := by
  constructor
  · intro hm x x'
    let g : TensorGroup (evaluationTwist Y AlternatingBilinearMap.zero) := ⟨(x, 0), 0⟩
    let h : TensorGroup (evaluationTwist Y AlternatingBilinearMap.zero) := ⟨(x', 0), 0⟩
    have hcomm : g * h = h * g := by ext <;> simp [g, h, add_comm]
    have hcomm' : evaluationShear Y α ε g * evaluationShear Y α ε h =
        evaluationShear Y α ε h * evaluationShear Y α ε g := by
      rw [← hm, ← hm, hcomm]
    have hz : (α x' : X →ₗ[F] Z) x - (α x : X →ₗ[F] Z) x' + ε x x' = 0 := by
      simpa [evaluationShear, g, h] using (TensorGroup.mul_comm_iff _ _).mp hcomm'
    change (α x : X →ₗ[F] Z) x' - (α x' : X →ₗ[F] Z) x = ε x x'
    calc
      _ = ((α x : X →ₗ[F] Z) x' - (α x' : X →ₗ[F] Z) x) +
          ((α x' : X →ₗ[F] Z) x - (α x : X →ₗ[F] Z) x' + ε x x') := by rw [hz]; simp
      _ = ε x x' := by abel
  · intro hα
    exact (evaluationShearMulEquiv Y α ε hα).map_mul

/-- If the evaluation operators separate input vectors, every twisted evaluation
bracket has zero radical. This conclusion is independent of the twist. -/
theorem evaluationTwist_radical_eq_zero
    (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z)
    (hsep : ∀ x : X, (∀ y : Y, (y : X →ₗ[F] Z) x = 0) → x = 0)
    (u : X × Y) (hu : ∀ v, evaluationTwist Y ε u v = 0) : u = 0 := by
  have hx : u.1 = 0 := by
    apply hsep
    intro y
    have h := hu (0, y)
    simpa using h
  have hy : u.2 = 0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    have h := hu (x, 0)
    simpa [hx] using h
  exact Prod.ext hx hy

/-- For an evaluation group whose operators separate inputs, the center consists
exactly of the output sector. -/
theorem evaluationGroup_center [NeZero (2 : F)]
    (Y : Submodule F (X →ₗ[F] Z)) (ε : AlternatingBilinearMap F X Z)
    (hsep : ∀ x : X, (∀ y : Y, (y : X →ₗ[F] Z) x = 0) → x = 0)
    (g : TensorGroup (evaluationTwist Y ε)) :
    (∀ h, g * h = h * g) ↔ g.fst = 0 :=
  TensorGroup.central_iff_fst_eq_zero (evaluationTwist_radical_eq_zero Y ε hsep) g

end Evaluation

end GroupWL
