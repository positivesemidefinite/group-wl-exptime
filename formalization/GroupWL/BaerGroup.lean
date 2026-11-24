import GroupWL.TensorGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic

/-! # The Baer vector space of an arbitrary odd-exponent class-two group

The underlying group need not already be presented by a tensor. Its abelian
addition and prime-field vector-space structure are constructed from its group
operations and the stated exponent and central-commutator identities.
-/

namespace GroupWL.Baer

open scoped commutatorElement

structure Data (p : ℕ) (G : Type*) [Group G] where
  odd : Odd p
  exponent : ∀ g : G, g ^ p = 1
  central : ∀ a b c : G, Commute ⁅a, b⁆ c

namespace Data
variable {p : ℕ} {G : Type*} [Group G] (D : Data p G)

def correction (_D : Data p G) (a b : G) : G := ⁅a, b⁆ ^ (p / 2)
def sum (a b : G) : G := a * b * D.correction a b

include D
theorem correction_central (a b c : G) : Commute (D.correction a b) c :=
  (D.central a b c).pow_left (p / 2)

theorem comm_mul_left (a b c : G) : ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    (D.central b c a).symm.eq]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  exact (D.central b c ⁅a, c⁆).eq

theorem comm_mul_right (a b c : G) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  rw [mul_assoc ⁅a, b⁆ b ⁅a, c⁆, (D.central a c b).symm.eq]
  simp [mul_assoc]

theorem correction_mul_left (a b c : G) :
    D.correction (a * b) c = D.correction a c * D.correction b c := by
  unfold correction
  rw [D.comm_mul_left, (D.central a c ⁅b, c⁆).mul_pow]

theorem correction_mul_right (a b c : G) :
    D.correction a (b * c) = D.correction a b * D.correction a c := by
  unfold correction
  rw [D.comm_mul_right, (D.central a b ⁅a, c⁆).mul_pow]

theorem correction_sum_left (a b c : G) :
    D.correction (D.sum a b) c = D.correction a c * D.correction b c := by
  rw [sum, D.correction_mul_left, D.correction_mul_left]
  have hc : D.correction (D.correction a b) c = 1 := by
    change ⁅D.correction a b, c⁆ ^ (p / 2) = 1
    rw [(D.correction_central a b c).commutator_eq, one_pow]
  rw [hc, mul_one]

theorem correction_sum_right (a b c : G) :
    D.correction a (D.sum b c) = D.correction a b * D.correction a c := by
  rw [sum, D.correction_mul_right, D.correction_mul_right]
  have hc : D.correction a (D.correction b c) = 1 := by
    change ⁅a, D.correction b c⁆ ^ (p / 2) = 1
    rw [(D.correction_central b c a).symm.commutator_eq, one_pow]
  rw [hc, mul_one]

theorem sum_assoc (a b c : G) : D.sum (D.sum a b) c = D.sum a (D.sum b c) := by
  change (a * b * D.correction a b) * c * D.correction (D.sum a b) c =
    a * (b * c * D.correction b c) * D.correction a (D.sum b c)
  rw [D.correction_sum_left, D.correction_sum_right]
  have h1 := (D.correction_central a b c).eq
  have h2 := (D.correction_central b c (D.correction a b * D.correction a c)).eq
  simp only [mul_assoc] at h2 ⊢
  rw [← mul_assoc (D.correction a b) c, h1, mul_assoc]
  rw [h2]

theorem correction_reverse (a b : G) : D.correction b a = (D.correction a b)⁻¹ := by
  unfold correction
  rw [← commutatorElement_inv a b, inv_pow]

theorem half_identity : p / 2 + 1 + p / 2 = p := by
  obtain ⟨k, hk⟩ := D.odd
  omega

theorem correction_swap (a b : G) :
    ⁅a, b⁆ * D.correction a b = (D.correction a b)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  unfold correction
  rw [← pow_succ', ← pow_add]
  rw [D.half_identity, D.exponent]

theorem sum_comm (a b : G) : D.sum a b = D.sum b a := by
  have hab : a * b = (b * a) * ⁅a, b⁆ := by
    rw [(D.central a b (b * a)).symm.eq, commutatorElement_def]
    group
  unfold sum
  rw [hab, mul_assoc, D.correction_swap, D.correction_reverse]
  simp only [inv_inv]

@[simp] theorem sum_one (a : G) : D.sum a 1 = a := by simp [sum, correction]
@[simp] theorem one_sum (a : G) : D.sum 1 a = a := by simp [sum, correction]
@[simp] theorem inv_sum (a : G) : D.sum a⁻¹ a = 1 := by
  simp [sum, correction, ((Commute.refl a).inv_left).commutator_eq]

theorem sum_of_commute {a b : G} (h : Commute a b) : D.sum a b = a * b := by
  simp [sum, correction, h.commutator_eq]

/-- A separate carrier prevents the new addition from being confused with
the original, possibly noncommutative multiplication. -/
@[ext] structure Vector (D : Data p G) where
  val : G

instance : Add (Vector D) := ⟨fun a b => ⟨D.sum a.val b.val⟩⟩
instance : Zero (Vector D) := ⟨⟨1⟩⟩
instance : Neg (Vector D) := ⟨fun a => ⟨a.val⁻¹⟩⟩

instance : AddCommGroup (Vector D) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := Vector.ext (D.sum_assoc a.val b.val c.val)
  zero_add a := Vector.ext (D.one_sum a.val)
  add_zero a := Vector.ext (D.sum_one a.val)
  neg_add_cancel a := Vector.ext (D.inv_sum a.val)
  add_comm a b := Vector.ext (D.sum_comm a.val b.val)

@[simp] theorem Vector.add_val (a b : Vector D) : (a + b).val = D.sum a.val b.val := rfl
@[simp] theorem Vector.zero_val : (0 : Vector D).val = 1 := rfl
@[simp] theorem Vector.neg_val (a : Vector D) : (-a).val = a.val⁻¹ := rfl

@[simp] theorem Vector.nsmul_val (n : ℕ) (a : Vector D) : (n • a).val = a.val ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, Vector.add_val, ih]
      rw [D.sum_of_commute ((Commute.refl a.val).pow_left n)]
      exact (pow_succ a.val n).symm

instance : Module (ZMod p) (Vector D) :=
  AddCommGroup.zmodModule (fun a => Vector.ext (by simpa using D.exponent a.val))

def Vector.equivGroup : Vector D ≃ G where
  toFun := Vector.val
  invFun := Vector.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite G] : Finite (Vector D) := Finite.of_equiv G (Vector.equivGroup D).symm

theorem comm_sum_left (a b c : G) : ⁅D.sum a b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [sum, D.comm_mul_left, D.comm_mul_left,
    (D.correction_central a b c).commutator_eq, mul_one]

theorem comm_sum_right (a b c : G) : ⁅a, D.sum b c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [sum, D.comm_mul_right, D.comm_mul_right,
    (D.correction_central b c a).symm.commutator_eq, mul_one]

def bracketRightAddHom (a : Vector D) : Vector D →+ Vector D where
  toFun b := ⟨⁅a.val, b.val⁆⟩
  map_zero' := Vector.ext (by simp)
  map_add' b c := by
    apply Vector.ext
    change ⁅a.val, D.sum b.val c.val⁆ = D.sum ⁅a.val, b.val⁆ ⁅a.val, c.val⁆
    rw [D.comm_sum_right, D.sum_of_commute (D.central a.val b.val _)]

def bracketAddHom : Vector D →+ (Vector D →ₗ[ZMod p] Vector D) where
  toFun a := (D.bracketRightAddHom a).toZModLinearMap p
  map_zero' := by
    apply LinearMap.ext
    intro b
    apply Vector.ext
    exact commutatorElement_one_left b.val
  map_add' a b := by
    apply LinearMap.ext
    intro c
    apply Vector.ext
    change ⁅D.sum a.val b.val, c.val⁆ = D.sum ⁅a.val, c.val⁆ ⁅b.val, c.val⁆
    rw [D.comm_sum_left, D.sum_of_commute (D.central a.val c.val _)]

/-- The commutator is a prime-field bilinear alternating map on the recovered space. -/
def bracket [Fact p.Prime] : AlternatingBilinearMap (ZMod p) (Vector D) (Vector D) where
  toLinearMap := D.bracketAddHom.toZModLinearMap p
  map_self_eq_zero a := Vector.ext (commutatorElement_self a.val)

@[simp] theorem bracket_val [Fact p.Prime] (a b : Vector D) :
    (D.bracket a b).val = ⁅a.val, b.val⁆ := rfl

theorem half_eq_natCast [Fact p.Prime] : (2 : ZMod p)⁻¹ = ((p / 2 + 1 : ℕ) : ZMod p) := by
  have hn : 2 * (p / 2 + 1) = p + 1 := by have := D.half_identity; omega
  have hf : (2 : ZMod p) * ((p / 2 + 1 : ℕ) : ZMod p) = 1 := by
    have hh := congrArg (fun n : ℕ => (n : ZMod p)) hn
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, ZMod.natCast_self,
      Nat.cast_one, zero_add] using hh
  exact inv_eq_of_mul_eq_one_right hf

theorem half_smul_val [Fact p.Prime] (a : Vector D) :
    ((2 : ZMod p)⁻¹ • a).val = a.val ^ (p / 2 + 1) := by
  rw [D.half_eq_natCast, Nat.cast_smul_eq_nsmul, Vector.nsmul_val]

/-- Original multiplication is exactly the class-two BCH product in the
new vector coordinates. -/
theorem multiplication_recovered [Fact p.Prime] (a b : Vector D) :
    (⟨a.val * b.val⟩ : Vector D) = a + b + (2 : ZMod p)⁻¹ • D.bracket a b := by
  apply Vector.ext
  rw [Vector.add_val, D.half_smul_val, Vector.add_val, D.bracket_val]
  rw [D.sum_of_commute ((D.central a.val b.val _).pow_left (p / 2 + 1)).symm]
  change a.val * b.val = a.val * b.val * ⁅a.val, b.val⁆ ^ (p / 2) *
    ⁅a.val, b.val⁆ ^ (p / 2 + 1)
  rw [mul_assoc, ← pow_add]
  have hn : p / 2 + (p / 2 + 1) = p := by have := D.half_identity; omega
  rw [hn, D.exponent, mul_one]

/-- An actual tensor-coordinate representation gives an isomorphism back to
the original arbitrary group; linearity alone is not assumed sufficient. -/
def coordinatesMulEquiv [Fact p.Prime]
    {V Z : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup Z] [Module (ZMod p) Z]
    (b : AlternatingBilinearMap (ZMod p) V Z)
    (E : (V × Z) ≃ₗ[ZMod p] Vector D)
    (hbracket : ∀ u v : V × Z, E (0, b u.1 v.1) = D.bracket (E u) (E v)) :
    TensorGroup b ≃* G where
  toEquiv := TensorGroup.equivProd.trans (E.toEquiv.trans (Vector.equivGroup D))
  map_mul' g h := by
    change (E (g.fst + h.fst, g.snd + h.snd + (2 : ZMod p)⁻¹ • b g.fst h.fst)).val =
      (E (g.fst, g.snd)).val * (E (h.fst, h.snd)).val
    have heq : (g.fst + h.fst, g.snd + h.snd + (2 : ZMod p)⁻¹ • b g.fst h.fst) =
        (g.fst, g.snd) + (h.fst, h.snd) + (2 : ZMod p)⁻¹ • (0, b g.fst h.fst) := by
      ext <;> simp
    rw [heq, map_add, map_add, map_smul, hbracket (g.fst, g.snd) (h.fst, h.snd)]
    exact congrArg Vector.val (D.multiplication_recovered (E (g.fst, g.snd)) (E (h.fst, h.snd))).symm

end Data
end GroupWL.Baer
