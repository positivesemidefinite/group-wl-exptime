import GroupWL.GeneratorImageSearch
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! # Normal index-prime decomposition of every finite prime-power group -/
namespace GroupWL.PGroupDecomposition

open Refinement
universe u
variable {G : Type u} [Group G] [Fintype G] {p D : ℕ} [Fact p.Prime]

/-- Every group of order `p^(D+1)` has a normal subgroup of order `p^D`. -/
theorem exists_normal_tail (hc : Nat.card G=p^(D+1)) :
    ∃ H : Subgroup G,Nat.card H=p^D ∧ H.index=p ∧ H.Normal := by
  obtain ⟨H,hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) p
    (show p^D ∣ Nat.card G by rw [hc,pow_succ]; exact dvd_mul_right _ _)
  have hi : H.index=p := by
    have hh := H.index_mul_card
    rw [hH,hc,pow_succ] at hh
    have hp : 0 < p^D := pow_pos (Fact.out : p.Prime).pos _
    nlinarith
  refine ⟨H,hH,hi,?_⟩
  apply H.normal_of_index_eq_minFac_card
  rw [hi,hc,(Fact.out : p.Prime).pow_minFac (by omega)]

/-- The quotient has a lifted element whose image has exact order `p`. -/
theorem exists_quotient_generator (H : Subgroup G) [H.Normal] (hi : H.index=p) :
    ∃ x : G,orderOf (QuotientGroup.mk' H x)=p := by
  have hc : Nat.card (G ⧸ H)=p := by rw [← H.index_eq_card,hi]
  obtain ⟨q,hq⟩ := exists_prime_orderOf_dvd_card' p (show p ∣ Nat.card (G ⧸ H) by rw [hc])
  obtain ⟨x,rfl⟩ := Quotient.mk''_surjective q
  exact ⟨x,hq⟩

/-- Standard representatives are a power of the lifted quotient generator followed by a tail element. -/
def normalForm (H : Subgroup G) (x : G) (v : Fin p × H) : G := x^v.1.val * v.2

theorem normalForm_injective (H : Subgroup G) [H.Normal] (x : G)
    (hx : orderOf (QuotientGroup.mk' H x)=p) : Function.Injective (normalForm (p := p) H x) := by
  rintro ⟨a,h⟩ ⟨b,j⟩ he
  have hq := congrArg (QuotientGroup.mk' H) he
  have hhq : QuotientGroup.mk' H (h:G)=1 := (QuotientGroup.eq_one_iff (h:G)).mpr h.property
  have hjq : QuotientGroup.mk' H (j:G)=1 := (QuotientGroup.eq_one_iff (j:G)).mpr j.property
  simp only [normalForm,map_mul,map_pow,hhq,hjq,mul_one] at hq
  have hab : a=b := by
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (x := QuotientGroup.mk' H x) (by simpa only [hx] using a.isLt)
      (by simpa only [hx] using b.isLt) hq
  subst b
  have hh : h=j := Subtype.ext (mul_left_cancel he)
  subst j
  rfl

/-- Every element has a unique one-step prime-power normal form. -/
theorem normalForm_bijective (H : Subgroup G) [H.Normal] (hi : H.index=p)
    (x : G) (hx : orderOf (QuotientGroup.mk' H x)=p) :
    Function.Bijective (normalForm (p := p) H x) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨normalForm_injective H x hx,?_⟩
  simp only [Fintype.card_prod,Fintype.card_fin]
  have hh := H.index_mul_card
  rw [hi,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card] at hh
  exact hh

noncomputable def normalFormEquiv (H : Subgroup G) [H.Normal] (hi : H.index=p)
    (x : G) (hx : orderOf (QuotientGroup.mk' H x)=p) : (Fin p × H) ≃ G :=
  Equiv.ofBijective (normalForm H x) (normalForm_bijective H hi x hx)

/-- The carry from exponent addition lies in the tail subgroup. -/
theorem pow_prime_mem (H : Subgroup G) [H.Normal] (x : G)
    (hx : orderOf (QuotientGroup.mk' H x)=p) : x^p ∈ H := by
  apply (QuotientGroup.eq_one_iff (x^p)).mp
  change QuotientGroup.mk' H (x^p)=1
  rw [map_pow,← hx,pow_orderOf_eq_one]

/-- Conjugation used when moving a tail element across a power on its right. -/
def conjugation (H : Subgroup G) [H.Normal] (x : G) : H ≃* H :=
  (MulAut.conjNormal x).symm

@[simp] theorem conjugation_val (H : Subgroup G) [H.Normal] (x : G) (h : H) :
    (conjugation H x h : G)=x⁻¹*h*x := MulAut.conjNormal_symm_apply x h

@[simp] theorem conjugation_iterate_val (H : Subgroup G) [H.Normal] (x : G) (n : ℕ) (h : H) :
    (((conjugation H x : H → H)^[n]) h : G)=(x^n)⁻¹*h*x^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply',conjugation_val,ih]
      simp only [pow_succ,mul_inv_rev,mul_assoc]

/-- A proposed extension is computed from a tail multiplication table,
conjugation map and carry element, without any collection procedure. -/
def extensionMul (p : ℕ) (hp : 0 < p) {K : Type*} [Monoid K]
    (θ : K → K) (c : K) (a b : Fin p × K) : Fin p × K :=
  (⟨(a.1.val+b.1.val)%p,Nat.mod_lt _ hp⟩,
    c^((a.1.val+b.1.val)/p) * θ^[b.1.val] a.2 * b.2)

/-- For data extracted from an actual group, the proposed extension operation
is exactly that group's multiplication. -/
theorem normalForm_extensionMul (H : Subgroup G) [H.Normal] (x : G)
    (hx : orderOf (QuotientGroup.mk' H x)=p) (a b : Fin p × H) :
    normalForm H x (extensionMul p (Fact.out : p.Prime).pos (conjugation H x)
      ⟨x^p,pow_prime_mem H x hx⟩ a b) = normalForm H x a * normalForm H x b := by
  rcases a with ⟨a,h⟩
  rcases b with ⟨b,j⟩
  simp only [normalForm,extensionMul,Subgroup.coe_mul,Subgroup.coe_pow,conjugation_iterate_val]
  rw [← pow_mul,← mul_assoc,← mul_assoc,← pow_add,Nat.mod_add_div]
  rw [pow_add]
  simp only [mul_assoc,mul_inv_cancel_left]

def wordPow {k : ℕ} (w : GroupWord k) : ℕ → GroupWord k
  | 0 => .one
  | n+1 => .mul (wordPow w n) w

@[simp] theorem eval_wordPow {k : ℕ} (a : Fin k → G) (w : GroupWord k) (n : ℕ) :
    (wordPow w n).eval a=(w.eval a)^n := by
  induction n with
  | zero => simp [wordPow,GroupWord.eval]
  | succ n ih => simp [wordPow,GroupWord.eval,ih,pow_succ]

def renameWord {k l : ℕ} (f : Fin k → Fin l) : GroupWord k → GroupWord l
  | .one => .one
  | .gen i => .gen (f i)
  | .mul w w' => .mul (renameWord f w) (renameWord f w')
  | .inv w => .inv (renameWord f w)

@[simp] theorem eval_renameWord {k l : ℕ} (f : Fin k → Fin l) (a : Fin l → G) (w : GroupWord k) :
    (renameWord f w).eval a=w.eval (a ∘ f) := by
  induction w with
  | one => rfl
  | gen i => rfl
  | mul w w' ih ih' => simp [renameWord,GroupWord.eval,ih,ih']
  | inv w ih => simp [renameWord,GroupWord.eval,ih]

/-- Adding the lifted quotient generator to a tail generating tuple generates
the whole group. -/
theorem generates_cons (H : Subgroup G) [H.Normal] (hi : H.index=p)
    (x : G) (hx : orderOf (QuotientGroup.mk' H x)=p)
    {k : ℕ} {a : Fin k → H} (ha : Generates a) :
    Generates (Fin.cons x (fun i => (a i : G))) := by
  intro g
  obtain ⟨⟨n,h⟩,rfl⟩ := (normalForm_bijective H hi x hx).2 g
  obtain ⟨w,hw⟩ := ha h
  refine ⟨.mul (wordPow (.gen 0) n.val) (renameWord Fin.succ w),?_⟩
  simp only [GroupWord.eval,eval_wordPow,Fin.cons_zero,eval_renameWord,normalForm]
  have he : (Fin.cons x (fun i => (a i : G))) ∘ Fin.succ=H.subtype ∘ a := by
    funext i
    rfl
  rw [he,GroupWord.eval_hom,hw]
  rfl

/-- The generator bound holds for every finite group of prime-power order,
not only for tensor groups. -/
theorem exists_generating_tuple (hc : Nat.card G=p^D) :
    ∃ a : Fin D → G,Generates a := by
  induction D generalizing G with
  | zero =>
      haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp (by simpa using hc)).1
      exact ⟨fun i => Fin.elim0 i,fun g => ⟨.one,Subsingleton.elim _ _⟩⟩
  | succ D ih =>
      obtain ⟨H,hH,hi,hn⟩ := exists_normal_tail hc
      letI := hn
      letI : Fintype H := Fintype.ofFinite H
      obtain ⟨a,ha⟩ := ih hH
      obtain ⟨x,hx⟩ := exists_quotient_generator H hi
      exact ⟨Fin.cons x (fun i => (a i:G)),generates_cons H hi x hx ha⟩

/-- Extension multiplication commutes with a change of tail coordinates. -/
theorem map_extensionMul {K L : Type*} [Group K] [Group L]
    (e : K ≃* L) (θ : K → K) (ψ : L → L) (he : ∀ a,e (θ a)=ψ (e a))
    (c : K) (a b : Fin p × K) :
    Prod.map id e (extensionMul p (Fact.out : p.Prime).pos θ c a b)=
      extensionMul p (Fact.out : p.Prime).pos ψ (e c)
        (Prod.map id e a) (Prod.map id e b) := by
  have hi (n : ℕ) (x : K) : e (θ^[n] x)=ψ^[n] (e x) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply',Function.iterate_succ_apply',he,ih]
  apply Prod.ext
  · rfl
  · simp only [extensionMul,Prod.map_apply, map_mul, map_pow,hi]
    rfl

end GroupWL.PGroupDecomposition
