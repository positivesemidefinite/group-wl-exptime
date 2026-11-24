import GroupWL.PGroupCandidateCoverage
import GroupWL.NumericGroupGenerators
import GroupWL.NumericGroupImages
import GroupWL.NumericCandidateCodes
import GroupWL.MachinePrograms.ExtensionTableSemantics
import Mathlib.Algebra.Group.TransferInstance

/-! Executable p-group candidates on numeric carriers. Generator selection
and image expansion use precisely the compiled array algorithms. -/
namespace GroupWL.NumericPGroupCandidates
open Refinement PGroupDecomposition NumericCandidateCodes
variable {p D : ℕ} [Fact p.Prime]

abbrev identity (t : Group (Fin (p^D))) := NumericGroupGenerators.identity t
abbrev operation (t : Group (Fin (p^D))) := NumericGroupGenerators.operation t

def expand (t : Group (Fin (p^D))) (images : Fin D → Fin (p^D)) : Fin (p^D) → Fin (p^D) :=
  NumericGroupImages.expand (operation t) (operation t) (identity t) (identity t)
    (NumericGroupGenerators.generators t) images

theorem expand_images (t : Group (Fin (p^D)))
    (θ : @MulEquiv (Fin (p^D)) (Fin (p^D)) t.toMul t.toMul) :
    expand t (θ ∘ NumericGroupGenerators.generators t)=θ := by
  letI := t
  have hg : Generates ((Equiv.refl (Fin (p^D))) ∘ NumericGroupGenerators.generators t) :=
    NumericGroupGenerators.generators_generate t
  exact NumericGroupImages.expand_hom (Equiv.refl (Fin (p^D))) (Equiv.refl (Fin (p^D)))
    (operation t) (operation t) (fun _ _ => rfl) (fun _ _ => rfl)
    (identity t) (identity t) rfl rfl _ _ hg θ.toMonoidHom (fun _ => rfl)

def extensionEquiv (p D : ℕ) : Fin (p^(D+1)) ≃ Fin p × Fin (p^D) :=
  (finCongr (pow_succ' p D)).trans finProdFinEquiv.symm

@[reducible] def transportedGroup {K L : Type*} (e : L ≃ K) (t : Group K) : Group L := @Equiv.group L K e t

def transportEquiv {K L : Type*} (e : L ≃ K) (t : Group K) :
    @MulEquiv L K (transportedGroup e t).toMul t.toMul := by
  letI := t
  letI := transportedGroup e t
  exact { e with map_mul' := fun x y => e.apply_symm_apply _ }

def extend (t : Group (Fin (p^D))) (images : Fin D → Fin (p^D)) (carry : Fin (p^D)) :
    Option (Group (Fin (p^(D+1)))) := by
  letI := t
  exact (PGroupCandidateCoverage.extend (p:=p) (expand t) images carry).map
    (transportedGroup (extensionEquiv p D))

def zero (p D : ℕ) [Fact p.Prime] : Fin (p^D) := ⟨0,pow_pos (Fact.out : p.Prime).pos D⟩

@[reducible] def baseGroup (p : ℕ) [Fact p.Prime] : Group (Fin (p^0)) := by
  letI : Subsingleton (Fin (p^0)) := by simpa only [pow_zero] using (inferInstance : Subsingleton (Fin 1))
  exact VerifiedGroupTable.group (zero p 0) (fun _ _ => zero p 0)
    ⟨fun _ => Subsingleton.elim _ _,fun _ => Subsingleton.elim _ _,
      fun _ _ _ => rfl,fun _ _ _ _ => Subsingleton.elim _ _⟩

def imagesAt (p D q : ℕ) [Fact p.Prime] : Fin D → Fin (p^D) :=
  finFunctionFinEquiv.symm ⟨q%((p^D)^D),Nat.mod_lt _ (pow_pos (pow_pos (Fact.out : p.Prime).pos D) D)⟩

def carryAt (p D q : ℕ) [Fact p.Prime] : Fin (p^D) :=
  ⟨q/((p^D)^D)%(p^D),Nat.mod_lt _ (pow_pos (Fact.out : p.Prime).pos D)⟩

def decode : (D : ℕ) → ℕ → Option (Group (Fin (p^D)))
  | 0,_ => some (baseGroup p)
  | D+1,q => match decode D (q%radix p D) with
    | none => none
    | some t => extend t (imagesAt p D (q/radix p D)) (carryAt p D (q/radix p D))

theorem extend_covers {G : Type*} [Group G] [Fintype G]
    (t : Group (Fin (p^D))) (H : Subgroup G) [H.Normal] (hi : H.index=p)
    (f : @MulEquiv (Fin (p^D)) H t.toMul inferInstance)
    (x : G) (hx : orderOf (QuotientGroup.mk' H x)=p) :
    ∃images carry u,extend t images carry=some u ∧
      Nonempty (@MulEquiv (Fin (p^(D+1))) G u.toMul inferInstance) := by
  letI := t
  obtain ⟨images,carry,u,hu,⟨e⟩⟩ := PGroupCandidateCoverage.extend_covers
    (NumericGroupGenerators.generators t) (expand t) (expand_images t) H hi f x hx
  refine ⟨images,carry,transportedGroup (extensionEquiv p D) u,?_,?_⟩
  · change Option.map _ (PGroupCandidateCoverage.extend (expand t) images carry)=_
    rw [hu]
    rfl
  · letI : Mul (Fin (p^(D+1))) := (transportedGroup (extensionEquiv p D) u).toMul
    letI : Mul (Fin p × Fin (p^D)) := u.toMul
    exact ⟨(transportEquiv (extensionEquiv p D) u).trans e⟩

theorem decode_covers (D : ℕ) {G : Type*} [Group G] [Fintype G]
    (hc : Nat.card G=p^D) :
    ∃q<radix p D,∃t,decode (p:=p) D q=some t ∧
      Nonempty (@MulEquiv (Fin (p^D)) G t.toMul inferInstance) := by
  induction D generalizing G with
  | zero =>
      haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp (by simpa using hc)).1
      letI : Unique G := ⟨⟨1⟩,fun g => Subsingleton.elim _ _⟩
      letI := baseGroup p
      letI : Mul (Fin (p^0)) := (baseGroup p).toMul
      letI : Unique (Fin (p^0)) := by simpa only [pow_zero] using (inferInstance : Unique (Fin 1))
      exact ⟨0,by simp [radix],baseGroup p,rfl,⟨MulEquiv.ofUnique⟩⟩
  | succ D ih =>
      obtain ⟨H,hH,hi,hn⟩ := exists_normal_tail hc
      letI := hn
      letI : Fintype H := Fintype.ofFinite H
      obtain ⟨q,hq,t,ht,⟨f⟩⟩ := ih hH
      obtain ⟨x,hx⟩ := exists_quotient_generator H hi
      obtain ⟨images,carry,u,hu,he⟩ := extend_covers t H hi f x hx
      let tail : Fin (radix p D) := ⟨q,hq⟩
      refine ⟨pack tail images carry,pack_lt tail images carry,u,?_,he⟩
      rw [decode,pack_mod,ht,pack_div (Fact.out : p.Prime).pos]
      have himages : imagesAt p D ((finFunctionFinEquiv images).val+(p^D)^D*carry.val)=images := by
        unfold imagesAt
        apply finFunctionFinEquiv.injective
        rw [Equiv.apply_symm_apply]
        exact Fin.ext (images_mod images carry)
      have hcarry : carryAt p D ((finFunctionFinEquiv images).val+(p^D)^D*carry.val)=carry := by
        apply Fin.ext
        exact carry_div (Fact.out : p.Prime).pos images carry
      rw [himages,hcarry]
      exact hu

theorem decode_covers_exponential (D : ℕ) {G : Type*} [Group G] [Fintype G]
    (hc : Nat.card G=p^D) :
    ∃q<p^(D^3),∃t,decode (p:=p) D q=some t ∧
      Nonempty (@MulEquiv (Fin (p^D)) G t.toMul inferInstance) := by
  obtain ⟨q,hq,t,ht,he⟩ := decode_covers D hc
  exact ⟨q,hq.trans_le (radix_le (Fact.out : p.Prime).one_le D),t,ht,he⟩

theorem imagesAt_mod (D q : ℕ) : imagesAt p D (q%((p^D)^(D+1)))=imagesAt p D q := by
  apply finFunctionFinEquiv.injective
  simp only [imagesAt,Equiv.apply_symm_apply]
  apply Fin.ext
  simp only [Fin.val_mk,pow_succ,Nat.mod_mul_right_mod]

theorem carryAt_mod (D q : ℕ) : carryAt p D (q%((p^D)^(D+1)))=carryAt p D q := by
  apply Fin.ext
  simp only [carryAt,Fin.val_mk,pow_succ,Nat.mod_mul_right_div_self,Nat.mod_mod]

theorem decode_mod (D q : ℕ) : decode (p:=p) D (q%radix p D)=decode D q := by
  cases D with
  | zero => rfl
  | succ D =>
      simp only [decode,radix,Nat.mod_mul_right_mod,Nat.mod_mul_right_div_self,
        imagesAt_mod,carryAt_mod]

theorem decode_succ (D q : ℕ) : decode (p:=p) (D+1) q=
    match decode D q with
    | none => none
    | some t => extend t (imagesAt p D (q/radix p D)) (carryAt p D (q/radix p D)) := by
  rw [decode,decode_mod]

theorem quotient_next (D q : ℕ) :
    q/radix p (D+1)=(q/radix p D)/((p^D)^(D+1)) := by
  rw [radix,Nat.div_div_eq_div_mul]

end GroupWL.NumericPGroupCandidates
