import GroupWL.PGroupDecomposition
import GroupWL.VerifiedGroupTable
import GroupWL.FiniteImageSearch

/-! # Bounded recursive candidate descriptions for all finite p-groups -/
namespace GroupWL.PGroupCandidates

open Refinement PGroupDecomposition GeneratorImageSearch

/-- Fixed finite normal-form carriers, independent of any proposed group law. -/
def Carrier (p : ℕ) : ℕ → Type
  | 0 => PUnit
  | D+1 => Fin p × Carrier p D

instance carrierFintype (p : ℕ) : ∀ D,Fintype (Carrier p D)
  | 0 => inferInstanceAs (Fintype PUnit)
  | D+1 => by
      letI := carrierFintype p D
      exact inferInstanceAs (Fintype (Fin p × Carrier p D))

instance carrierDecidableEq (p : ℕ) : ∀ D,DecidableEq (Carrier p D)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | D+1 => by
      letI := carrierDecidableEq p D
      exact inferInstanceAs (DecidableEq (Fin p × Carrier p D))

@[simp] theorem card_carrier (p D : ℕ) : Fintype.card (Carrier p D)=p^D := by
  induction D with
  | zero => rfl
  | succ D ih =>
      change Fintype.card (Fin p × Carrier p D)=_
      simp only [Fintype.card_prod,Fintype.card_fin,ih,pow_succ']

/-- Each extension records only the images of the tail's generators and one carry. -/
def Code (p : ℕ) : ℕ → Type
  | 0 => PUnit
  | D+1 => Code p D × (Fin D → Carrier p D) × Carrier p D

instance codeFintype (p : ℕ) : ∀ D,Fintype (Code p D)
  | 0 => inferInstanceAs (Fintype PUnit)
  | D+1 => by
      letI := codeFintype p D
      exact inferInstanceAs (Fintype (Code p D × (Fin D → Carrier p D) × Carrier p D))

/-- The explicit candidate-description bound has cubic exponent. -/
theorem card_code_le (p D : ℕ) (hp : 1 ≤ p) : Fintype.card (Code p D) ≤ p^(D^3) := by
  induction D with
  | zero => simp [Code]
  | succ D ih =>
      change Fintype.card (Code p D × (Fin D → Carrier p D) × Carrier p D) ≤ _
      calc
        _ = Fintype.card (Code p D) * p^(D*D+D) := by
          simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,card_carrier,
            pow_mul,pow_add,mul_assoc]
        _ ≤ p^(D^3) * p^(D*D+D) := Nat.mul_le_mul_right _ ih
        _ = p^(D^3+(D*D+D)) := (pow_add _ _ _).symm
        _ ≤ p^((D+1)^3) := Nat.pow_le_pow_right hp (by nlinarith)

variable {p D : ℕ} [Fact p.Prime]

/-- A concrete enumeration of the normal-form carrier. -/
def elements (p : ℕ) : (D : ℕ) → List (Carrier p D)
  | 0 => [PUnit.unit]
  | D+1 => (List.finRange p).flatMap (fun i => (elements p D).map (fun x => (i,x)))

theorem mem_elements (p D : ℕ) (x : Carrier p D) : x ∈ elements p D := by
  induction D with
  | zero => cases x; simp [elements]
  | succ D ih =>
      rcases x with ⟨i,x⟩
      simp only [elements,List.mem_flatMap,List.mem_map]
      exact ⟨i,List.mem_finRange i,x,ih x,rfl⟩

/-- Explicit enumeration of tuples, without choosing an ordering of a finset. -/
def tuples {A : Type*} (xs : List A) : (n : ℕ) → List (Fin n → A)
  | 0 => [Fin.elim0]
  | n+1 => xs.flatMap (fun a => (tuples xs n).map (Fin.cons a))

theorem mem_tuples {A : Type*} (xs : List A) (hx : ∀ x,x ∈ xs)
    (n : ℕ) (a : Fin n → A) : a ∈ tuples xs n := by
  induction n with
  | zero =>
      have he : a=Fin.elim0 := by funext i; exact Fin.elim0 i
      simp [tuples,he]
  | succ n ih =>
      simp only [tuples,List.mem_flatMap,List.mem_map]
      exact ⟨a 0,hx _,Fin.tail a,ih _,Fin.cons_self_tail a⟩

private theorem generator_exists (t : Group (Carrier p D)) :
    letI := t
    ∃ a, a ∈ tuples (elements p D) D ∧ FiniteImageSearch.generates a=true := by
  letI := t
  obtain ⟨a,ha⟩ := exists_generating_tuple (G := Carrier p D)
    (by rw [Nat.card_eq_fintype_card,card_carrier])
  exact ⟨a,mem_tuples _ (mem_elements p D) D a,(FiniteImageSearch.generates_correct a).mpr ha⟩

/-- Find the first generating tuple by an executable finite saturation test. -/
def generators (t : Group (Carrier p D)) : Fin D → Carrier p D := by
  letI := t
  exact List.choose (fun a => FiniteImageSearch.generates a=true)
    (tuples (elements p D) D) (generator_exists t)

theorem generators_generate (t : Group (Carrier p D)) :
    letI := t
    Generates (generators t) := by
  letI := t
  exact (FiniteImageSearch.generates_correct _).mp
    (List.choose_property _ _ (generator_exists t))

/-- Expand generator images by the bounded paired-subgroup search. -/
def imageCandidate (t : Group (Carrier p D)) (images : Fin D → Carrier p D) :
    Carrier p D → Carrier p D := by
  letI := t
  exact FiniteImageSearch.expand (elements p D) (generators t) images

theorem imageCandidate_images (t : Group (Carrier p D))
    (e : @MulEquiv (Carrier p D) (Carrier p D) t.toMul t.toMul) :
    imageCandidate t (e ∘ generators t)=e := by
  letI := t
  exact FiniteImageSearch.expand_images _ (mem_elements p D) (generators_generate t) e.toMonoidHom

noncomputable def representatives (t : Group (Carrier p D)) :
    @Representatives (Carrier p D) t D (generators t) := by
  letI := t
  exact Representatives.of_generates (generators_generate t)

/-- Compile a one-step candidate, checking its complete finite multiplication table. -/
def extend (t : Group (Carrier p D))
    (images : Fin D → Carrier p D) (carry : Carrier p D) : Option (Group (Carrier p (D+1))) := by
  letI := t
  let one : Fin p × Carrier p D := (⟨0,(Fact.out : p.Prime).pos⟩,1)
  let op := extensionMul p (Fact.out : p.Prime).pos (imageCandidate t images) carry
  exact if h : VerifiedGroupTable.Valid one op then some (VerifiedGroupTable.group one op h) else none

/-- Every accepted candidate is a group on a carrier of exactly `p^D` elements. -/
def decode : (D : ℕ) → Code p D → Option (Group (Carrier p D))
  | 0,_ => some (inferInstanceAs (Group PUnit))
  | D+1,(c,images,carry) =>
      match decode D c with
      | none => none
      | some t => extend t images carry

/-- Acceptance carries all group axioms, rather than an unchecked operation table. -/
theorem accepted_order (D : ℕ) (c : Code p D) (t : Group (Carrier p D))
    (_h : decode D c=some t) : Nat.card (Carrier p D)=p^D := by
  rw [Nat.card_eq_fintype_card,card_carrier]


/-- Every one-step extension of an actual finite p-group appears among the
proposed generator-image tuples and passes the complete table check. -/
theorem extend_covers {G : Type*} [Group G] [Fintype G]
    (t : Group (Carrier p D)) (H : Subgroup G) [H.Normal]
    (hi : H.index=p) (f : @MulEquiv (Carrier p D) H t.toMul inferInstance)
    (x : G) (hx : orderOf (QuotientGroup.mk' H x)=p) :
    ∃ images carry u, extend t images carry=some u ∧
      Nonempty (@MulEquiv (Carrier p (D+1)) G u.toMul inferInstance) := by
  letI := t
  let θ : Carrier p D ≃* Carrier p D := (f.trans (conjugation H x)).trans f.symm
  let images := θ ∘ generators t
  let carry := f.symm ⟨x^p,pow_prime_mem H x hx⟩
  let e : Carrier p (D+1) ≃ G :=
    (Equiv.prodCongr (Equiv.refl (Fin p)) f.toEquiv).trans (normalFormEquiv H hi x hx)
  let one : Carrier p (D+1) := (⟨0,(Fact.out : p.Prime).pos⟩,1)
  let op := extensionMul p (Fact.out : p.Prime).pos
    (imageCandidate t images) carry
  have hc : imageCandidate t images=θ := imageCandidate_images t θ
  have he1 : e one=1 := by
    change x^0*(f 1:G)=1
    simp
  have hem (a b : Carrier p (D+1)) : e (op a b)=e a*e b := by
    have hm := map_extensionMul f (θ : Carrier p D → Carrier p D) (conjugation H x)
      (fun z => by simp [θ]) carry a b
    change normalForm H x (Prod.map id f (op a b))=_
    unfold op
    rw [hc,hm]
    have hcarry : f carry=⟨x^p,pow_prime_mem H x hx⟩ := f.apply_symm_apply _
    rw [hcarry,normalForm_extensionMul H x hx]
    rfl
  have hv : VerifiedGroupTable.Valid one op := VerifiedGroupTable.valid_of_transport e one op he1 hem
  let u := VerifiedGroupTable.group one op hv
  refine ⟨images,carry,u,?_,?_⟩
  · change (if h : VerifiedGroupTable.Valid one op then some (VerifiedGroupTable.group one op h) else none)=_
    rw [dif_pos hv]
  · exact ⟨{ e with map_mul' := hem }⟩

/-- Every finite group of order p^D is isomorphic to a decoded candidate.
This is coverage among all finite groups, with no presentation hypothesis. -/
theorem decode_covers (D : ℕ) {G : Type*} [Group G] [Fintype G]
    (hc : Nat.card G=p^D) :
    ∃ c t,decode (p := p) D c=some t ∧
      Nonempty (@MulEquiv (Carrier p D) G t.toMul inferInstance) := by
  induction D generalizing G with
  | zero =>
      haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp (by simpa using hc)).1
      letI : Unique G := ⟨⟨1⟩,fun g => Subsingleton.elim _ _⟩
      letI : Unique (Carrier p 0) := inferInstanceAs (Unique PUnit)
      letI : Group (Carrier p 0) := inferInstanceAs (Group PUnit)
      exact ⟨PUnit.unit,inferInstanceAs (Group PUnit),rfl,⟨MulEquiv.ofUnique⟩⟩
  | succ D ih =>
      obtain ⟨H,hH,hi,hn⟩ := exists_normal_tail hc
      letI := hn
      letI : Fintype H := Fintype.ofFinite H
      obtain ⟨c,t,ht,⟨f⟩⟩ := ih hH
      obtain ⟨x,hx⟩ := exists_quotient_generator H hi
      obtain ⟨images,carry,u,hu,he⟩ := extend_covers t H hi f x hx
      refine ⟨(c,images,carry),u,?_,he⟩
      simp only [decode,ht,hu]

end GroupWL.PGroupCandidates
