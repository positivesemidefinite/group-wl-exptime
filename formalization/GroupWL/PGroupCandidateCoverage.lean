import GroupWL.PGroupCandidates

/-! Extension coverage is independent of the ordering used to choose a
generating tuple and of the implementation used to expand its images. -/
namespace GroupWL.PGroupCandidateCoverage
open Refinement PGroupDecomposition

variable {p k : ℕ} [Fact p.Prime]
variable {K : Type*} [Fintype K] [DecidableEq K] [Group K]

def extend (expand : (Fin k → K) → K → K)
    (images : Fin k → K) (carry : K) : Option (Group (Fin p × K)) := by
  let identity : Fin p × K := (⟨0,(Fact.out : p.Prime).pos⟩,1)
  let op := extensionMul p (Fact.out : p.Prime).pos (expand images) carry
  exact if h : VerifiedGroupTable.Valid identity op then
    some (VerifiedGroupTable.group identity op h) else none

def validatedEquiv {L G : Type*} [Fintype L] [DecidableEq L] [Group G]
    (e : L ≃ G) (identity : L) (op : L → L → L) (hv : VerifiedGroupTable.Valid identity op)
    (hm : ∀x y,e (op x y)=e x*e y) :
    @MulEquiv L G (VerifiedGroupTable.group identity op hv).toMul inferInstance := by
  letI := VerifiedGroupTable.group identity op hv
  exact { e with map_mul' := hm }

theorem extend_covers {G : Type*} [Group G] [Fintype G]
    (a : Fin k → K) (expand : (Fin k → K) → K → K)
    (recovery : ∀ θ : MulEquiv K K,expand (θ ∘ a)=θ)
    (H : Subgroup G) [H.Normal] (hi : H.index=p)
    (f : MulEquiv K H)
    (x : G) (hx : orderOf (QuotientGroup.mk' H x)=p) :
    ∃ images carry u,extend (p:=p) expand images carry=some u ∧
      Nonempty (@MulEquiv (Fin p × K) G u.toMul inferInstance) := by
  let θ : K ≃* K := (f.trans (conjugation H x)).trans f.symm
  let images := θ ∘ a
  let carry := f.symm ⟨x^p,pow_prime_mem H x hx⟩
  let e : (Fin p × K) ≃ G :=
    (Equiv.prodCongr (Equiv.refl (Fin p)) f.toEquiv).trans (normalFormEquiv H hi x hx)
  let identity : Fin p × K := (⟨0,(Fact.out : p.Prime).pos⟩,1)
  let op := extensionMul p (Fact.out : p.Prime).pos (expand images) carry
  have hc : expand images=θ := recovery θ
  have he1 : e identity=1 := by
    change x^0*(f 1:G)=1
    simp
  have hem (u v : Fin p × K) : e (op u v)=e u*e v := by
    have hm := map_extensionMul f (θ : K → K) (conjugation H x)
      (fun z => by simp [θ]) carry u v
    change normalForm H x (Prod.map id f (op u v))=_
    unfold op
    rw [hc,hm]
    have hcarry : f carry=⟨x^p,pow_prime_mem H x hx⟩ := f.apply_symm_apply _
    rw [hcarry,normalForm_extensionMul H x hx]
    rfl
  have hv : VerifiedGroupTable.Valid identity op := VerifiedGroupTable.valid_of_transport e identity op he1 hem
  let u := VerifiedGroupTable.group identity op hv
  refine ⟨images,carry,u,?_,?_⟩
  · change (if h : VerifiedGroupTable.Valid identity op then some (VerifiedGroupTable.group identity op h) else none)=_
    rw [dif_pos hv]
  · exact ⟨validatedEquiv e identity op hv hem⟩

end GroupWL.PGroupCandidateCoverage
