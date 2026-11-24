import GroupWL.NumericPGroupCandidates
import GroupWL.GroupTableTransport

/-! Accepted numeric candidates expose exactly the multiplication tables
constructed by the operational extension builder, with identity index zero. -/
namespace GroupWL.NumericPGroupCandidates
open MachinePrograms
variable {p D : ℕ} [Fact p.Prime]

def nextOperation (t : Group (Fin (p^D))) (images : Fin D → Fin (p^D)) (carry : Fin (p^D))
    (a b : Fin (p^(D+1))) : Fin (p^(D+1)) :=
  (finCongr (pow_succ' p D)).symm
    (ExtensionTablePrograms.operation (Fact.out : p.Prime).pos (operation t) (expand t images) carry (identity t)
      (finCongr (pow_succ' p D) a) (finCongr (pow_succ' p D) b))

theorem nextOperation_eq (t : Group (Fin (p^D))) (images : Fin D → Fin (p^D)) (carry : Fin (p^D))
    (a b : Fin (p^(D+1))) :
    nextOperation t images carry a b=(extensionEquiv p D).symm
      (@PGroupDecomposition.extensionMul p (Fact.out : p.Prime).pos (Fin (p^D)) t.toMonoid
        (expand t images) carry (extensionEquiv p D a) (extensionEquiv p D b)) := by
  letI := t
  let x := extensionEquiv p D a
  let y := extensionEquiv p D b
  have hx : ExtensionTablePrograms.encodePair (Equiv.refl (Fin (p^D))) x=finCongr (pow_succ' p D) a := by
    change finProdFinEquiv (finProdFinEquiv.symm (finCongr (pow_succ' p D) a))=_
    exact Equiv.apply_symm_apply _ _
  have hy : ExtensionTablePrograms.encodePair (Equiv.refl (Fin (p^D))) y=finCongr (pow_succ' p D) b := by
    change finProdFinEquiv (finProdFinEquiv.symm (finCongr (pow_succ' p D) b))=_
    exact Equiv.apply_symm_apply _ _
  have hm := ExtensionTablePrograms.operation_extensionMul (Fact.out : p.Prime).pos
    (Equiv.refl (Fin (p^D))) (expand t images) carry x y
  rw [hx,hy] at hm
  exact congrArg (finCongr (pow_succ' p D)).symm hm

theorem extend_properties (t : Group (Fin (p^D))) (images : Fin D → Fin (p^D)) (carry : Fin (p^D))
    (u : Group (Fin (p^(D+1)))) (h : extend t images carry=some u) :
    identity u=(extensionEquiv p D).symm (⟨0,(Fact.out : p.Prime).pos⟩,identity t) ∧
      operation u=nextOperation t images carry := by
  unfold extend PGroupCandidateCoverage.extend at h
  dsimp only at h
  split at h
  · simp only [Option.map_some,Option.some.injEq] at h
    subst u
    constructor
    · rfl
    · funext a b
      exact (nextOperation_eq t images carry a b).symm
  · simp only [Option.map_none] at h
    cases h

theorem extensionEquiv_zero :
    (extensionEquiv p D).symm (⟨0,(Fact.out : p.Prime).pos⟩,zero p D)=zero p (D+1) := by
  apply Fin.ext
  simp [extensionEquiv,zero,finProdFinEquiv]

theorem decode_identity (D q : ℕ) (t : Group (Fin (p^D))) (h : decode D q=some t) :
    identity t=zero p D := by
  induction D generalizing q with
  | zero =>
      simp only [decode,Option.some.injEq] at h
      subst t
      rfl
  | succ D ih =>
      simp only [decode] at h
      split at h
      · cases h
      · rename_i u hu
        have hid := ih _ u hu
        rw [(extend_properties _ _ _ t h).1,hid,extensionEquiv_zero]

theorem extend_isSome_iff (t : Group (Fin (p^D))) (images : Fin D → Fin (p^D)) (carry : Fin (p^D))
    (hid : identity t=zero p D) :
    (extend t images carry).isSome=true ↔
      VerifiedGroupTable.Valid (zero p (D+1)) (nextOperation t images carry) := by
  letI := t
  let onePair : Fin p × Fin (p^D) := (⟨0,(Fact.out : p.Prime).pos⟩,identity t)
  let op := @PGroupDecomposition.extensionMul p (Fact.out : p.Prime).pos (Fin (p^D)) t.toMonoid
    (expand t images) carry
  have hv := VerifiedGroupTable.valid_reindex_iff (extensionEquiv p D) onePair op
  have he : (extensionEquiv p D).symm onePair=zero p (D+1) := by
    apply Fin.ext
    simp [onePair,extensionEquiv,zero,finProdFinEquiv,hid]
  have hop : (fun a b => (extensionEquiv p D).symm (op (extensionEquiv p D a) (extensionEquiv p D b)))=
      nextOperation t images carry := funext (fun a => funext (fun b => (nextOperation_eq t images carry a b).symm))
  rw [he,hop] at hv
  rw [←hv]
  unfold extend PGroupCandidateCoverage.extend
  dsimp only
  change (Option.map (transportedGroup (extensionEquiv p D))
    (if h : VerifiedGroupTable.Valid onePair op then some (VerifiedGroupTable.group onePair op h) else none)).isSome=true ↔ _
  split <;> simp_all

theorem extend_check (t : Group (Fin (p^D))) (images : Fin D → Fin (p^D)) (carry : Fin (p^D))
    (hid : identity t=zero p D) :
    (extend t images carry).isSome=VerifiedGroupTable.check (zero p (D+1)) (nextOperation t images carry) := by
  apply Bool.eq_iff_iff.mpr
  rw [extend_isSome_iff t images carry hid,VerifiedGroupTable.check_correct]

end GroupWL.NumericPGroupCandidates
