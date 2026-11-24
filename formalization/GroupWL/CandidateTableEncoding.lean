import GroupWL.NumericPGroupCandidateTables
import GroupWL.MachinePrograms.GroupInitial

namespace GroupWL.MachinePrograms.GroupInitial

theorem tableWord_finCongr {n m : ℕ} (h : n=m) (op : Fin m→Fin m→Fin m) :
    tableWord (fun x y => (finCongr h).symm (op (finCongr h x) (finCongr h y)))=tableWord op := by
  cases h
  rfl

end GroupWL.MachinePrograms.GroupInitial

namespace GroupWL.NumericPGroupCandidates
open MachinePrograms
variable {p D : ℕ} [Fact p.Prime]

theorem nextOperation_tableWord (g : Group (Fin (p^D))) (images : Fin D→Fin (p^D)) (carry : Fin (p^D)) :
    GroupInitial.tableWord (nextOperation g images carry)=GroupInitial.tableWord
      (ExtensionTablePrograms.operation (Fact.out : p.Prime).pos (operation g) (expand g images) carry (identity g)) :=
  GroupInitial.tableWord_finCongr (pow_succ' p D) _

theorem raw_valid_iff (g : Group (Fin (p^D))) (images : Fin D→Fin (p^D)) (carry : Fin (p^D))
    (hid : identity g=zero p D) :
    VerifiedGroupTable.Valid (finProdFinEquiv ((⟨0,(Fact.out : p.Prime).pos⟩ : Fin p),identity g))
      (ExtensionTablePrograms.operation (Fact.out : p.Prime).pos (operation g) (expand g images) carry (identity g)) ↔
      (extend g images carry).isSome=true := by
  have he : (finCongr (pow_succ' p D)).symm
      (finProdFinEquiv ((⟨0,(Fact.out : p.Prime).pos⟩ : Fin p),identity g))=zero p (D+1) := by
    apply Fin.ext
    simp [hid,zero,finProdFinEquiv]
  have h := VerifiedGroupTable.valid_reindex_iff (finCongr (pow_succ' p D))
    (finProdFinEquiv ((⟨0,(Fact.out : p.Prime).pos⟩ : Fin p),identity g))
    (ExtensionTablePrograms.operation (Fact.out : p.Prime).pos (operation g) (expand g images) carry (identity g))
  rw [he] at h
  exact h.trans (extend_isSome_iff g images carry hid).symm

end GroupWL.NumericPGroupCandidates
