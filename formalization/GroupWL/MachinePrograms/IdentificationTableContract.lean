import GroupWL.MachinePrograms.IdentificationTest
import GroupWL.MachinePrograms.TableWLCorrectness

/-! Discharge the WL-client contract using the proved concrete I/II program. -/
namespace GroupWL.MachinePrograms.IdentificationTest
open NatArrayLanguage
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1500000
variable {p D k B : ℕ} [Fact p.Prime]
variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

def version (word : Bool) : Refinement.Version := if word then .two else .one

theorem table_contract (word : Bool) (e : G≃Fin (p^D)) (he : (e 1).val=0)
    (matrixRoom : InitialMatrixPrograms.Room (p^D) (p^D) k B)
    (productRoom : (p^D)^4≤B)
    (room : IndexedWL.Room ((p^D)^k+(p^D)^k) k (p^D) B) :
    WLContract (version word) word k B e := by
  intro g S hg hb hn hm hk hs ht
  letI := g
  letI : Mul (Fin (p^D)) := g.toMul
  have targetTable : S.array (TableWL.array .targets)=GroupInitial.tableWord
      (GroupInitial.encodedMul (Equiv.refl (Fin (p^D)))) := ht
  obtain ⟨t,htime,T,run,hT,out⟩ := TableWL.decide_runs word e (Equiv.refl (Fin (p^D))) he hg S B
    ⟨hb,hn,hm,hk,hs,targetTable⟩ matrixRoom (by simpa using productRoom) (by simpa using room)
  refine ⟨t,htime,T,run,hT,?_⟩
  cases word <;> simpa [version,Refinement.GroupEquivalent] using out

end GroupWL.MachinePrograms.IdentificationTest
