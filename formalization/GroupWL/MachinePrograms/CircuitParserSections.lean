import GroupWL.MachinePrograms.CircuitParserControl

/-! Section preparation and decoding, with explicit execution and frame bounds. -/
namespace GroupWL.MachinePrograms.CircuitParserStages
open NatArrayLanguage CircuitRecordParser AddressedCircuit CircuitDescription
open NatArrayLowering (bitNat)
set_option maxHeartbeats 2000000
variable {T : Type*} [FiniteCode T] {r : ℕ}

def sectionCode (as : List (Atom Reg Arr)) (output : WorkArr) : Code :=
  .seq (atoms as) (stage output)

theorem section_runs (C : Circuit T r) (as : List (Atom Reg Arr)) (output : WorkArr)
    (xs : List Token) (w tail : List Bool) (M stride un : ℕ) (S : State)
    (bounded : S.Bounded M) (room : 1≤M) (ready : Ready w S) (metadata : Metadata C S)
    (pure : PureControls as) (valid : ValidAtoms M as S)
    (hs : (applyAtoms as S).scalar (wr .stride)=stride)
    (hu : (applyAtoms as S).scalar (wr .unaryCount)=un)
    (hc : (applyAtoms as S).scalar (wr .count)=xs.length)
    (word : w.drop (S.scalar (cr .cursor))=stream xs++tail)
    (positive : 0<xs.length → 0<stride)
    (shape : ∀i : Fin xs.length,(xs[i]).isNat=decide (i.val%stride<un)) :
    ∃t≤xs.length*(7*w.length+18)+as.length+10,∃U,
      Runs (storageBound Reg Arr M) (sectionCode as output) S t U ∧ U.Bounded M ∧
      Ready w U ∧ Metadata C U ∧ U.array (wa output)=xs.map Token.value ∧
      w.drop (U.scalar (cr .cursor))=tail ∧ ∀a≠output,U.array (wa a)=S.array (wa a) := by
  obtain ⟨pre,hV⟩ := atoms_runs bounded as valid
  have vr := pure.ready ready
  obtain ⟨t,ht,U,run,hU,out,ui,ul,uv,rest,left,frame⟩ := stage_runs output xs w tail M stride un
    (applyAtoms as S) hV room vr.length vr.valid vr.input hs hu hc
    (by rwa [pure.cursor]) positive shape
  refine ⟨as.length+t,by omega,U,.seq pre run,hU,vr.of_stage left ul uv ui,
    (pure.metadata metadata).of_stage left,out,rest,?_⟩
  intro a ha
  rw [frame a ha,(pure S).1]

def opening : Code := .seq (atoms initAtoms) (.seq (stage .header) (atoms loadHeaderAtoms))

theorem opening_runs (C : Circuit T r) (S : State) (M : ℕ)
    (bounded : S.Bounded M) (room : 5≤M)
    (input : S.array (ca .input)=(circuitWord C).map bitNat) :
    ∃t≤5*(7*(circuitWord C).length+18)+30,∃U,
      Runs (storageBound Reg Arr M) opening S t U ∧ U.Bounded M ∧
      Ready (circuitWord C) U ∧ Metadata C U ∧
      U.array (wa .header)=List.ofFn (headerValues C) ∧
      (circuitWord C).drop (U.scalar (cr .cursor))=
        kindWord C++stream (schemaRecords C)++stream (seedRecords C)++stream (testRecords C) := by
  obtain ⟨init,hV,vr,vc,vcount,vs,vu⟩ := init_runs (circuitWord C) S M bounded room input
  let V := applyAtoms initAtoms S
  obtain ⟨t,ht,W,run,hW,out,wi,wl,wv,rest,left,frame⟩ := stage_runs .header (headerTokens C)
    (circuitWord C) (kindWord C++stream (schemaRecords C)++stream (seedRecords C)++stream (testRecords C))
    M 5 5 V hV (by omega) vr.length vr.valid vr.input vs vu
    (by simpa using vcount)
    (by rw [vc,List.drop_zero,headerTokens_stream,circuitWord_records]; simp only [List.append_assoc])
    (by omega) (headerTokens_kind C)
  have wh : W.array (wa .header)=List.ofFn (headerValues C) := out.trans (headerTokens_values C)
  obtain ⟨load,hU,ur,um,uc,ua⟩ := loadHeader_runs C (circuitWord C) W M hW room
    (vr.of_stage left wl wv wi) wh
  refine ⟨10+(t+10),by simpa using (show 10+(t+10)≤5*(7*(circuitWord C).length+18)+30 by simpa using (by omega : 10+(t+10)≤(headerTokens C).length*(7*(circuitWord C).length+18)+30)),
    applyAtoms loadHeaderAtoms W,.seq init (.seq run load),hU,ur,um,?_,?_⟩
  · rw [ua]; exact wh
  · rw [uc]; exact rest

end GroupWL.MachinePrograms.CircuitParserStages
