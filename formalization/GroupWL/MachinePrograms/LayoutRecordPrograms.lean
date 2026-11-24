import GroupWL.MachinePrograms.LayoutFormPrograms
import GroupWL.MachinePrograms.ReadoutDimensionProgram
import GroupWL.MachinePrograms.SquareChargeRecords

/-! Complete executable coefficient, dimension, and charge record generation. -/
namespace GroupWL.MachinePrograms.LayoutRecordPrograms
open NatArrayLanguage LayoutMetadata
set_option maxHeartbeats 5000000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
abbrev Reg := LayoutFormPrograms.Reg⊕(ReadoutDimensionProgram.Reg⊕SquareChargeRecords.Reg)
abbrev Arr := LayoutFormPrograms.Arr⊕(ReadoutDimensionProgram.Arr⊕SquareChargeRecords.Arr)
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
abbrev oldr (r : LayoutIncidencePrograms.Reg) : Reg := .inl (.inl r)
abbrev olda (a : LayoutIncidencePrograms.Arr) : Arr := .inl (.inl a)
abbrev dr (r : ReadoutDimensionProgram.Reg) : Reg := .inr (.inl r)
abbrev da (a : ReadoutDimensionProgram.Arr) : Arr := .inr (.inl a)
abbrev cr (r : SquareChargeRecords.Reg) : Reg := .inr (.inr r)
abbrev ca (a : SquareChargeRecords.Arr) : Arr := .inr (.inr a)
abbrev vr : Reg := oldr (.inl (.inl (.inr (.inr (.inl .count)))))
abbrev hf : Arr := olda (.inl (.inl (.inl (.inr (.inl .output)))))
abbrev sf : Arr := olda (.inl (.inl (.inl (.inr (.inr .output)))))
def setup : List (Atom Reg Arr) := [
  .const (cr (.inl .one)) 1,.const (cr (.inl .four)) 4,
  .binary .add (dr (.inl (.inl .count))) (oldr (LayoutIncidencePrograms.lr (LinkLabels.lr .length))) (cr (.inl .one)),
  .binary .mul (dr (.inl (.inl .count))) (dr (.inl (.inl .count))) (oldr (LayoutIncidencePrograms.nr .comparisons)),
  .binary .add (dr (.inl (.inl .count))) (dr (.inl (.inl .count))) (oldr (LayoutIncidencePrograms.nr .types)),
  .binary .mul (dr (.inl (.inr (.inl .repeats)))) (cr (.inl .four)) (oldr (LayoutIncidencePrograms.nr .width)),
  .copy (dr (.inl (.inr (.inr .selected)))) (oldr (LayoutIncidencePrograms.hreg .count)),
  .binary .add (dr (.inr .count)) (oldr (LayoutIncidencePrograms.hreg .count)) vr,
  .copyArray (da (.inl (.inr (.inr .flags)))) hf,
  .binary .mul (cr (.inl .links)) (oldr (LayoutIncidencePrograms.nr .comparisons)) (oldr (LayoutIncidencePrograms.lr (LinkLabels.lr .length))),
  .binary .add (cr (.inl .links)) (cr (.inl .links)) (oldr (LayoutIncidencePrograms.nr .comparisons)),
  .binary .add (cr (.inl .special)) (cr (.inl .links)) (cr (.inl .special)),
  .binary .add (cr (.inl .links)) (cr (.inl .links)) (oldr (LayoutIncidencePrograms.nr .comparisons)),
  .copy (cr (.inl .width)) (oldr (LayoutIncidencePrograms.nr .width)),
  .copy (cr (.inr (.inl .selected))) (oldr (LayoutIncidencePrograms.sreg .count)),
  .copy (cr (.inr (.inr 0))) (oldr (LayoutIncidencePrograms.hreg .count)),
  .copyArray (ca (.inr (.inl .flags))) sf]
def pair : NatArrayLanguage.Program (ReadoutDimensionProgram.Reg⊕SquareChargeRecords.Reg)
    (ReadoutDimensionProgram.Arr⊕SquareChargeRecords.Arr) :=
  .seq (ReadoutDimensionProgram.program.map Sum.inl Sum.inl)
    (SquareChargeRecords.program.map Sum.inr Sum.inr)
def records : Code := .seq (atoms setup) (pair.map Sum.inr Sum.inr)
def program : Code := .seq (LayoutFormPrograms.program.map Sum.inl Sum.inl) records
def dimensionWord (C : ComparisonMetadata.Table) (L : ℕ) :=
  ReadoutDimensionProgram.dimensions C.dimensions (horizontalFlags C L) (nodeCount C L) (4*C.coordinates)
    (horizontalCount C L+verticalCount C L)
def chargeWord (C : ComparisonMetadata.Table) (L q : ℕ) :=
  List.replicate (horizontalCount C L) 0++SelectArray.selectedPrefix (squareFlags C L)
    (SquareChargeRecords.word C.coordinates (C.comparisons+C.comparisons*L+q) (squareFlags C L).length)
    (squareFlags C L).length
structure Output (C : ComparisonMetadata.Table) (L q : ℕ) (S : State) : Prop where
  forms : LayoutFormPrograms.Output C L S.left
  dimensions : S.right.left.right.array .output=dimensionWord C L
  charge : S.right.right.right.right.array 2=chargeWord C L q

theorem records_runs (C : ComparisonMetadata.Table) (L q M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : LayoutFormPrograms.Output C L S.left)
    (dimensions : S.right.left.left.left.array .input=C.dimensions)
    (special : S.right.right.left.scalar .special=q) (qbound : q≤C.comparisons)
    (room : LayoutIncidencePrograms.Room C L M) (copies : 4*C.coordinates≤M)
    (blocks : horizontalCount C L+squareCount C L≤M) (width : 0<C.coordinates)
    (binary : ∀x∈C.domain,x≤1) :
    ∃t≤7*nodeCount C L+17*(horizontalFlags C L).length+7*(horizontalCount C L+verticalCount C L)+
        18*(squareFlags C L).length+8*(horizontalCount C L+squareCount C L)+84,∃T,
      Runs (storageBound Reg Arr M) records S t T ∧ T.Bounded M ∧ Output C L q T := by
  have st : S.scalar (oldr (LayoutIncidencePrograms.nr .types))=C.types := input.incidence.metadata.ranks.flags.labels.types
  have se : S.scalar (oldr (LayoutIncidencePrograms.nr .comparisons))=C.comparisons := input.incidence.metadata.ranks.flags.labels.comparisons
  have sl : S.scalar (oldr (LayoutIncidencePrograms.lr (LinkLabels.lr .length)))=L := input.incidence.metadata.ranks.flags.labels.length
  have sw : S.scalar (oldr (LayoutIncidencePrograms.nr .width))=C.coordinates := input.incidence.metadata.ranks.flags.labels.width
  have sh : S.scalar (oldr (LayoutIncidencePrograms.hreg .count))=horizontalCount C L := input.incidence.metadata.ranks.horizontalCount
  have sv : S.scalar vr=verticalCount C L := input.incidence.metadata.ranks.verticalCount
  have ss : S.scalar (oldr (LayoutIncidencePrograms.sreg .count))=squareCount C L := input.incidence.metadata.ranks.squareCount
  have sq : S.scalar (cr (.inl .special))=q := special
  have valid : ValidAtoms M setup S := by
    simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,st,se,sl,sw,sh,sv,ss,sq]
    have hn := room.nodes
    have hl := room.links
    unfold nodeCount at hn
    unfold linkCount at hl
    exact ⟨by have := room.four;omega,room.four,room.steps,by nlinarith,by nlinarith,
      copies,room.ranks,by omega,by omega,by omega,by omega⟩
  obtain ⟨first,hU⟩ := atoms_runs bounded setup valid
  let U := applyAtoms setup S
  have dn : U.right.left.left.left.scalar .count=nodeCount C L := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.left,Store.right,
      dr,cr,oldr,LayoutIncidencePrograms.nr,LayoutIncidencePrograms.lr] at *
    unfold nodeCount; nlinarith
  have dp : U.right.left.left.right.left.scalar .repeats=4*C.coordinates := by
    simpa [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.left,Store.right,dr,cr,oldr] using sw
  have ds : U.right.left.left.right.right.scalar .selected=horizontalCount C L := by
    simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.left,Store.right,dr,cr,oldr] using sh
  have dt : U.right.left.right.scalar .count=horizontalCount C L+verticalCount C L := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.left,Store.right,dr,cr,oldr,vr] at *
    omega
  have df : U.right.left.left.right.right.array .flags=horizontalFlags C L := input.incidence.metadata.ranks.flags.horizontal
  have di : U.right.left.left.left.array .input=C.dimensions := dimensions
  have cl : U.right.right.left.scalar .links=linkCount C L := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.left,Store.right,dr,cr,oldr] at *
    unfold linkCount;nlinarith
  have cw : U.right.right.left.scalar .width=C.coordinates := by
    simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.left,Store.right,dr,cr,oldr] using sw
  have cq : U.right.right.left.scalar .special=C.comparisons+C.comparisons*L+q := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.left,Store.right,dr,cr,oldr] at *
    nlinarith
  have cs : U.right.right.right.left.scalar .selected=squareCount C L := by
    simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.left,Store.right,dr,cr,oldr] using ss
  have ch : U.right.right.right.right.scalar 0=horizontalCount C L := by
    simpa [U,setup,applyAtoms,Atom.apply,Store.setScalar,Store.left,Store.right,dr,cr,oldr] using sh
  have cf : U.right.right.right.left.array .flags=squareFlags C L := input.incidence.metadata.ranks.flags.square
  obtain ⟨t,ht,V,run,hV,hout⟩ := ReadoutDimensionProgram.program_runs U.right.left M hU.right.left
    (by have := room.four;omega) (by rw [df,dn,dp];simp [horizontalFlags];ring)
    (by rw [df];exact LayoutFlagPrograms.horizontal_binary C L binary) (by rw [ds,df];rfl)
  let W := V.join U.right.right
  have hW : W.Bounded M := hV.join hU.right.right
  obtain ⟨s,hs,X,last,hX,hcharge⟩ := SquareChargeRecords.program_runs W.right M hW.right room.four
    (by simpa [W,cw] using width) (by simp [W,cf,cl,cw,squareFlags])
    (by change ∀x∈U.right.right.right.left.array .flags,x≤1;rw [cf];exact LayoutFlagPrograms.square_binary C L binary)
    (by simp only [W,Store.right_join,cs,cf];rfl) (by simpa [W,ch,cs] using blocks)
  have combined := (run.left_bounded hU.right).seq (last.right_bounded hW)
  refine ⟨17+(t+s),?_,U.left.join (W.left.join X),first.seq (combined.right_bounded hU),
    hU.left.join (hW.left.join hX),input,?_,?_⟩
  · rw [dn,df,dt] at ht
    change s≤18*(U.right.right.right.left.array .flags).length+
      8*(U.right.right.right.right.scalar 0+U.right.right.right.left.scalar .selected)+30 at hs
    rw [cf,ch,cs] at hs;omega
  · simpa [dimensionWord,di,df,dn,dp,dt] using hout
  · simpa [chargeWord,W,ch,cf,cw,cq] using hcharge

theorem program_runs (C : ComparisonMetadata.Table) (L q M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : LayoutIncidencePrograms.Input C L S.left.left)
    (source : S.left.right.right.left.left.array .forms=C.sourceForm)
    (target : S.left.right.right.right.left.array .forms=C.targetForm)
    (dimensions : S.right.left.left.left.array .input=C.dimensions)
    (special : S.right.right.left.scalar .special=q) (qbound : q≤C.comparisons)
    (valid : LayoutIncidencePrograms.Valid C) (room : LayoutIncidencePrograms.Room C L M) (positive : 0<L)
    (copies : 4*C.coordinates≤M) (size : 2*(squareFlags C L).length≤M) (links : 2*linkCount C L≤M)
    (blocks : horizontalCount C L+squareCount C L≤M) (width : 0<C.coordinates)
    (sourceLength : C.sourceForm.length=2*C.comparisons) (targetLength : C.targetForm.length=2*C.comparisons) :
    ∃t≤2000*M+500,∃T,Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧ Output C L q T := by
  obtain ⟨t,ht,U,first,hU,hout⟩ := LayoutFormPrograms.program_runs C L M S.left bounded.left input source target
    valid room positive copies size links sourceLength targetLength
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  obtain ⟨s,hs,T,last,hT,output⟩ := records_runs C L q M V hV hout dimensions special qbound room copies blocks width valid.domainBinary
  have hn := room.nodes
  have hnr := room.horizontal
  have hlr := room.square
  have hhv := room.ranks
  simp only [horizontalFlags,squareFlags,List.length_ofFn] at hs
  exact ⟨t+s,by omega,T,(first.left_bounded bounded).seq last,hT,output⟩

end GroupWL.MachinePrograms.LayoutRecordPrograms
