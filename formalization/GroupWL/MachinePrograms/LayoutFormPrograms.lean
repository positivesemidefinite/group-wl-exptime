import GroupWL.MachinePrograms.LayoutIncidencePrograms
import GroupWL.MachinePrograms.LinkFormRecords
import GroupWL.MachinePrograms.DuplicateFlags

/-! Incidence records followed by both repeated and compacted linear-form arrays. -/
namespace GroupWL.MachinePrograms.LayoutFormPrograms
open NatArrayLanguage LayoutMetadata
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 32768
set_option maxRecDepth 16384
abbrev FormReg := LinkFormRecords.Reg⊕LinkFormRecords.Reg
abbrev FormArr := LinkFormRecords.Arr⊕LinkFormRecords.Arr
abbrev Reg := LayoutIncidencePrograms.Reg⊕(ArrayRepeatBlocks.Reg⊕FormReg)
abbrev Arr := LayoutIncidencePrograms.Arr⊕(ArrayRepeatBlocks.Arr⊕FormArr)
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
abbrev oldr (r : LayoutIncidencePrograms.Reg) : Reg := .inl r
abbrev dr (r : ArrayRepeatBlocks.Reg) : Reg := .inr (.inl r)
abbrev da (a : ArrayRepeatBlocks.Arr) : Arr := .inr (.inl a)
abbrev flr (r : LinkFormRecords.Reg) : Reg := .inr (.inr (.inl r))
abbrev frr (r : LinkFormRecords.Reg) : Reg := .inr (.inr (.inr r))
abbrev fla (a : LinkFormRecords.Arr) : Arr := .inr (.inr (.inl a))
abbrev fra (a : LinkFormRecords.Arr) : Arr := .inr (.inr (.inr a))
def duplicateSetup : List (Atom Reg Arr) := [
  .copyArray (da .input) (.inl (.inl (.inl (.inl (.inr (.inr .output)))))),
  .arrayLength (dr .blocks) (da .input),.const (dr .width) 1,.const (dr .repeats) 2]
def formSetup : List (Atom Reg Arr) := [
  .copy (flr (.inl .comparisons)) (oldr (LayoutIncidencePrograms.nr .comparisons)),
  .copy (flr (.inl .length)) (oldr (LayoutIncidencePrograms.lr (LinkLabels.lr .length))),
  .const (dr .width) 4,.binary .mul (flr (.inr (.inl .repeats))) (dr .width) (oldr (LayoutIncidencePrograms.nr .width)),
  .const (dr .repeats) 2,.binary .mul (flr (.inr (.inr .selected))) (dr .repeats) (oldr (LayoutIncidencePrograms.sreg .count)),
  .copyArray (fla (.inr (.inr .flags))) (da .output),
  .copy (frr (.inl .comparisons)) (flr (.inl .comparisons)),
  .copy (frr (.inl .length)) (flr (.inl .length)),
  .copy (frr (.inr (.inl .repeats))) (flr (.inr (.inl .repeats))),
  .copy (frr (.inr (.inr .selected))) (flr (.inr (.inr .selected))),
  .copyArray (fra (.inr (.inr .flags))) (da .output)]
def formPair : NatArrayLanguage.Program FormReg FormArr :=
  .seq ((LinkFormRecords.program false).map Sum.inl Sum.inl)
    ((LinkFormRecords.program true).map Sum.inr Sum.inr)
def forms : Code := .seq (atoms duplicateSetup)
  (.seq ((ArrayRepeatBlocks.program.map Sum.inl Sum.inl).map Sum.inr Sum.inr)
    (.seq (atoms formSetup) ((formPair.map Sum.inr Sum.inr).map Sum.inr Sum.inr)))
def program : Code := .seq (LayoutIncidencePrograms.program.map Sum.inl Sum.inl) forms
def word (C : ComparisonMetadata.Table) (L : ℕ) (right : Bool) : List ℕ :=
  SelectArray.selectedPrefix (DuplicateFlags.word (squareFlags C L))
    (RepeatedSelection.repeated (LinkFormRecords.forms right (if right then C.targetForm else C.sourceForm)
      C.comparisons L) (linkCount C L) 2 (4*C.coordinates)) (DuplicateFlags.word (squareFlags C L)).length

structure Output (C : ComparisonMetadata.Table) (L : ℕ) (S : State) : Prop where
  incidence : LayoutIncidencePrograms.Output C L S.left
  leftForm : S.right.right.left.right.right.array .output=word C L false
  rightForm : S.right.right.right.right.right.array .output=word C L true

theorem forms_runs (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : LayoutIncidencePrograms.Output C L S.left)
    (source : S.right.right.left.left.array .forms=C.sourceForm)
    (target : S.right.right.right.left.array .forms=C.targetForm)
    (room : 4≤M) (copies : 4*C.coordinates≤M) (size : 2*(squareFlags C L).length≤M)
    (links : 2*linkCount C L≤M) (binary : ∀x∈C.domain,x≤1)
    (sourceLength : C.sourceForm.length=2*C.comparisons) (targetLength : C.targetForm.length=2*C.comparisons) :
    ∃t≤86*(squareFlags C L).length+36*linkCount C L+94,∃T,
      Runs (storageBound Reg Arr M) forms S t T ∧ T.Bounded M ∧ Output C L T := by
  obtain ⟨first,hU⟩ := atoms_runs bounded duplicateSetup (by
    simp [duplicateSetup,ValidAtoms,Atom.Valid,Atom.SmallResult];omega)
  let U := applyAtoms duplicateSetup S
  have ui : U.right.left.array .input=squareFlags C L := input.metadata.ranks.flags.square
  have ub : U.right.left.scalar .blocks=(squareFlags C L).length := by
    simpa [U,duplicateSetup,applyAtoms,Atom.apply,Store.setScalar,Store.right,Store.left,dr,da]
      using congrArg List.length input.metadata.ranks.flags.square
  have uw : U.right.left.scalar .width=1 := rfl
  have ur : U.right.left.scalar .repeats=2 := rfl
  obtain ⟨t,ht,V,dup,hV,hdup⟩ := ArrayRepeatBlocks.program_runs U.right.left M hU.right.left (by omega)
    (by rw [ui,ub,uw];simp) (by simpa [ub,uw,ur,Nat.mul_comm] using size)
  let W := U.left.join (V.join U.right.right)
  have hW : W.Bounded M := hU.left.join (hV.join hU.right.right)
  have duprun := (dup.left_bounded hU.right).right_bounded hU
  have wo : W.array (da .output)=DuplicateFlags.word (squareFlags C L) := by
    simpa [W,DuplicateFlags.word,RepeatedSelection.repeated,ui,ub,uw,ur] using hdup
  have se : W.scalar (oldr (LayoutIncidencePrograms.nr .comparisons))=C.comparisons := input.metadata.ranks.flags.labels.comparisons
  have sl : W.scalar (oldr (LayoutIncidencePrograms.lr (LinkLabels.lr .length)))=L := input.metadata.ranks.flags.labels.length
  have sw : W.scalar (oldr (LayoutIncidencePrograms.nr .width))=C.coordinates := input.metadata.ranks.flags.labels.width
  have ss : W.scalar (oldr (LayoutIncidencePrograms.sreg .count))=squareCount C L := input.metadata.ranks.squareCount
  have smallCount := FilterRanks.count_le (LayoutFlagPrograms.square_binary C L binary) (squareFlags C L).length
  change squareCount C L≤(squareFlags C L).length at smallCount
  have fs : ValidAtoms M formSetup W := by
    simp [formSetup,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,sw,ss]
    exact ⟨room,copies,by omega,by omega⟩
  obtain ⟨middle,hX⟩ := atoms_runs hW formSetup fs
  let X := applyAtoms formSetup W
  have le : X.right.right.left.left.scalar .comparisons=C.comparisons := by
    simpa [X,formSetup,applyAtoms,Atom.apply,Store.setScalar,Store.right,Store.left,flr,frr,dr,oldr] using se
  have ll : X.right.right.left.left.scalar .length=L := by
    simpa [X,formSetup,applyAtoms,Atom.apply,Store.setScalar,Store.right,Store.left,flr,frr,dr,oldr] using sl
  have lp : X.right.right.left.right.left.scalar .repeats=4*C.coordinates := by
    simpa [X,formSetup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.right,Store.left,flr,frr,dr,oldr] using sw
  have lc : X.right.right.left.right.right.scalar .selected=2*squareCount C L := by
    simpa [X,formSetup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.right,Store.left,flr,frr,dr,oldr] using ss
  have lf : X.right.right.left.right.right.array .flags=DuplicateFlags.word (squareFlags C L) := wo
  have li : X.right.right.left.left.array .forms=C.sourceForm := source
  have re : X.right.right.right.left.scalar .comparisons=C.comparisons := le
  have rl : X.right.right.right.left.scalar .length=L := ll
  have rp : X.right.right.right.right.left.scalar .repeats=4*C.coordinates := lp
  have rc : X.right.right.right.right.right.scalar .selected=2*squareCount C L := lc
  have rf : X.right.right.right.right.right.array .flags=DuplicateFlags.word (squareFlags C L) := wo
  have ri : X.right.right.right.left.array .forms=C.targetForm := target
  have select : FilterRanks.count (DuplicateFlags.word (squareFlags C L))
      (DuplicateFlags.word (squareFlags C L)).length=2*squareCount C L := by
    rw [DuplicateFlags.length,DuplicateFlags.count_even _ _ le_rfl];rfl
  obtain ⟨a,ha,A,run,hA,hleft⟩ := LinkFormRecords.program_runs false X.right.right.left M hX.right.right.left
    (by omega) (by simpa [le,ll,linkCount,Nat.mul_comm] using links)
    (by rw [li,le];exact sourceLength)
    (by rw [lf,le,ll,lp,DuplicateFlags.length];simp [squareFlags,linkCount];ring)
    (by rw [lf];exact DuplicateFlags.binary _ (LayoutFlagPrograms.square_binary C L binary))
    (by rw [lc,lf,select])
  let Y := A.join X.right.right.right
  have hY : Y.Bounded M := hA.join hX.right.right.right
  obtain ⟨b,hb,B,last,hB,hright⟩ := LinkFormRecords.program_runs true Y.right M hY.right
    (by omega) (by simpa [Y,re,rl,linkCount,Nat.mul_comm] using links)
    (by simp only [Y,Store.right_join,ri,re];exact targetLength)
    (by simp only [Y,Store.right_join,rf,re,rl,rp,DuplicateFlags.length];simp [squareFlags,linkCount];ring)
    (by change ∀x∈X.right.right.right.right.right.array .flags,x≤1;rw [rf];
        exact DuplicateFlags.binary _ (LayoutFlagPrograms.square_binary C L binary))
    (by simp only [Y,Store.right_join,rc,rf,select])
  have pair := (run.left_bounded hX.right.right).seq (last.right_bounded hY)
  refine ⟨4+(t+(12+(a+b))),?_,X.left.join (X.right.left.join (Y.left.join B)),
    first.seq (duprun.seq (middle.seq ((pair.right_bounded hX.right).right_bounded hX))),
    hX.left.join (hX.right.left.join (hY.left.join hB)),input,?_,?_⟩
  · rw [ub,uw,ur] at ht
    rw [le,ll,lf,DuplicateFlags.length] at ha
    change b≤9*((X.right.right.right.left.scalar .comparisons+X.right.right.right.left.scalar .comparisons*
      X.right.right.right.left.scalar .length+X.right.right.right.left.scalar .comparisons)*2)+
      17*(X.right.right.right.right.right.array .flags).length+35 at hb
    rw [re,rl,rf,DuplicateFlags.length] at hb
    unfold linkCount;omega
  · simpa [word,le,ll,lp,lf,li,linkCount] using hleft
  · simpa [word,Y,re,rl,rp,rf,ri,linkCount] using hright

theorem program_runs (C : ComparisonMetadata.Table) (L M : ℕ) (S : State)
    (bounded : S.Bounded M) (input : LayoutIncidencePrograms.Input C L S.left)
    (source : S.right.right.left.left.array .forms=C.sourceForm)
    (target : S.right.right.right.left.array .forms=C.targetForm)
    (valid : LayoutIncidencePrograms.Valid C) (room : LayoutIncidencePrograms.Room C L M) (positive : 0<L)
    (copies : 4*C.coordinates≤M) (size : 2*(squareFlags C L).length≤M) (links : 2*linkCount C L≤M)
    (sourceLength : C.sourceForm.length=2*C.comparisons) (targetLength : C.targetForm.length=2*C.comparisons) :
    ∃t≤130*(nodeCount C L*C.coordinates)+1286*(linkCount C L*C.coordinates)+94*linkCount C L+274,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧ Output C L T := by
  obtain ⟨t,ht,U,first,hU,hout⟩ := LayoutIncidencePrograms.program_runs C L M S.left bounded.left input valid room positive
  let V := U.join S.right
  have hV : V.Bounded M := hU.join bounded.right
  obtain ⟨s,hs,T,last,hT,output⟩ := forms_runs C L M V hV hout source target room.four copies size links
    valid.domainBinary sourceLength targetLength
  simp only [squareFlags,List.length_ofFn] at hs
  exact ⟨t+s,by omega,T,(first.left_bounded bounded).seq last,hT,output⟩

end GroupWL.MachinePrograms.LayoutFormPrograms
