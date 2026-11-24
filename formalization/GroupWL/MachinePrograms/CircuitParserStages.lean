import GroupWL.MachinePrograms.CircuitParserWords
import GroupWL.MachinePrograms.NatArrayComponents

/-! Concrete stage composition for decoding the five sections of a circuit. -/
namespace GroupWL.MachinePrograms.CircuitParserStages
open NatArrayLanguage
open NatArrayLowering (bitNat)

inductive WorkReg where
  | count | stride | unaryCount | types | coordinates | edges | seeds | tests
  | zero | one | two | three | five | index
  deriving DecidableEq,Fintype
inductive WorkArr where | header | kinds | schemas | seeds | tests
  deriving DecidableEq,Fintype
abbrev Reg := WorkReg ⊕ CircuitRecordParser.Reg
abbrev Arr := WorkArr ⊕ CircuitRecordParser.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
abbrev wr : WorkReg → Reg := Sum.inl
abbrev wa : WorkArr → Arr := Sum.inl
abbrev cr : CircuitRecordParser.Reg → Reg := Sum.inr
abbrev ca : CircuitRecordParser.Arr → Arr := Sum.inr

def parser : Code := CircuitRecordParser.program.map cr ca

def stage (output : WorkArr) : Code :=
  .seq (atoms [.copy (cr .count) (wr .count),.copy (cr .stride) (wr .stride),
    .copy (cr .unaryCount) (wr .unaryCount)])
    (.seq parser (.atom (.copyArray (wa output) (ca .output))))

theorem parser_runs {S : State} {T : CircuitRecordParser.State} {M t : ℕ}
    (bounded : S.Bounded M)
    (run : Runs (storageBound CircuitRecordParser.Reg CircuitRecordParser.Arr M)
      CircuitRecordParser.program S.right t T) :
    Runs (storageBound Reg Arr M) parser S t (S.left.join T) := by
  simpa only [parser] using run.right_bounded bounded

theorem stage_runs (output : WorkArr) (xs : List CircuitRecordParser.Token)
    (w tail : List Bool) (M stride un : ℕ) (S : State)
    (bounded : S.Bounded M) (room : 1≤M)
    (length : S.scalar (cr .length)=w.length) (valid : S.scalar (cr .valid)=1)
    (input : S.array (ca .input)=w.map bitNat)
    (hs : S.scalar (wr .stride)=stride) (hu : S.scalar (wr .unaryCount)=un)
    (hc : S.scalar (wr .count)=xs.length)
    (word : w.drop (S.scalar (cr .cursor))=CircuitRecordParser.stream xs++tail)
    (positive : 0<xs.length → 0<stride)
    (shape : ∀i : Fin xs.length,(xs[i]).isNat=decide (i.val%stride<un)) :
    ∃t≤xs.length*(7*w.length+18)+10,∃T,
      Runs (storageBound Reg Arr M) (stage output) S t T ∧ T.Bounded M ∧
      T.array (wa output)=xs.map CircuitRecordParser.Token.value ∧
      T.array (ca .input)=w.map bitNat ∧ T.scalar (cr .length)=w.length ∧
      T.scalar (cr .valid)=1 ∧ w.drop (T.scalar (cr .cursor))=tail ∧
      T.left.scalar=S.left.scalar ∧ ∀a≠output,T.array (wa a)=S.array (wa a) := by
  let pre : List (Atom Reg Arr) := [.copy (cr .count) (wr .count),.copy (cr .stride) (wr .stride),
    .copy (cr .unaryCount) (wr .unaryCount)]
  have pv : ValidAtoms M pre S := by simp [pre,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨pr,hU⟩ := atoms_runs bounded pre pv
  let U := applyAtoms pre S
  have left : U.left=S.left := by
    apply Store.ext
    · intro r; simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.left]
    · intro a; rfl
  obtain ⟨t,ht,V,run,hV,out,vin,vlen,vvalid,vrest⟩ := CircuitRecordParser.program_runs xs w tail M stride un
    U.right hU.right room
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.right,length])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.right,valid]) input
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.right,hs])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.right,hu])
    (by simp [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.right,hc])
    (by simpa [U,pre,applyAtoms,Atom.apply,Store.setScalar,Store.right] using word) positive shape
  have run' := parser_runs hU run
  let W := U.left.join V
  have hW : W.Bounded M := hU.left.join hV
  let finish : Atom Reg Arr := .copyArray (wa output) (ca .output)
  have last := atom_runs hW finish trivial trivial
  let T := finish.apply W
  have hT := finish.apply_bounded hW trivial
  refine ⟨3+(t+1),by omega,T,.seq pr (.seq run' last),hT,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [T,finish,Atom.apply,Store.setArray,W] using out
  · simpa [T,finish,Atom.apply,Store.setArray,W] using vin
  · simpa [T,finish,Atom.apply,Store.setArray,W] using vlen
  · simpa [T,finish,Atom.apply,Store.setArray,W] using vvalid
  · simpa [T,finish,Atom.apply,Store.setArray,W] using vrest
  · change U.left.scalar=S.left.scalar
    rw [left]
  · intro a ha
    have he : U.array (wa a)=S.array (wa a) := rfl
    simpa [T,finish,Atom.apply,Store.setArray,W,ha] using he

end GroupWL.MachinePrograms.CircuitParserStages
