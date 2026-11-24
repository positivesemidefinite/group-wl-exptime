import GroupWL.MachinePrograms.ArrayMaterialization
import GroupWL.MachinePrograms.NatArrayFrames

/-! Scalar-first ring dimensions from the computed readout radical widths. -/
namespace GroupWL.MachinePrograms.RingDimensions
open NatArrayLanguage
set_option maxHeartbeats 1400000

inductive Reg where
  | total | index | remaining | one | zero | unit | blocks | readout | result | flag
  deriving DecidableEq,Fintype
inductive Arr where | widths | output deriving DecidableEq,Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def value (widths : List ℕ) (b i : ℕ) : ℕ := if i<b then 2 else widths[i-b]?.getD 0+1
def registers : Fin 5 ↪ Reg := ⟨![.total,.index,.remaining,.one,.zero],by decide⟩
def headAtoms : List (Atom Reg Arr) := [.const .unit 1,.binary .lt .flag .index .blocks]
def tailAtoms : List (Atom Reg Arr) := [
  .binary .sub .readout .index .blocks,.read .result .widths .readout,.binary .add .result .result .unit]
def cell : Code := .seq (atoms headAtoms) (.branch .flag (.atom (.const .result 2)) (atoms tailAtoms))
def program : Code := materialize registers .output .result cell

def Ready (widths : List ℕ) (b : ℕ) (S : State) : Prop :=
  S.array .widths=widths ∧ S.scalar .blocks=b ∧ S.scalar .total=b+widths.length

theorem read_le (widths : List ℕ) (b : ℕ) (h : ∀ x∈widths,x≤b) (i : ℕ) :
    widths[i]?.getD 0≤b := by
  cases hx : widths[i]? with
  | none => exact Nat.zero_le _
  | some x => exact h x (List.mem_of_getElem? hx)

theorem cell_runs (widths : List ℕ) (b M : ℕ) (hM : b+2≤M) (hv : ∀ x∈widths,x≤b)
    (S : State) (ready : Ready widths b S) (bounded : S.Bounded M)
    (hi : S.scalar .index<b+widths.length) :
    ∃ t≤6, ∃ T, Runs (storageBound Reg Arr M) cell S t T ∧ T.Bounded M ∧ Ready widths b T ∧
      T.scalar .result=value widths b (S.scalar .index) ∧ T.array .output=S.array .output ∧
      ∀ i : Fin 4, T.scalar (registers i.castSucc)=S.scalar (registers i.castSucc) := by
  rcases ready with ⟨hws,hb,ht⟩
  have headValid : ValidAtoms M headAtoms S := by
    simp [headAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval]
    split_ifs <;> omega
  obtain ⟨headRun,hUB⟩ := atoms_runs bounded headAtoms headValid
  let U := applyAtoms headAtoms S
  have uflag : U.scalar .flag=if S.scalar .index<b then 1 else 0 := by
    simp [U,headAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hb]
  have finishPost (T : State) (t : ℕ) (run : Runs (storageBound Reg Arr M) cell S t T) :
      Ready widths b T ∧ T.array .output=S.array .output ∧
      ∀ i : Fin 4, T.scalar (registers i.castSucc)=S.scalar (registers i.castSucc) := by
    refine ⟨⟨(run.array_eq_of_not_mem .widths (by decide)).trans hws,
      (run.scalar_eq_of_not_mem .blocks (by decide)).trans hb,
      (run.scalar_eq_of_not_mem .total (by decide)).trans ht⟩,
      run.array_eq_of_not_mem .output (by decide),?_⟩
    intro i
    fin_cases i <;> exact run.scalar_eq_of_not_mem _ (by decide)
  by_cases hs : S.scalar .index<b
  · have last := atom_runs hUB (Atom.const Reg.result 2) trivial (by change 2≤M; omega)
    have run : Runs (storageBound Reg Arr M) cell S 4 ((Atom.const Reg.result 2).apply U) :=
      headRun.seq (.branch_nonzero (by rw [uflag,if_pos hs]; decide) last)
    have post := finishPost _ _ run
    refine ⟨4,by omega,_,run,hUB.setScalar _ (by omega),post.1,?_,post.2.1,post.2.2⟩
    simp [Atom.apply,Store.setScalar,value,hs]
  · have hj : S.scalar .index-b<widths.length := by omega
    have hsub : S.scalar .index-b≤M := (Nat.sub_le _ _).trans (bounded.1 _)
    have hv' : widths[S.scalar .index-b]?.getD 0+1≤M := by have := read_le widths b hv (S.scalar .index-b); omega
    have tailValid : ValidAtoms M tailAtoms U := by
      simp [tailAtoms,U,headAtoms,applyAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,
        BinaryOp.eval,Store.setScalar,hws,hb,hj,hsub]
      simpa only [List.getElem?_eq_getElem hj,Option.getD_some] using hv'
    obtain ⟨tailRun,hTB⟩ := atoms_runs hUB tailAtoms tailValid
    have run : Runs (storageBound Reg Arr M) cell S 6 (applyAtoms tailAtoms U) :=
      headRun.seq (.branch_zero (by rw [uflag,if_neg hs]) tailRun)
    have post := finishPost _ _ run
    refine ⟨6,le_rfl,_,run,hTB,post.1,?_,post.2.1,post.2.2⟩
    simp [tailAtoms,U,headAtoms,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hws,hb,value,hs]

theorem program_runs (widths : List ℕ) (b M : ℕ) (hM : b+2≤M) (hv : ∀ x∈widths,x≤b)
    (S : State) (ready : Ready widths b S) (bounded : S.Bounded M) :
    ∃ t≤(b+widths.length)*10+6, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧
      T.Bounded M ∧ Ready widths b T ∧
      T.array .output=List.ofFn (fun i : Fin (b+widths.length) => value widths b i.val) := by
  apply materialize_runs registers .output .result cell (Ready widths b) (value widths b) M
    (b+widths.length) 6 (by omega)
  · intro T hT i v
    fin_cases i <;> simpa [Ready,registers,Store.setScalar] using hT
  · intro T hT xs
    simpa [Ready,Store.setArray] using hT
  · exact fun T hT hB hi => cell_runs widths b M hM hv T hT hB hi
  · exact bounded
  · exact ready
  · exact ready.2.2

end GroupWL.MachinePrograms.RingDimensions
