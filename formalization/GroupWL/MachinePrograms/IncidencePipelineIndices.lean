import GroupWL.MachinePrograms.IncidencePipelineRecords
import GroupWL.MachinePrograms.PairIndices
import GroupWL.MachinePrograms.ArraySlice
import GroupWL.FramePairEncoding
import GroupWL.SourceIncidenceEncoding

/-! Exact, unpadded lists of active incidences and ordered frame pairs. -/
namespace GroupWL.MachinePrograms.IncidencePipeline.Indices
open NatArrayLanguage SourceLayout SourceTableEncoding
set_option synthInstance.maxSize 16384
set_option maxRecDepth 16384

theorem take_as_table (xs : List ℕ) (k : ℕ) (hk : k≤xs.length) :
    List.ofFn (fun i : Fin k => ArraySlice.value xs 0 i)=xs.take k := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<k
  · have hx : i<xs.length := hi.trans_le hk
    simp [ArraySlice.value,hi,hx]
  · simp [hi]

def sliceScalar {U V : Type} (n : U) : ArraySlice.Reg → Ports.Scalar U V
  | .length => .scalar n
  | _ => .literal 0
def sliceArray {V : Type} (a : V) : ArraySlice.Arr → Option V
  | .input => some a | _ => none

variable {U V : Type} [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V]

noncomputable def trim (first : NatArrayLanguage.Program U V) (n : U) (a : V) :=
  Ports.thenRun first (sliceScalar n) (sliceArray a) ArraySlice.program

def trimCost (t k : ℕ) := t+(Fintype.card ArraySlice.Reg+Fintype.card ArraySlice.Arr+(6*k+6))

theorem trim_runs (first : NatArrayLanguage.Program U V) (n : U) (a : V) (M t : ℕ)
    (S : Store (U⊕ArraySlice.Reg) (V⊕ArraySlice.Arr)) (bounded : S.Bounded M) (one : 1≤M) (xs : List ℕ)
    (stage : ∃j≤t,∃T,Runs (storageBound U V M) first S.left j T ∧ T.Bounded M ∧
      T.scalar n=xs.length ∧ xs.length≤(T.array a).length ∧ (T.array a).take (T.scalar n)=xs) :
    ∃j≤trimCost t xs.length,∃T,Runs (storageBound (U⊕ArraySlice.Reg) (V⊕ArraySlice.Arr) M) (trim first n a) S j T ∧
      T.Bounded M ∧ T.right.array .output=xs := by
  obtain ⟨j,hj,T,run,hT,_,hw⟩ := Ports.thenRun_post first (sliceScalar n) (sliceArray a) ArraySlice.program
    S M t (6*xs.length+6) bounded (by intro i k h; cases i <;> simp_all [sliceScalar] <;> omega)
    (fun W => W.scalar n=xs.length ∧ xs.length≤(W.array a).length ∧ (W.array a).take (W.scalar n)=xs)
    (fun _ W => W.array .output=xs) stage (by
      intro W h _ B
      let P := Ports.target (sliceScalar n) (sliceArray a) W
      have hlen : P.scalar .length=xs.length := h.1
      have hoff : P.scalar .offset=0 := rfl
      have hin : P.array .input=W.array a := rfl
      obtain ⟨k,hk,Y,rY,hY,hy⟩ := ArraySlice.program_runs P M B one (by rw [hoff,hlen,hin,Nat.zero_add];exact h.2.1)
      rw [hlen] at hk
      rw [hlen,hoff,hin,take_as_table _ _ h.2.1,←h.1,h.2.2] at hy
      exact ⟨k,hk,Y,rY,hY,hy⟩)
  exact ⟨j,hj,T,run,hT,hw⟩

abbrev EReg := SourceNeighbors.Reg⊕ArraySlice.Reg
abbrev EArr := SourceNeighbors.Arr⊕ArraySlice.Arr
abbrev PReg := PairIndices.Reg⊕ArraySlice.Reg
abbrev PArr := PairIndices.Arr⊕ArraySlice.Arr
abbrev Reg := EReg⊕PReg
abbrev Arr := EArr⊕PArr
abbrev State := Store Reg Arr
noncomputable def edges := trim RangeSelection.program SourceNeighbors.Reg.count SourceNeighbors.Arr.output
noncomputable def pairs := trim PairIndices.program (.inr SourceNeighbors.Reg.count) (.inr SourceNeighbors.Arr.output)
noncomputable def program : NatArrayLanguage.Program Reg Arr :=
  .seq (edges.map Sum.inl Sum.inl) (pairs.map Sum.inr Sum.inr)

def edgePort : Arr := .inl (.inr .output)
def pairPort : Arr := .inr (.inr .output)
def time (sc q : ℕ) := trimCost (sc*9+10) sc+trimCost (q*q*15+18) (q*q)

theorem program_runs (xs : List ℕ) (q M : ℕ) (S : State) (bounded : S.Bounded M) (hq : 0<q)
    (one : 1≤M) (room : q*q≤M)
    (input : S.left.left.array .input=xs) (frames : S.right.left.left.scalar .frames=q) :
    ∃t≤time xs.length q,∃T,Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array edgePort=RangeSelection.selected xs ∧ T.array pairPort=FramePairEncoding.word q := by
  let es := RangeSelection.selected xs
  let ps := FramePairEncoding.word q
  have he : es.length≤xs.length := SourceNeighbors.selected_length_le _ _ _ _
  have hp : ps.length≤q*q := by rw [show ps=SourceNeighbors.selected (PairFlags.flags q) 1 0 (q*q) from FramePairEncoding.word_selected q];exact SourceNeighbors.selected_length_le _ _ _ _
  have pword : RangeSelection.selected (PairFlags.flags q)=ps := by
    rw [show ps=SourceNeighbors.selected (PairFlags.flags q) 1 0 (q*q) from FramePairEncoding.word_selected q]
    simp [RangeSelection.selected,PairFlags.flags]
  obtain ⟨i,hi,U,eRun,hU,edgesOut⟩ := trim_runs RangeSelection.program SourceNeighbors.Reg.count SourceNeighbors.Arr.output
    M (xs.length*9+10) S.left bounded.left one es (by
      obtain ⟨k,hk,T,run,B,_,hc,hl,hw⟩ := RangeSelection.program_runs xs M one S.left.left bounded.left.left input
      exact ⟨k,hk,T,run,B,hc,hl ▸ he,hw⟩)
  obtain ⟨j,hj,W,pRun,hW,pairsOut⟩ := trim_runs PairIndices.program (.inr SourceNeighbors.Reg.count) (.inr SourceNeighbors.Arr.output)
    M (q*q*15+18) S.right bounded.right one ps (by
      obtain ⟨k,hk,T,run,B,hc,hl,hw⟩ := PairIndices.program_runs q M hq one room S.right.left bounded.right.left frames
      rw [pword] at hc hw
      exact ⟨k,hk,T,run,B,hc,hl ▸ hp,hw⟩)
  exact ⟨i+j,by unfold time trimCost at *;omega,U.join W,
    (eRun.left_bounded bounded).seq (pRun.right_bounded (S:=U.join S.right) (hU.join bounded.right)),hU.join hW,edgesOut,pairsOut⟩

end GroupWL.MachinePrograms.IncidencePipeline.Indices
