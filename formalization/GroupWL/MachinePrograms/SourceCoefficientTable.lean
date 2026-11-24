import GroupWL.MachinePrograms.SourceCoefficients
import GroupWL.MachinePrograms.NatArrayComponents
import GroupWL.MachinePrograms.ArrayMaterialization

/-! A complete rectangular materialization loop for the two padded source
coefficients at every block/readout pair. -/
namespace GroupWL.MachinePrograms.SourceCoefficientTable

open NatArrayLanguage
set_option maxHeartbeats 1200000

inductive Admin where
  | total | position | remaining | one | zero | two | readouts | quotient
  deriving DecidableEq, Fintype
abbrev Reg := SourceCoefficients.Reg ⊕ Admin
abbrev Arr := SourceCoefficients.Arr ⊕ Unit
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def loopRegisters : Fin 5 ↪ Reg :=
  ⟨![.inr .total,.inr .position,.inr .remaining,.inr .one,.inr .zero],by decide⟩

def decodeAtoms : List (Atom Reg Arr) := [
  .divmod (.inr .quotient) (.inl .coordinate) (.inr .position) (.inr .two),
  .divmod (.inl .block) (.inl .readout) (.inr .quotient) (.inr .readouts)]

def cell : Code := .seq (atoms decodeAtoms) (SourceCoefficients.program.map Sum.inl Sum.inl)

def program : Code := materialize loopRegisters (.inr ()) (.inl .result) cell

def sourceState (data : SourceCoefficients.Arr → List ℕ) (h p b j k : ℕ) : SourceCoefficients.State where
  scalar
    | .horizontal => h | .modulus => p | .block => b | .readout => j | .coordinate => k
    | _ => 0
  array := data

def tableEntry (data : SourceCoefficients.Arr → List ℕ) (h p r i : ℕ) : ℕ :=
  SourceCoefficients.coefficient (sourceState data h p (i/2/r) (i/2%r) (i%2))

def Ready (data : SourceCoefficients.Arr → List ℕ) (h p b r : ℕ) (S : State) : Prop :=
  S.left.array = data ∧ S.scalar (.inl .horizontal) = h ∧ S.scalar (.inl .modulus) = p ∧
    S.scalar (.inr .readouts) = r ∧ S.scalar (.inr .two) = 2 ∧ S.scalar (.inr .total) = b*r*2

def RecordsValid (data : SourceCoefficients.Arr → List ℕ) (h p b : ℕ) : Prop :=
  0 < p ∧ h ≤ b ∧
    (∀ a : SourceCoefficients.Arr, a ≠ .leftForm → a ≠ .rightForm → b-h ≤ (data a).length) ∧
    (∀ a : SourceCoefficients.Arr, a = .leftForm ∨ a = .rightForm →
      2*(b-h) ≤ (data a).length ∧ ∀ i < 2*(b-h), (data a)[i]?.getD 0 < p)

theorem cell_runs (data : SourceCoefficients.Arr → List ℕ) (h p b r M : ℕ)
    (hr : 0 < r) (hM : 6*p+4 ≤ M) (valid : RecordsValid data h p b)
    (S : State) (ready : Ready data h p b r S) (bounded : S.Bounded M)
    (hi : S.scalar (.inr .position) < b*r*2) :
    ∃ t ≤ 30, ∃ T, Runs (storageBound Reg Arr M) cell S t T ∧ T.Bounded M ∧
      Ready data h p b r T ∧ T.scalar (.inl .result) = tableEntry data h p r (S.scalar (.inr .position)) ∧
      T.array (.inr ()) = S.array (.inr ()) ∧
      ∀ i : Fin 4, T.scalar (loopRegisters i.castSucc) = S.scalar (loopRegisters i.castSucc) := by
  rcases ready with ⟨hdata,hh,hp,hread,htwo,htotal⟩
  have hv : ValidAtoms M decodeAtoms S := by
    simp [decodeAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,hread,htwo,hr]
  obtain ⟨hdecode,hDB⟩ := atoms_runs bounded decodeAtoms hv
  let D := applyAtoms decodeAtoms S
  have hDdata : D.left.array = data := hdata
  have hDh : D.left.scalar .horizontal = h := by
    simpa [D,decodeAtoms,applyAtoms,Atom.apply,Store.setScalar,Store.left] using hh
  have hDp : D.left.scalar .modulus = p := by
    simpa [D,decodeAtoms,applyAtoms,Atom.apply,Store.setScalar,Store.left] using hp
  have hDb : D.left.scalar .block = S.scalar (.inr .position)/2/r := by
    simp [D,decodeAtoms,applyAtoms,Atom.apply,Store.setScalar,Store.left,hread,htwo]
  have hDj : D.left.scalar .readout = S.scalar (.inr .position)/2%r := by
    simp [D,decodeAtoms,applyAtoms,Atom.apply,Store.setScalar,Store.left,hread,htwo]
  have hDk : D.left.scalar .coordinate = S.scalar (.inr .position)%2 := by
    simp [D,decodeAtoms,applyAtoms,Atom.apply,Store.setScalar,Store.left,htwo]
  have hb : D.left.scalar .block < b := by
    rw [hDb]
    apply (Nat.div_lt_iff_lt_mul hr).2
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
    exact hi
  have hk : D.left.scalar .coordinate < 2 := by rw [hDk]; exact Nat.mod_lt _ (by decide)
  have hvalid : D.left.scalar .horizontal ≤ D.left.scalar .block → SourceCoefficients.SquareValid D.left := by
    intro hsite
    have hs : D.left.scalar .block-h < b-h := by omega
    have hidx : 2*(D.left.scalar .block-h)+D.left.scalar .coordinate < 2*(b-h) := by omega
    refine ⟨by simpa [hDp] using valid.1,?_,?_⟩
    · intro a ha hb'
      simpa [hDh,hDdata] using hs.trans_le (valid.2.2.1 a ha hb')
    · intro a ha
      have hv := valid.2.2.2 a ha
      refine ⟨?_,?_⟩
      · simpa [hDh,hDdata] using hidx.trans_le hv.1
      · simpa [SourceCoefficients.read,hDh,hDp,hDdata] using hv.2 _ hidx
  obtain ⟨t,ht,hsource,hSB,hvalue⟩ := SourceCoefficients.program_runs D.left M hDB.left
    (by simpa [hDp] using hM) hvalid
  let T := (SourceCoefficients.resultStore D.left).join D.right
  have hrun : Runs (storageBound Reg Arr M) (SourceCoefficients.program.map Sum.inl Sum.inl) D t T := by
    simpa only [Store.join_left_right] using hsource.left_bounded hDB
  have hpersist := SourceCoefficients.resultStore_preserves D.left
  refine ⟨2+t,by omega,T,hdecode.seq hrun,hSB.join hDB.right,?_,?_,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa [T] using hpersist.2.2.2.2.2.trans hDdata
    · exact hpersist.2.1.trans hDh
    · exact hpersist.2.2.2.2.1.trans hDp
    · simpa [T,Store.right,D,decodeAtoms,applyAtoms,Atom.apply,Store.setScalar] using hread
    · simpa [T,Store.right,D,decodeAtoms,applyAtoms,Atom.apply,Store.setScalar] using htwo
    · simpa [T,Store.right,D,decodeAtoms,applyAtoms,Atom.apply,Store.setScalar] using htotal
  · change (SourceCoefficients.resultStore D.left).scalar .result = _
    rw [hvalue]
    simp only [tableEntry,SourceCoefficients.coefficient,SourceCoefficients.read,
      sourceState,hDh,hDp,hDb,hDj,hDk,hDdata]
  · rfl
  · intro i
    fin_cases i <;> simp [T,loopRegisters,Store.right,D,decodeAtoms,applyAtoms,Atom.apply,Store.setScalar]

theorem program_runs (data : SourceCoefficients.Arr → List ℕ) (h p b r M : ℕ)
    (hr : 0 < r) (hM : 6*p+4 ≤ M) (valid : RecordsValid data h p b)
    (S : State) (ready : Ready data h p b r S) (bounded : S.Bounded M) :
    ∃ t ≤ b*r*2*34+6, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧
      T.Bounded M ∧ Ready data h p b r T ∧
      T.array (.inr ()) = List.ofFn (fun i : Fin (b*r*2) => tableEntry data h p r i.val) := by
  apply materialize_runs loopRegisters (.inr ()) (.inl .result) cell
    (Ready data h p b r) (tableEntry data h p r) M (b*r*2) 30 (by omega)
  · intro T hT i v
    fin_cases i <;> simpa [Ready,loopRegisters,Store.setScalar,Store.left] using hT
  · intro T hT xs
    simpa [Ready,Store.setArray,Store.left] using hT
  · exact fun T hT hb hi => cell_runs data h p b r M hr hM valid T hT hb hi
  · exact bounded
  · exact ready
  · exact ready.2.2.2.2.2

end GroupWL.MachinePrograms.SourceCoefficientTable
