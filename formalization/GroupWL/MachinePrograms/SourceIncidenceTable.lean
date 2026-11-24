import GroupWL.MachinePrograms.SourceIncidence
import GroupWL.MachinePrograms.NatArrayComponents
import GroupWL.MachinePrograms.ArrayMaterialization

/-! Materialized source incidence, independent of the coefficient values. -/
namespace GroupWL.MachinePrograms.SourceIncidenceTable

open NatArrayLanguage

inductive Admin where
  | total | position | remaining | one | zero | readouts
  deriving DecidableEq, Fintype
abbrev Reg := SourceIncidence.Reg ⊕ Admin
abbrev Arr := SourceIncidence.Arr ⊕ Unit
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def loopRegisters : Fin 5 ↪ Reg :=
  ⟨![.inr .total,.inr .position,.inr .remaining,.inr .one,.inr .zero],by decide⟩

def decode : Atom Reg Arr :=
  .divmod (.inl .block) (.inl .readout) (.inr .position) (.inr .readouts)

def cell : Code := .seq (.atom decode) (SourceIncidence.program.map Sum.inl Sum.inl)

def program : Code := materialize loopRegisters (.inr ()) (.inl .result) cell

def sourceState (data : SourceIncidence.Arr → List ℕ) (h b j : ℕ) : SourceIncidence.State where
  scalar
    | .horizontal => h | .block => b | .readout => j
    | _ => 0
  array := data

def tableEntry (data : SourceIncidence.Arr → List ℕ) (h r i : ℕ) : ℕ :=
  SourceIncidence.incidence (sourceState data h (i/r) (i%r))

def Ready (data : SourceIncidence.Arr → List ℕ) (h b r : ℕ) (S : State) : Prop :=
  S.left.array = data ∧ S.scalar (.inl .horizontal) = h ∧
    S.scalar (.inr .readouts) = r ∧ S.scalar (.inr .total) = b*r

def RecordsValid (data : SourceIncidence.Arr → List ℕ) (h b : ℕ) : Prop :=
  h ≤ b ∧ ∀ a : SourceIncidence.Arr, b-h ≤ (data a).length

theorem cell_runs (data : SourceIncidence.Arr → List ℕ) (h b r M : ℕ)
    (hr : 0 < r) (hM : 4 ≤ M) (valid : RecordsValid data h b)
    (S : State) (ready : Ready data h b r S) (bounded : S.Bounded M)
    (hi : S.scalar (.inr .position) < b*r) :
    ∃ t ≤ 17, ∃ T, Runs (storageBound Reg Arr M) cell S t T ∧ T.Bounded M ∧
      Ready data h b r T ∧ T.scalar (.inl .result) = tableEntry data h r (S.scalar (.inr .position)) ∧
      T.array (.inr ()) = S.array (.inr ()) ∧
      ∀ i : Fin 4, T.scalar (loopRegisters i.castSucc) = S.scalar (loopRegisters i.castSucc) := by
  rcases ready with ⟨hdata,hh,hread,htotal⟩
  have hv : decode.Valid S := by simp [decode,Atom.Valid,hread,hr]
  have hdecode := atom_runs bounded decode hv trivial
  have hDB := Atom.apply_bounded bounded decode trivial
  let D := decode.apply S
  have hDdata : D.left.array = data := hdata
  have hDh : D.left.scalar .horizontal = h := by
    simpa [D,decode,Atom.apply,Store.setScalar,Store.left] using hh
  have hDb : D.left.scalar .block = S.scalar (.inr .position)/r := by
    simp [D,decode,Atom.apply,Store.setScalar,Store.left,hread]
  have hDj : D.left.scalar .readout = S.scalar (.inr .position)%r := by
    simp [D,decode,Atom.apply,Store.setScalar,Store.left,hread]
  have hb : D.left.scalar .block < b := by
    rw [hDb]
    exact (Nat.div_lt_iff_lt_mul hr).2 hi
  have hvalid : D.left.scalar .horizontal ≤ D.left.scalar .block →
      ∀ a, D.left.scalar .block-D.left.scalar .horizontal < (D.left.array a).length := by
    intro hsite a
    have hs : D.left.scalar .block-h < b-h := by omega
    simpa [hDh,hDdata] using hs.trans_le (valid.2 a)
  obtain ⟨t,ht,hsource,hSB,hvalue⟩ := SourceIncidence.program_runs D.left M hDB.left hM hvalid
  let T := (SourceIncidence.resultStore D.left).join D.right
  have hrun : Runs (storageBound Reg Arr M) (SourceIncidence.program.map Sum.inl Sum.inl) D t T := by
    simpa only [Store.join_left_right] using hsource.left_bounded hDB
  have hpersist := SourceIncidence.resultStore_preserves D.left
  refine ⟨1+t,by omega,T,hdecode.seq hrun,hSB.join hDB.right,?_,?_,?_,?_⟩
  · refine ⟨?_,?_,?_,?_⟩
    · simpa [T] using hpersist.2.2.2.trans hDdata
    · exact hpersist.2.1.trans hDh
    · simpa [T,Store.right,D,decode,Atom.apply,Store.setScalar] using hread
    · simpa [T,Store.right,D,decode,Atom.apply,Store.setScalar] using htotal
  · change (SourceIncidence.resultStore D.left).scalar .result = _
    rw [hvalue]
    simp only [tableEntry,SourceIncidence.incidence,SourceIncidence.read,sourceState,hDh,hDb,hDj,hDdata]
    split_ifs <;> rfl
  · rfl
  · intro i
    fin_cases i <;> simp [T,loopRegisters,Store.right,D,decode,Atom.apply,Store.setScalar]

theorem program_runs (data : SourceIncidence.Arr → List ℕ) (h b r M : ℕ)
    (hr : 0 < r) (hM : 4 ≤ M) (valid : RecordsValid data h b)
    (S : State) (ready : Ready data h b r S) (bounded : S.Bounded M) :
    ∃ t ≤ b*r*21+6, ∃ T, Runs (storageBound Reg Arr M) program S t T ∧
      T.Bounded M ∧ Ready data h b r T ∧
      T.array (.inr ()) = List.ofFn (fun i : Fin (b*r) => tableEntry data h r i.val) := by
  apply materialize_runs loopRegisters (.inr ()) (.inl .result) cell
    (Ready data h b r) (tableEntry data h r) M (b*r) 17 (by omega)
  · intro T hT i v
    fin_cases i <;> simpa [Ready,loopRegisters,Store.setScalar,Store.left] using hT
  · intro T hT xs
    simpa [Ready,Store.setArray,Store.left] using hT
  · exact fun T hT hb hi => cell_runs data h b r M hr hM valid T hT hb hi
  · exact bounded
  · exact ready
  · exact ready.2.2.2

end GroupWL.MachinePrograms.SourceIncidenceTable
