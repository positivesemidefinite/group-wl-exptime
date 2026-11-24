import GroupWL.MachinePrograms.NatArrayEncoding
import GroupWL.MachinePrograms.ArrayMetadata

/-! Concrete materialized-array instructions for the finite-register compiler. -/
namespace GroupWL.MachinePrograms.NatArrayLowering

open NatArrayLanguage
open Structured

variable {Reg Arr : Type*} [DecidableEq Reg] [DecidableEq Arr] [Fintype Reg] [Fintype Arr]

def readSlots (a : Arr) : Fin 5 ↪ StackIndex Reg Arr where
  toFun := ![scratchSlot 0, arraySlot a, scratchSlot 1, scratchSlot 2, scratchSlot 15]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [scratchSlot, arraySlot]

def readBody (r : Reg) (a : Arr) (i : Reg) : Structured.Program (StackIndex Reg Arr) :=
  .seq (copy (scalarSlot i) (scratchSlot 0) (scratchSlot 15))
    (.seq (arrayRead (readSlots a))
      (.seq (clear (scalarSlot r)) (transfer (scratchSlot 1) (scalarSlot r))))

def readCode (r : Reg) (a : Arr) (i : Reg) : BodyCode (.read r a i) where
  body := readBody r a i
  correct := by
    intro S B valid before after
    let v := ((S.array a)[S.scalar i]?).getD 0
    let T₀ := encodeStore S
    let T₁ := Function.update T₀ (scratchSlot 0) (List.replicate (S.scalar i) true)
    let T₂ := Function.update (Function.update T₁ (scratchSlot 0) [])
      (scratchSlot 1) (List.replicate v true)
    let T₃ := Function.update T₂ (scalarSlot r) []
    let T₄ := Function.update (Function.update T₃ (scratchSlot 1) [])
      (scalarSlot r) (List.replicate v true)
    have h1 : Structured.Runs (copy (scalarSlot i) (scratchSlot 0) (scratchSlot 15))
        T₀ (7*S.scalar i+2) T₁ := by
      simpa [T₀, T₁] using copy_runs T₀ (scalarSlot i) (scratchSlot 0) (scratchSlot 15)
        (by simp) (by simp) (by simp) (by simp [T₀])
    obtain ⟨tr, htr, h2⟩ := arrayRead_index (readSlots (Reg := Reg) a) T₁ (S.array a) (S.scalar i)
      valid (by simp [readSlots, T₁]) (by simp [readSlots, T₁, T₀])
      (by simp [readSlots, T₁, T₀]) (by simp [readSlots, T₁, T₀]) (by simp [readSlots, T₁, T₀])
    change Structured.Runs (arrayRead (readSlots a)) T₁ tr T₂ at h2
    have hold : T₂ (scalarSlot r) = List.replicate (S.scalar r) true := by simp [T₂, T₁, T₀]
    have h3 : Structured.Runs (clear (scalarSlot r)) T₂ (2*S.scalar r+1) T₃ := by
      simpa [T₃, hold] using clear_runs T₂ (scalarSlot r)
    have hv : T₃ (scratchSlot 1) = List.replicate v true := by simp [T₃, T₂]
    have hz : T₃ (scalarSlot r) = [] := by simp [T₃]
    have h4 : Structured.Runs (transfer (scratchSlot 1) (scalarSlot r)) T₃ (3*v+1) T₄ := by
      simpa [T₄, hv, hz] using transfer_runs T₃ (scratchSlot 1) (scalarSlot r) (by simp)
    have he1 : DataEncoded S T₁ := (dataEncoded_encodeStore S).update_scratch 0 _
    have he2 : DataEncoded S T₂ := (he1.update_scratch 0 []).update_scratch 1 _
    have he3 : DataEncoded (S.setScalar r 0) T₃ := he2.update_scalar r 0
    have he4 := (he3.update_scratch 1 []).update_scalar r v
    have hvB : v ≤ B := by
      have hb : v ≤ ((Atom.read r a i).apply S).size := by
        simpa [Atom.apply, Store.setScalar, v] using
          Store.scalar_le_size ((Atom.read r a i).apply S) r
      exact hb.trans after
    have hiB := (S.scalar_le_size i).trans before
    have hrB := (S.scalar_le_size r).trans before
    have hlB := (S.array_length_le_size a).trans before
    have hsB := (S.array_sum_le_size a).trans before
    simp only [arrayWord_length] at htr
    refine ⟨7*S.scalar i+2+(tr+(2*S.scalar r+1+(3*v+1))), ?_, T₄, ?_, ?_⟩
    · apply le_trans (b := 100*(B+1)) ?_ (bodyBudget_ge_linear B)
      omega
    · exact Structured.Runs.seq h1 (Structured.Runs.seq h2 (Structured.Runs.seq h3 h4))
    · simpa [Atom.apply, Store.setScalar, Function.update_idem, T₄, v] using he4

def clearArrayCode (a : Arr) : BodyCode (.clearArray (Reg := Reg) a) where
  body := clear (arraySlot a)
  correct := by
    intro S B valid before after
    refine ⟨2*(arrayWord (S.array a)).length+1, ?_,
      Function.update (encodeStore S) (arraySlot a) [], ?_, ?_⟩
    · have hl := (S.array_length_le_size a).trans before
      have hs := (S.array_sum_le_size a).trans before
      apply le_trans (b := 100*(B+1)) ?_ (bodyBudget_ge_linear B)
      simp only [arrayWord_length]
      omega
    · simpa using clear_runs (encodeStore S) (arraySlot a)
    · exact (dataEncoded_encodeStore S).update_array a []

def copyArrayCode (a b : Arr) : BodyCode (.copyArray (Reg := Reg) a b) := by
  by_cases hab : a = b
  · subst b
    refine ⟨.skip, ?_⟩
    intro S B valid before after
    refine ⟨0, Nat.zero_le _, encodeStore S, Structured.Runs.skip _, ?_⟩
    simpa [Atom.apply, Store.setArray, Function.update_eq_self] using dataEncoded_encodeStore S
  · refine ⟨.seq (clear (arraySlot a)) (copy (arraySlot b) (arraySlot a) (scratchSlot 15)), ?_⟩
    intro S B valid before after
    let T := Function.update (encodeStore S) (arraySlot a) []
    have h1 : Structured.Runs (clear (arraySlot a)) (encodeStore S)
        (2*(arrayWord (S.array a)).length+1) T := by
      simpa [T] using clear_runs (encodeStore S) (arraySlot a)
    have hb : T (arraySlot b) = arrayWord (S.array b) := by simp [T, Ne.symm hab]
    have ha : T (arraySlot a) = [] := by simp [T]
    have ht : T (scratchSlot 15) = [] := by simp [T]
    have h2 := copy_runs T (arraySlot b) (arraySlot a) (scratchSlot 15)
      (by simpa using Ne.symm hab) (by simp) (by simp) ht
    rw [hb, ha, List.append_nil] at h2
    have hend : Function.update T (arraySlot a) (arrayWord (S.array b)) =
        Function.update (encodeStore S) (arraySlot a) (arrayWord (S.array b)) := by
      simp [T, Function.update_idem]
    rw [hend] at h2
    refine ⟨2*(arrayWord (S.array a)).length+1+(7*(arrayWord (S.array b)).length+2), ?_,
      Function.update (encodeStore S) (arraySlot a) (arrayWord (S.array b)),
      Structured.Runs.seq h1 h2, (dataEncoded_encodeStore S).update_array a (S.array b)⟩
    have ha₁ := (S.array_length_le_size a).trans before
    have ha₂ := (S.array_sum_le_size a).trans before
    have hb₁ := (S.array_length_le_size b).trans before
    have hb₂ := (S.array_sum_le_size b).trans before
    apply le_trans (b := 100*(B+1)) ?_ (bodyBudget_ge_linear B)
    simp only [arrayWord_length]
    omega

def writeBody (a : Arr) (i v : Reg) : Structured.Program (StackIndex Reg Arr) :=
  .seq (copy (scalarSlot i) (scratchSlot 0) (scratchSlot 15))
    (.seq (copy (scalarSlot v) (scratchSlot 1) (scratchSlot 15)) (arrayWrite (readSlots a)))

def writeCode (a : Arr) (i v : Reg) : BodyCode (.write a i v) where
  body := writeBody a i v
  correct := by
    intro S B valid before after
    let T₀ := encodeStore S
    let T₁ := Function.update T₀ (scratchSlot 0) (List.replicate (S.scalar i) true)
    let T₂ := Function.update T₁ (scratchSlot 1) (List.replicate (S.scalar v) true)
    have h1 : Structured.Runs (copy (scalarSlot i) (scratchSlot 0) (scratchSlot 15))
        T₀ (7*S.scalar i+2) T₁ := by
      simpa [T₀,T₁] using copy_runs T₀ (scalarSlot i) (scratchSlot 0) (scratchSlot 15)
        (by simp) (by simp) (by simp) (by simp [T₀])
    have h2 : Structured.Runs (copy (scalarSlot v) (scratchSlot 1) (scratchSlot 15))
        T₁ (7*S.scalar v+2) T₂ := by
      simpa [T₀,T₁,T₂] using copy_runs T₁ (scalarSlot v) (scratchSlot 1) (scratchSlot 15)
        (by simp) (by simp) (by simp) (by simp [T₀,T₁])
    obtain ⟨tw, htw, hw⟩ := arrayWrite_index (readSlots (Reg := Reg) a) T₂
      (S.array a) (S.scalar i) (S.scalar v) valid
      (by simp [readSlots,T₂,T₁]) (by simp [readSlots,T₂,T₁,T₀])
      (by simp [readSlots,T₂]) (by simp [readSlots,T₂,T₁,T₀]) (by simp [readSlots,T₂,T₁,T₀])
    have he2 : DataEncoded S T₂ := ((dataEncoded_encodeStore S).update_scratch 0 _).update_scratch 1 _
    refine ⟨7*S.scalar i+2+(7*S.scalar v+2+tw), ?_, _,
      Structured.Runs.seq h1 (Structured.Runs.seq h2 hw), ?_⟩
    · have hiB := (S.scalar_le_size i).trans before
      have hvB := (S.scalar_le_size v).trans before
      have hlB := (S.array_length_le_size a).trans before
      have hsB := (S.array_sum_le_size a).trans before
      simp only [arrayWord_length] at htw
      apply le_trans (b := 100*(B+1)) ?_ (bodyBudget_ge_linear B)
      omega
    · exact (he2.update_scratch 0 []).update_array a _

def lengthSlots (a : Arr) : Fin 3 ↪ StackIndex Reg Arr where
  toFun := ![arraySlot a, scratchSlot 0, scratchSlot 15]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [scratchSlot,arraySlot]

def lengthBody (r : Reg) (a : Arr) : Structured.Program (StackIndex Reg Arr) :=
  .seq (arrayLength (lengthSlots a))
    (.seq (clear (scalarSlot r)) (transfer (scratchSlot 0) (scalarSlot r)))

def arrayLengthCode (r : Reg) (a : Arr) : BodyCode (.arrayLength r a) where
  body := lengthBody r a
  correct := by
    intro S B valid before after
    let n := (S.array a).length
    let T₀ := encodeStore S
    let T₁ := Function.update T₀ (scratchSlot 0) (List.replicate n true)
    let T₂ := Function.update T₁ (scalarSlot r) []
    let T₃ := Function.update (Function.update T₂ (scratchSlot 0) [])
      (scalarSlot r) (List.replicate n true)
    have h1 : Structured.Runs (arrayLength (lengthSlots a)) T₀
        (6*(S.array a).sum+8*(S.array a).length+2) T₁ := by
      simpa [lengthSlots,T₀,T₁,n] using arrayLength_runs (lengthSlots (Reg := Reg) a)
        (S.array a) T₀ (by simp [lengthSlots,T₀]) (by simp [lengthSlots,T₀])
        (by simp [lengthSlots,T₀])
    have hold : T₁ (scalarSlot r) = List.replicate (S.scalar r) true := by simp [T₁,T₀]
    have h2 : Structured.Runs (clear (scalarSlot r)) T₁ (2*S.scalar r+1) T₂ := by
      simpa [T₂,hold] using clear_runs T₁ (scalarSlot r)
    have hn : T₂ (scratchSlot 0) = List.replicate n true := by simp [T₂,T₁]
    have hz : T₂ (scalarSlot r) = [] := by simp [T₂]
    have h3 : Structured.Runs (transfer (scratchSlot 0) (scalarSlot r)) T₂ (3*n+1) T₃ := by
      simpa [T₃,hn,hz] using transfer_runs T₂ (scratchSlot 0) (scalarSlot r) (by simp)
    have he1 : DataEncoded S T₁ := (dataEncoded_encodeStore S).update_scratch 0 _
    have he2 : DataEncoded (S.setScalar r 0) T₂ := he1.update_scalar r 0
    have he3 := (he2.update_scratch 0 []).update_scalar r n
    refine ⟨6*(S.array a).sum+8*(S.array a).length+2+(2*S.scalar r+1+(3*n+1)), ?_,
      T₃, Structured.Runs.seq h1 (Structured.Runs.seq h2 h3), ?_⟩
    · have hrB := (S.scalar_le_size r).trans before
      have hlB := (S.array_length_le_size a).trans before
      have hsB := (S.array_sum_le_size a).trans before
      apply le_trans (b := 100*(B+1)) ?_ (bodyBudget_ge_linear B)
      dsimp only [n]
      omega
    · simpa [Atom.apply,Store.setScalar,Function.update_idem,T₃,n] using he3

def allocateSlots (a : Arr) : Fin 5 ↪ StackIndex Reg Arr where
  toFun := ![scratchSlot 0, scratchSlot 1, arraySlot a, scratchSlot 2, scratchSlot 15]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [scratchSlot,arraySlot]

def allocateBody (a : Arr) (n v : Reg) : Structured.Program (StackIndex Reg Arr) :=
  .seq (copy (scalarSlot n) (scratchSlot 0) (scratchSlot 15))
    (.seq (copy (scalarSlot v) (scratchSlot 1) (scratchSlot 15))
      (.seq (clear (arraySlot a)) (allocateArray (allocateSlots a))))

def allocateCode (a : Arr) (n v : Reg) : BodyCode (.allocate a n v) where
  body := allocateBody a n v
  correct := by
    intro S B valid before after
    let T₀ := encodeStore S
    let T₁ := Function.update T₀ (scratchSlot 0) (List.replicate (S.scalar n) true)
    let T₂ := Function.update T₁ (scratchSlot 1) (List.replicate (S.scalar v) true)
    let T₃ := Function.update T₂ (arraySlot a) []
    let T₄ := Function.update T₃ (arraySlot a)
      (arrayWord (List.replicate (S.scalar n) (S.scalar v)))
    have h1 : Structured.Runs (copy (scalarSlot n) (scratchSlot 0) (scratchSlot 15))
        T₀ (7*S.scalar n+2) T₁ := by
      simpa [T₀,T₁] using copy_runs T₀ (scalarSlot n) (scratchSlot 0) (scratchSlot 15)
        (by simp) (by simp) (by simp) (by simp [T₀])
    have h2 : Structured.Runs (copy (scalarSlot v) (scratchSlot 1) (scratchSlot 15))
        T₁ (7*S.scalar v+2) T₂ := by
      simpa [T₀,T₁,T₂] using copy_runs T₁ (scalarSlot v) (scratchSlot 1) (scratchSlot 15)
        (by simp) (by simp) (by simp) (by simp [T₀,T₁])
    have ha2 : T₂ (arraySlot a) = arrayWord (S.array a) := by simp [T₂,T₁,T₀]
    have h3 : Structured.Runs (clear (arraySlot a)) T₂ (2*(arrayWord (S.array a)).length+1) T₃ := by
      simpa [T₃,ha2] using clear_runs T₂ (arraySlot a)
    have h4 : Structured.Runs (allocateArray (allocateSlots a)) T₃
        (7*S.scalar n*S.scalar v+12*S.scalar n+3) T₄ := by
      simpa [allocateSlots,T₄] using allocateArray_runs (allocateSlots (Reg := Reg) a)
        (S.scalar n) (S.scalar v) T₃
        (by simp [allocateSlots,T₃,T₂,T₁,unary]) (by simp [allocateSlots,T₃,T₂,unary])
        (by simp [allocateSlots,T₃]) (by simp [allocateSlots,T₃,T₂,T₁,T₀])
        (by simp [allocateSlots,T₃,T₂,T₁,T₀])
    have he2 : DataEncoded S T₂ := ((dataEncoded_encodeStore S).update_scratch 0 _).update_scratch 1 _
    have he3 : DataEncoded (S.setArray a []) T₃ := he2.update_array a []
    have he4 := he3.update_array a (List.replicate (S.scalar n) (S.scalar v))
    refine ⟨7*S.scalar n+2+(7*S.scalar v+2+(2*(arrayWord (S.array a)).length+1+
      (7*S.scalar n*S.scalar v+12*S.scalar n+3))), ?_, T₄,
      Structured.Runs.seq h1 (Structured.Runs.seq h2 (Structured.Runs.seq h3 h4)), ?_⟩
    · have hnB := (S.scalar_le_size n).trans before
      have hvB := (S.scalar_le_size v).trans before
      have hlB := (S.array_length_le_size a).trans before
      have hsB := (S.array_sum_le_size a).trans before
      have hpB : S.scalar n*S.scalar v ≤ B := by
        have hb := Store.array_sum_le_size ((Atom.allocate a n v).apply S) a
        have he : S.scalar n*S.scalar v ≤ ((Atom.allocate a n v).apply S).size := by
          simpa [Atom.apply,Store.setArray,List.sum_replicate] using hb
        exact he.trans after
      apply le_trans (b := 100*(B+1)) ?_ (bodyBudget_ge_linear B)
      simp only [arrayWord_length]
      nlinarith
    · simpa [Atom.apply,Store.setArray,Function.update_idem,T₄] using he4

end GroupWL.MachinePrograms.NatArrayLowering
