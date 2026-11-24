import GroupWL.MachinePrograms.CircuitRecordPipelineBase

/-! The complete circuit-word-to-comparison-tables array program. -/
namespace GroupWL.MachinePrograms.CircuitRecordPipeline.Metadata
open NatArrayLanguage CircuitMetadataValues CircuitDescription AddressedCircuit
open CircuitMetadataExpressions (Field Input)
open NatArrayLowering (bitNat)
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

abbrev RawReg := Decode.Reg ⊕ BaseReg
abbrev RawArr := Decode.Arr ⊕ Input
noncomputable def counts : NatArrayLanguage.Program RawReg RawArr :=
  Ports.thenRun Decode.program rawScalar (some ∘ rawArr) (atoms countAtoms)

def countsTime (n s : ℕ) := Decode.time n s + (Fintype.card BaseReg+Fintype.card Input+16)

def fields : List Field := [.dimension,.source,.target,.sourceForm,.targetForm,.domain,.permutation]

def fromBaseReg : (fs : List Field) → CircuitRecordPipeline.Reg fs → Option BaseReg
  | [], r => some r
  | _ :: fs, .inl r => fromBaseReg fs r
  | _ :: _, .inr _ => none

def fromBaseArray : (fs : List Field) → CircuitRecordPipeline.Arr fs → Option Input
  | [], a => some a
  | _ :: fs, .inl a => fromBaseArray fs a
  | _ :: _, .inr _ => none

@[simp] theorem fromBaseReg_baseReg (fs : List Field) (r : BaseReg) : fromBaseReg fs (baseReg fs r)=some r := by
  induction fs <;> simp [fromBaseReg,baseReg, *]
@[simp] theorem fromBaseArray_baseArray (fs : List Field) (a : Input) : fromBaseArray fs (baseArray fs a)=some a := by
  induction fs <;> simp [fromBaseArray,baseArray, *]

def scalarPort (fs : List Field) (r : CircuitRecordPipeline.Reg fs) : Ports.Scalar RawReg RawArr :=
  match fromBaseReg fs r with | some b => .scalar (.inr b) | none => .literal 0

def arrayPort (fs : List Field) (a : CircuitRecordPipeline.Arr fs) : Option RawArr :=
  (fromBaseArray fs a).map Sum.inr

abbrev Reg := RawReg ⊕ CircuitRecordPipeline.Reg fields
abbrev Arr := RawArr ⊕ CircuitRecordPipeline.Arr fields
noncomputable def program : NatArrayLanguage.Program Reg Arr :=
  Ports.thenRun counts (scalarPort fields) (arrayPort fields) (tables fields)

abbrev inputArray : Arr := .inl (.inl Decode.inputArray)
abbrev arity : Reg := .inl (.inr (.inl .coordinates))
abbrev typeCount : Reg := .inl (.inr (.inr .dimension))
abbrev comparisonCount : Reg := .inl (.inr (.inr .source))
def output (f : Field) : Arr := .inr (outputArray f fields)

noncomputable def time (n s b : ℕ) := countsTime n s + (Fintype.card (CircuitRecordPipeline.Reg fields)+Fintype.card (CircuitRecordPipeline.Arr fields)+tableTime b fields)

variable {T : Type} [FiniteCode T] {r : ℕ}
structure Output (C : Circuit T r) (S : Store Reg Arr) : Prop where
  coordinates : S.scalar arity=r
  types : S.scalar typeCount=(ofCircuit C).realTypes
  comparisons : S.scalar comparisonCount=(ofCircuit C).comparisons
  arrays : ∀ f,S.array (output f)=tableWord (ofCircuit C).table f

theorem bounded_mono {R A : Type} {S : Store R A} {a b : ℕ} (h : S.Bounded a) (hab : a≤b) : S.Bounded b :=
  ⟨fun i=>(h.1 i).trans hab,fun i=>(h.2.1 i).trans hab,fun i x hx=>(h.2.2 i x hx).trans hab⟩
theorem storage_mono (R A : Type) [Fintype R] [Fintype A] {a b : ℕ} (hab : a≤b) :
    storageBound R A a≤storageBound R A b := by unfold storageBound; gcongr

private theorem countLiteral (u : BaseReg) (k M : ℕ) (h : rawScalar u=.literal k) : k≤M := by
  cases u with
  | inl v=> cases v <;> first | contradiction | cases h;omega
  | inr v=> cases h;omega

theorem counts_runs (C : Circuit T r) (S : Store RawReg RawArr) (B M : ℕ) (hs : S.Bounded B)
    (room : 6≤B) (hparse : 3*(circuitWord C).length+5≤B)
    (size : ∀f,fieldSize (ofCircuit C) f≤B) (budget : ∀f,(B+2)^(2*((CircuitMetadataExpressions.entry f).expression CircuitMetadataExpressions.sizeRegister).cost)≤M)
    (input : S.left.array Decode.inputArray=(circuitWord C).map bitNat) :
    ∃t≤countsTime (circuitWord C).length (FiniteCode.size T),∃U,
      Runs (storageBound RawReg RawArr B) counts S t U ∧ U.Bounded B ∧ Prepared (ofCircuit C) B M U.right := by
  have run := Packed.chain Decode.program rawScalar (some ∘ rawArr) (atoms countAtoms) S B _ 16
    (Decode.Output C) (Prepared (ofCircuit C) B M) hs (fun u k h=>countLiteral u k B h)
    (Decode.program_runs C S.left B hs.left hparse input) ?_
  · obtain ⟨t,ht,U,run,b,_,out⟩ := run
    exact ⟨t,ht,U,run,b,out⟩
  · intro P hp hP
    obtain ⟨run,b,out⟩ := count_runs (ofCircuit C) (raw P) B M hP room (raw_data C hp) (raw_lengths P) size budget
    exact ⟨16,le_rfl,_,run,b,out⟩

theorem program_runs (C : Circuit T r) (S : Store Reg Arr) (B M : ℕ) (hs : S.Bounded B) (hBM : B≤M)
    (room : 6≤B) (hparse : 3*(circuitWord C).length+5≤B)
    (size : ∀f,fieldSize (ofCircuit C) f≤B) (budget : ∀f,(B+2)^(2*((CircuitMetadataExpressions.entry f).expression CircuitMetadataExpressions.sizeRegister).cost)≤M)
    (input : S.array inputArray=(circuitWord C).map bitNat) :
    ∃t≤time (circuitWord C).length (FiniteCode.size T) B,∃U,
      Runs (storageBound Reg Arr M) program S t U ∧ U.Bounded M ∧ Output C U := by
  obtain ⟨t,ht,P,run,bP,hP⟩ := counts_runs C S.left B M hs.left room hparse size budget input
  let X := Ports.target (scalarPort fields) (arrayPort fields) P
  have pre : extractBase fields X = P.right := by
    apply Store.ext
    · intro i; simp [extractBase,X,Ports.target,scalarPort,Store.right]
    · intro a; simp [extractBase,X,Ports.target,arrayPort,Store.right]
  have lit (i : CircuitRecordPipeline.Reg fields) (k : ℕ) (h : scalarPort fields i=.literal k) : k≤M := by
    unfold scalarPort at h
    split at h <;> cases h;omega
  have bp := bounded_mono bP hBM
  have bs := bounded_mono hs hBM
  have wire := Ports.code_runs (scalarPort fields) (arrayPort fields) P S.right M (bp.join bs.right) lit
  obtain ⟨u,hu,Q,last,bQ,_,result⟩ := tables_runs fields (ofCircuit C) B M X wire.2 (pre ▸ hP)
  have full := Ports.thenRun_runs counts (scalarPort fields) (arrayPort fields) (tables fields) S.left P S.right Q M t u
    bs.left bp bs.right lit (run.mono (storage_mono _ _ hBM)) last
  rw [Store.join_left_right] at full
  have coord := congrArg Data.coordinates hP.data
  refine ⟨_,Nat.add_le_add ht (Nat.add_le_add_left hu _),P.join Q,full,bp.join bQ,coord,hP.sizes .dimension,hP.sizes .source,?_⟩
  intro f
  exact (result f (by cases f <;> decide)).trans (fieldWord_eq _ _)
end GroupWL.MachinePrograms.CircuitRecordPipeline.Metadata
