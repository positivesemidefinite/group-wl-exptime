import GroupWL.MachinePrograms.KernelToTensor
import GroupWL.MachinePrograms.WedgeDescriptorTables
import GroupWL.MachinePrograms.IncidenceFormMatrix

/-! A common input frame for the descriptor tables. Compute table lengths and
      the actual internal keep mask and count before running the field clients. -/
namespace GroupWL.MachinePrograms.DescriptorPipeline
open NatArrayLanguage NatArrayExpressions
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192
structure Layout where
  frames : ℕ
  cap : ℕ
  blocks : ℕ
  readouts : ℕ
  oldInput : ℕ
  dimensions : List ℕ
  offsets : List ℕ
  pairs : List ℕ
  incidences : List ℕ
  radicals : List ℕ
namespace Layout
def internal (D : Layout) : InternalWedgeDescriptors.Data :=
  ⟨D.frames,D.cap,D.dimensions.length,D.pairs.length,D.dimensions,D.offsets,D.pairs⟩
def edges (D : Layout) : EdgeWedgeDescriptors.Data :=
  ⟨D.frames,D.readouts,D.blocks,D.incidences.length,D.oldInput,D.offsets,D.incidences⟩
def forms (D : Layout) : IncidenceFormMatrix.Data :=
  ⟨D.frames,D.blocks,D.readouts,D.incidences.length,D.oldInput,D.dimensions,D.offsets,D.incidences,D.radicals⟩
def internalCount (D : Layout) := D.dimensions.length*D.pairs.length*D.cap
def edgeCount (D : Layout) := D.incidences.length*D.frames*D.frames*2
def matrixCount (D : Layout) := (D.oldInput+D.incidences.length*D.frames*2)*D.oldInput
def flags (D : Layout) := InternalDescriptorRecords.word D.internal .keep
def selected (D : Layout) := FilterRanks.count D.flags D.flags.length
def fieldWord (D : Layout) (f : InternalWedgeDescriptors.Field) :=
  SelectArray.selectedPrefix D.flags (InternalDescriptorRecords.word D.internal f) D.flags.length
    ++ WedgeDescriptorTables.edgeWord D.edges f
def matrixWord (D : Layout) := List.ofFn (fun i : Fin D.matrixCount => IncidenceFormMatrix.value D.forms i)
theorem flags_binary (D : Layout) : ∀x∈D.flags,x≤1 := by
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  change (if _ then 1 else 0) ≤ 1
  split_ifs <;> omega
structure Valid (D : Layout) (M : ℕ) : Prop where
  internal : InternalWedgeDescriptors.Valid D.internal M
  edges : EdgeWedgeDescriptors.Valid D.edges M
  forms : IncidenceFormMatrix.Valid D.forms
  internalSpace : D.internalCount ≤ M
  outputSpace : D.selected + D.edgeCount ≤ M
  matrixSpace : D.matrixCount ≤ M
end Layout

inductive InputReg where
  | frames | cap | blocks | readouts | oldInput | pairs | internalTotal | edgeTotal | matrixTotal | temp | two
  deriving DecidableEq,Fintype
inductive InputArr where
  | dimensions | offsets | pairs | incidences | radicals
  deriving DecidableEq,Fintype
abbrev InputState := Store InputReg InputArr
structure Input (D : Layout) (S : InputState) : Prop where
  frames : S.scalar .frames = D.frames
  cap : S.scalar .cap = D.cap
  blocks : S.scalar .blocks = D.blocks
  readouts : S.scalar .readouts = D.readouts
  oldInput : S.scalar .oldInput = D.oldInput
  dimensions : S.array .dimensions = D.dimensions
  offsets : S.array .offsets = D.offsets
  pairs : S.array .pairs = D.pairs
  incidences : S.array .incidences = D.incidences
  radicals : S.array .radicals = D.radicals
structure Prepared (D : Layout) (S : InputState) extends Input D S where
  pairCount : S.scalar .pairs = D.pairs.length
  internalTotal : S.scalar .internalTotal = D.internalCount
  edgeTotal : S.scalar .edgeTotal = D.edgeCount
  matrixTotal : S.scalar .matrixTotal = D.matrixCount
def prepareAtoms : List (Atom InputReg InputArr) := [
  .const .two 2,.arrayLength .pairs .pairs,.arrayLength .internalTotal .dimensions,
  .binary .mul .internalTotal .internalTotal .pairs,.binary .mul .internalTotal .internalTotal .cap,
  .arrayLength .temp .incidences,.binary .mul .temp .temp .frames,
  .binary .mul .edgeTotal .temp .frames,.binary .mul .edgeTotal .edgeTotal .two,
  .binary .mul .temp .temp .two,.binary .add .temp .oldInput .temp,.binary .mul .matrixTotal .temp .oldInput]

theorem prepare_runs (D : Layout) (M : ℕ) (v : D.Valid M) (S : InputState) (hS : S.Bounded M)
    (h : Input D S) : Runs (storageBound InputReg InputArr M) (atoms prepareAtoms) S 12
      (applyAtoms prepareAtoms S) ∧ (applyAtoms prepareAtoms S).Bounded M ∧ Prepared D (applyAtoms prepareAtoms S) := by
  have hc : 0 < D.cap := v.internal.cap
  have hq : 0 < D.frames := v.internal.frames
  have hi : 0 < D.oldInput := v.forms.oldInput
  have iBound := v.internalSpace
  have eBound := v.outputSpace
  have mBound := v.matrixSpace
  dsimp only [Layout.internalCount,Layout.edgeCount,Layout.matrixCount] at iBound eBound mBound
  have h1 := Nat.le_mul_of_pos_right (D.dimensions.length*D.pairs.length) hc
  have h2 := Nat.le_mul_of_pos_right (D.incidences.length*D.frames) hq
  have h3 := Nat.le_mul_of_pos_right (D.oldInput+D.incidences.length*D.frames*2) hi
  have valid : ValidAtoms M prepareAtoms S := by
    simp [prepareAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,
      BinaryOp.eval,h.frames,h.cap,h.oldInput,h.dimensions,h.pairs,h.incidences]
    have := v.edges.room
    omega
  obtain ⟨run,bounded⟩ := atoms_runs hS _ valid
  refine ⟨run,bounded,?_,?_,?_,?_,?_⟩
  · constructor <;> simp [applyAtoms,prepareAtoms,Atom.apply,Store.setScalar,h.frames,h.cap,h.blocks,h.readouts,h.oldInput,h.dimensions,h.offsets,h.pairs,h.incidences,h.radicals]
  all_goals simp [applyAtoms,prepareAtoms,Atom.apply,Store.setScalar,BinaryOp.eval,h.frames,h.cap,
    h.oldInput,h.dimensions,h.pairs,h.incidences,Layout.internalCount,Layout.edgeCount,Layout.matrixCount]

abbrev MaskReg := Registers InternalWedgeDescriptors.Reg (InternalWedgeDescriptors.expression .keep).need
abbrev MaskArr := InternalWedgeDescriptors.Arr
def maskScalar : MaskReg → Ports.Scalar InputReg InputArr
  | .inl .total => .scalar .internalTotal | .inl .frames => .scalar .frames
  | .inl .cap => .scalar .cap | .inl .pairs => .scalar .pairs | _ => .literal 0
def maskArray : MaskArr → Option InputArr
  | .dimensions => some .dimensions | .offsets => some .offsets | .pairCodes => some .pairs | .output => none
abbrev MaskHostReg := InputReg ⊕ MaskReg
abbrev MaskHostArr := InputArr ⊕ MaskArr
noncomputable def maskProgram := Ports.thenRun (atoms prepareAtoms) maskScalar maskArray (InternalWedgeDescriptors.program .keep)
def rankScalar (_ : FilterRanks.Reg) : Ports.Scalar MaskHostReg MaskHostArr := .literal 0
def rankArray : FilterRanks.Arr → Option MaskHostArr | .flags => some (.inr .output) | .ranks => none
abbrev SourceReg := MaskHostReg ⊕ FilterRanks.Reg
abbrev SourceArr := MaskHostArr ⊕ FilterRanks.Arr
abbrev SourceState := Store SourceReg SourceArr
noncomputable def sourceProgram := Ports.thenRun maskProgram rankScalar rankArray FilterRanks.program
def sourceCost (D : Layout) := 12+(Fintype.card MaskReg+Fintype.card MaskArr+
  (D.internalCount*((InternalWedgeDescriptors.expression .keep).cost+4)+6))+
  (Fintype.card FilterRanks.Reg+Fintype.card FilterRanks.Arr+ (6*D.internalCount+8))
structure Source (D : Layout) (S : SourceState) : Prop where
  prepared : Prepared D S.left.left
  flags : S.left.right.array .output = D.flags
  selected : S.right.scalar .count = D.selected

theorem source_runs (D : Layout) (M : ℕ) (v : D.Valid M) (S : SourceState) (hS : S.Bounded M)
    (h : Input D S.left.left) : ∃t≤sourceCost D,∃T,
    Runs (storageBound SourceReg SourceArr M) sourceProgram S t T ∧ T.Bounded M ∧ Source D T := by
  obtain ⟨prep,hP,ok⟩ := prepare_runs D M v S.left.left hS.left.left h
  let P := applyAtoms prepareAtoms S.left.left
  have small : ∀i k,maskScalar i=.literal k → k≤M := by
    intro i k he
    rcases i with i|i
    · cases i <;> simp_all [maskScalar] <;> omega
    · simp_all [maskScalar] <;> omega
  obtain ⟨_,hB⟩ := Ports.code_runs maskScalar maskArray P S.left.right M (hP.join hS.left.right) small
  let B := Ports.target maskScalar maskArray P
  have ready : InternalWedgeDescriptors.Ready D.internal (inputs B) := ⟨ok.frames,ok.cap,ok.pairCount,
    ok.dimensions,ok.offsets,ok.pairs⟩
  obtain ⟨t,ht,U,mask,hU,_,flags⟩ := InternalWedgeDescriptors.program_runs D.internal .keep M v.internal B hB ready ok.internalTotal
  have first := Ports.thenRun_runs _ maskScalar maskArray _ S.left.left P S.left.right U M 12 t
    hS.left.left hP hS.left.right small prep mask
  rw [Store.join_left_right] at first
  let W := P.join U
  have hW : W.Bounded M := hP.join hU
  have sm : ∀i k,rankScalar i=.literal k → k≤M := by simp [rankScalar]
  obtain ⟨_,hY⟩ := Ports.code_runs rankScalar rankArray W S.right M (hW.join hS.right) sm
  let Y := Ports.target rankScalar rankArray W
  have fy : Y.array .flags = D.flags := flags
  obtain ⟨u,hu,Z,rank,hZ,count,_⟩ := FilterRanks.program_runs Y M hY v.internal.room (by rw [fy];exact D.flags_binary)
  have last := Ports.thenRun_runs _ rankScalar rankArray _ S.left W S.right Z M _ u
    hS.left hW hS.right sm first rank
  rw [Store.join_left_right] at last
  rw [fy] at hu count
  change u ≤ 6*(List.ofFn _).length+8 at hu
  rw [List.length_ofFn] at hu
  refine ⟨_,?_,W.join Z,last,hW.join hZ,ok,flags,count⟩
  unfold sourceCost
  change t ≤ D.internalCount*((InternalWedgeDescriptors.expression .keep).cost+4)+6 at ht
  change u ≤ 6*D.internalCount+8 at hu
  omega

end GroupWL.MachinePrograms.DescriptorPipeline
