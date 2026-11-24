import GroupWL.MachinePrograms.DescriptorPipelineSetup

/-! Run independent descriptor-field and form-matrix clients from the same
computed metadata. Each worker contributes a fixed finite register bank. -/
namespace GroupWL.MachinePrograms.DescriptorPipeline
open NatArrayLanguage NatArrayExpressions
set_option maxHeartbeats 4000000
set_option maxRecDepth 12288
set_option synthInstance.maxSize 65536

structure Worker where
  Reg : Type
  Arr : Type
  [deqR : DecidableEq Reg]
  [deqA : DecidableEq Arr]
  [finR : Fintype Reg]
  [finA : Fintype Arr]
  scalars : Reg → Ports.Scalar SourceReg SourceArr
  arrays : Arr → Option SourceArr
  program : NatArrayLanguage.Program Reg Arr
  read : Store Reg Arr → List (List ℕ)
  meaning : Layout → List (List ℕ)
  cost : Layout → ℕ
  small : ∀i k,scalars i = .literal k → k=0
  sound : ∀(D : Layout) (M : ℕ) (v : D.Valid M) (P : SourceState), Source D P →
    (Ports.target scalars arrays P).Bounded M →
    ∃t ≤ cost D,∃T,Runs (storageBound Reg Arr M) program (Ports.target scalars arrays P) t T ∧
      T.Bounded M ∧ read T = meaning D
attribute [instance] Worker.deqR Worker.deqA Worker.finR Worker.finA

def Worker.pair (x y : Worker) : Worker where
  Reg := x.Reg ⊕ y.Reg
  Arr := x.Arr ⊕ y.Arr
  scalars := Sum.elim x.scalars y.scalars
  arrays := Sum.elim x.arrays y.arrays
  program := .seq (x.program.map Sum.inl Sum.inl) (y.program.map Sum.inr Sum.inr)
  read := fun T => x.read T.left ++ y.read T.right
  meaning := fun D => x.meaning D ++ y.meaning D
  cost := fun D => x.cost D + y.cost D
  small := fun i k => by cases i with | inl i => exact x.small i k | inr i => exact y.small i k
  sound := by
    intro D M h P source bounded
    obtain ⟨t,ht,T,run,hT,first⟩ := x.sound D M h P source bounded.left
    obtain ⟨u,hu,U,run',hU,last⟩ := y.sound D M h P source bounded.right
    let S := Ports.target (Sum.elim x.scalars y.scalars) (Sum.elim x.arrays y.arrays) P
    let W := T.join S.right
    have hW : W.Bounded M := hT.join bounded.right
    have r1 : Runs (storageBound x.Reg x.Arr M) x.program S.left t T := run
    have r2 : Runs (storageBound y.Reg y.Arr M) y.program W.right u U := run'
    exact ⟨t+u,Nat.add_le_add ht hu,T.join U,(r1.left_bounded bounded).seq (r2.right_bounded hW),hT.join hU,
      congrArg₂ List.append first last⟩

private def srcR (r : InputReg) : Ports.Scalar SourceReg SourceArr := .scalar (.inl (.inl r))
private def srcA (a : InputArr) : Option SourceArr := some (.inl (.inl a))
private def fs (f : InternalWedgeDescriptors.Field) : WedgeDescriptorTables.Reg f → Ports.Scalar SourceReg SourceArr
  | .inl (.inl (.inl (.inl .total))) => srcR .internalTotal
  | .inl (.inl (.inl (.inl .frames))) => srcR .frames
  | .inl (.inl (.inl (.inl .cap))) => srcR .cap
  | .inl (.inl (.inl (.inl .pairs))) => srcR .pairs
  | .inl (.inl (.inr .selected)) => .scalar (.inr .count)
  | .inl (.inr (.inl .total)) => srcR .edgeTotal
  | .inl (.inr (.inl .frames)) => srcR .frames
  | .inl (.inr (.inl .readouts)) => srcR .readouts
  | .inl (.inr (.inl .oldInput)) => srcR .oldInput
  | _ => .literal 0
private def fa : WedgeDescriptorTables.Arr → Option SourceArr
  | .inl (.inl (.inl .dimensions)) => srcA .dimensions
  | .inl (.inl (.inl .offsets)) => srcA .offsets
  | .inl (.inl (.inl .pairCodes)) => srcA .pairs
  | .inl (.inl (.inr .flags)) => some (.inl (.inr .output))
  | .inl (.inr .offsets) => srcA .offsets
  | .inl (.inr .incidences) => srcA .incidences
  | _ => none

def fieldWorker (f : InternalWedgeDescriptors.Field) : Worker where
  Reg := WedgeDescriptorTables.Reg f
  Arr := WedgeDescriptorTables.Arr
  scalars := fs f
  arrays := fa
  program := WedgeDescriptorTables.program f
  read := fun T => [T.right.array 2]
  meaning := fun D => [D.fieldWord f]
  cost := fun D => D.internalCount*((InternalWedgeDescriptors.expression f).cost+12)+
    D.edgeCount*((EdgeWedgeDescriptors.expression f).cost+4)+8*(D.selected+D.edgeCount)+32
  small := by intro i k h; unfold fs at h; split at h <;> simp_all [srcR]
  sound := by
    intro D M v P src hB
    let B := Ports.target (fs f) fa P
    have iReady : InternalWedgeDescriptors.Ready D.internal (inputs B.left.left.left) :=
      ⟨src.prepared.frames,src.prepared.cap,src.prepared.pairCount,src.prepared.dimensions,
        src.prepared.offsets,src.prepared.pairs⟩
    have eReady : EdgeWedgeDescriptors.Ready D.edges (inputs B.left.right) :=
      ⟨src.prepared.frames,src.prepared.readouts,src.prepared.oldInput,src.prepared.offsets,src.prepared.incidences⟩
    have hf : B.left.left.right.array .flags = D.flags := src.flags
    have hc : B.left.left.right.scalar .selected = D.selected := src.selected
    obtain ⟨t,ht,T,run,hT,out⟩ := WedgeDescriptorTables.program_runs D.internal D.edges f M v.internal v.edges B hB
      iReady eReady src.prepared.internalTotal src.prepared.edgeTotal (by rw [hf]; exact List.length_ofFn)
      (by rw [hf]; exact D.flags_binary) (by rw [hf,hc];rfl) (by rw [hc];exact v.outputSpace)
    rw [hc] at ht
    rw [hf] at out
    exact ⟨t,ht,T,run,hT,by rw [out];rfl⟩

abbrev FormReg := Registers IncidenceFormMatrix.Reg IncidenceFormMatrix.expression.need
private def ms : FormReg → Ports.Scalar SourceReg SourceArr
  | .inl .total => srcR .matrixTotal | .inl .frames => srcR .frames
  | .inl .blocks => srcR .blocks | .inl .readouts => srcR .readouts | .inl .oldInput => srcR .oldInput
  | _ => .literal 0
private def ma : IncidenceFormMatrix.Arr → Option SourceArr
  | .dimensions => srcA .dimensions | .offsets => srcA .offsets | .incidences => srcA .incidences
  | .radicals => srcA .radicals | .output => none

def formWorker : Worker where
  Reg := FormReg
  Arr := IncidenceFormMatrix.Arr
  scalars := ms
  arrays := ma
  program := IncidenceFormMatrix.program
  read := fun T => [T.array .output]
  meaning := fun D => [D.matrixWord]
  cost := fun D => D.matrixCount*(IncidenceFormMatrix.expression.cost+4)+6
  small := by intro i k h; unfold ms at h; split at h <;> simp_all [srcR]
  sound := by
    intro D M v P src hB
    let B := Ports.target ms ma P
    have ready : IncidenceFormMatrix.Ready D.forms (inputs B) :=
      ⟨src.prepared.frames,src.prepared.blocks,src.prepared.readouts,src.prepared.oldInput,
        src.prepared.dimensions,src.prepared.offsets,src.prepared.incidences,src.prepared.radicals⟩
    obtain ⟨t,ht,T,run,hT,_,out⟩ := IncidenceFormMatrix.program_runs D.forms M v.forms v.edges.room B
      hB ready src.prepared.matrixTotal
    exact ⟨t,ht,T,run,hT,by rw [out];rfl⟩

def workers := (fieldWorker .u0).pair ((fieldWorker .v0).pair ((fieldWorker .u1).pair
    ((fieldWorker .v1).pair ((fieldWorker .second).pair formWorker))))
abbrev Reg := SourceReg ⊕ workers.Reg
abbrev Arr := SourceArr ⊕ workers.Arr
abbrev State := Store Reg Arr
abbrev inputReg (r : InputReg) : Reg := .inl (.inl (.inl r))
abbrev inputArr (a : InputArr) : Arr := .inl (.inl (.inl a))
abbrev inputState (S : State) := S.left.left.left
abbrev u0Port : Arr := .inr (.inl (.inr 2))
abbrev v0Port : Arr := .inr (.inr (.inl (.inr 2)))
abbrev u1Port : Arr := .inr (.inr (.inr (.inl (.inr 2))))
abbrev v1Port : Arr := .inr (.inr (.inr (.inr (.inl (.inr 2)))))
abbrev secondPort : Arr := .inr (.inr (.inr (.inr (.inr (.inl (.inr 2))))))
abbrev formPort : Arr := .inr (.inr (.inr (.inr (.inr (.inr .output)))))
noncomputable def program : NatArrayLanguage.Program Reg Arr := Ports.thenRun sourceProgram workers.scalars workers.arrays workers.program
def cost (D : Layout) := sourceCost D+(Fintype.card workers.Reg+Fintype.card workers.Arr+workers.cost D)

private def model (i e z m : ℕ) :=
  let f := fun t => i*((InternalWedgeDescriptors.expression t).cost+12)+
    e*((EdgeWedgeDescriptors.expression t).cost+4)+8*z+32
  (12+(Fintype.card MaskReg+Fintype.card MaskArr+(i*((InternalWedgeDescriptors.expression .keep).cost+4)+6))+
    (Fintype.card FilterRanks.Reg+Fintype.card FilterRanks.Arr+(6*i+8)))+
  (Fintype.card workers.Reg+Fintype.card workers.Arr+(f .u0+(f .v0+(f .u1+(f .v1+
    (f .second+(m*(IncidenceFormMatrix.expression.cost+4)+6)))))))
def coefficient := model 1 1 1 1

theorem cost_le (D : Layout) (M : ℕ) (v : D.Valid M) : cost D ≤ coefficient*(M+1) := by
  have hi := v.internalSpace
  have he : D.edgeCount ≤ M := by have := v.outputSpace; omega
  have hz := v.outputSpace
  have hm := v.matrixSpace
  change model D.internalCount D.edgeCount (D.selected+D.edgeCount) D.matrixCount ≤ _
  calc
    _ ≤ model M M M M := by dsimp only [model]; gcongr
    _ ≤ _ := by unfold coefficient model;ring_nf;omega

structure Output (D : Layout) (T : State) : Prop where
  u0 : T.array u0Port = D.fieldWord .u0
  v0 : T.array v0Port = D.fieldWord .v0
  u1 : T.array u1Port = D.fieldWord .u1
  v1 : T.array v1Port = D.fieldWord .v1
  second : T.array secondPort = D.fieldWord .second
  matrix : T.array formPort = D.matrixWord

theorem tables_runs (D : Layout) (M : ℕ) (v : D.Valid M) (S : State) (hS : S.Bounded M)
    (h : Input D (inputState S)) : ∃t≤cost D,∃T,
    Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧ Source D T.left ∧ Output D T := by
  obtain ⟨t,ht,P,first,hP,src⟩ := source_runs D M v S.left hS.left h
  have small : ∀i k,workers.scalars i=.literal k → k ≤ M := fun i k h => by rw [workers.small i k h];omega
  obtain ⟨_,hW⟩ := Ports.code_runs workers.scalars workers.arrays P S.right M (hP.join hS.right) small
  obtain ⟨u,hu,U,second,hU,out⟩ := workers.sound D M v P src hW
  have run := Ports.thenRun_runs _ workers.scalars workers.arrays _ S.left P S.right U M t u
    hS.left hP hS.right small first second
  rw [Store.join_left_right] at run
  let T := P.join U
  change [T.array u0Port,T.array v0Port,T.array u1Port,T.array v1Port,T.array secondPort,T.array formPort]=
    [D.fieldWord .u0,D.fieldWord .v0,D.fieldWord .u1,D.fieldWord .v1,D.fieldWord .second,D.matrixWord] at out
  simp only [List.cons.injEq,and_true] at out
  exact ⟨t+(Fintype.card workers.Reg+Fintype.card workers.Arr+u),by unfold cost;omega,T,run,hP.join hU,src,out.1,out.2.1,out.2.2.1,out.2.2.2.1,out.2.2.2.2.1,out.2.2.2.2.2⟩

end GroupWL.MachinePrograms.DescriptorPipeline
