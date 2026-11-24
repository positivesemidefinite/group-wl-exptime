import GroupWL.MachinePrograms.DescriptorPipelineData
import GroupWL.MachinePrograms.DescriptorPipelineTables

/-! The six materialized output arrays are the canonical obstruction descriptors
and the ordinary form matrix. The five descriptor passes share a computed mask. -/
namespace GroupWL.MachinePrograms.DescriptorPipeline
open NatArrayLanguage ConstructiveIncidence IncidenceTensor ConstructiveCoordinates
set_option maxRecDepth 12288
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 2000000
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [FiniteCode I] [FiniteCode J]
variable (p : ℕ) [Fact p.Prime]
variable {V : J → Type} [∀j, AddCommGroup (V j)] [∀j, Module (ZMod p) (V j)]
variable (A : AffineSystem (ZMod p) I J V) (R : ∀j, Coordinates (ZMod p) (ReadoutRadical A j)) (q cap : ℕ)
def layout (radicals : List ℕ) : Layout where
  frames := q
  cap := cap
  blocks := FiniteCode.size I
  readouts := FiniteCode.size J
  oldInput := FiniteCode.size (OldInputIndex A R q)
  dimensions := ringDimensions A R
  offsets := inputOffsets A R q
  pairs := FramePairEncoding.word q
  incidences := edgeIncidences A
  radicals := radicals

private theorem layout_internal (rs : List ℕ) : (layout p A R q cap rs).internal = internalData A R q cap := by
  simp [layout,Layout.internal,internalData,ringDimensions,FramePairEncoding.word]
private theorem layout_edges (rs : List ℕ) : (layout p A R q cap rs).edges = edgeData A R q := by
  simp [layout,Layout.edges,edgeData,edgeIncidences]
private theorem layout_forms (rs : List ℕ) : (layout p A R q cap rs).forms = formData p A R q rs := by
  simp [layout,Layout.forms,formData,edgeIncidences]
private theorem layout_flags (rs : List ℕ) : (layout p A R q cap rs).flags = internalRaw A R q cap .keep := by
  rw [Layout.flags,layout_internal];rfl

theorem layout_field (rs : List ℕ) (dims : ∀v,ringDimension A R v ≤ cap) (f : Field) :
    (layout p A R q cap rs).fieldWord f = canonicalField p A R q f := by
  rw [Layout.fieldWord,layout_flags,layout_internal,layout_edges]
  exact descriptor_tables_correct A R q cap dims f

theorem layout_matrix (rs : List ℕ) (spec : RadicalTableSpec p A R rs) (values : ∀x∈rs,x<p) :
    (layout p A R q cap rs).matrixWord = formMatrix p A R q := by
  unfold Layout.matrixWord
  have len : (layout p A R q cap rs).matrixCount =
      IncidenceFormMatrix.forms (formData p A R q rs)*FiniteCode.size (OldInputIndex A R q) := by
    simp [Layout.matrixCount,layout,IncidenceFormMatrix.forms,formData,edgeIncidences]
  simp only [len,layout_forms]
  exact formData_word p A R q rs spec values

structure Room (M : ℕ) : Prop where
  frames : 2 ≤ q
  capPositive : 0 < cap
  readouts : 0 < FiniteCode.size J
  oldInput : 0 < FiniteCode.size (OldInputIndex A R q)
  dimensions : ∀v,ringDimension A R v ≤ cap
  radicalDimensions : ∀v,ringDimension A R v ≤ FiniteCode.size I + 1
  two : 2 ≤ M
  offsets : inputTotal A R q+(q+1)*cap ≤ M
  edgeOffsets : inputTotal A R q+q*2+1 ≤ M
  forms : FiniteCode.size (OldInputIndex A R q)+FiniteCode.size (Incidence A)*q*2 ≤ M
  candidates : FiniteCode.size (I⊕J)*FiniteCode.size (Pair q)*cap ≤ M
  outputs : FiniteCode.size (OldOutputIndex A R q) ≤ M
  matrix : FiniteCode.size (FormIndex A R q)*FiniteCode.size (OldInputIndex A R q) ≤ M

theorem layout_valid (rs : List ℕ) (M : ℕ) (room : Room p A R q cap M)
    (length : rs.length=FiniteCode.size I*FiniteCode.size J*FiniteCode.size I) :
    (layout p A R q cap rs).Valid M := by
  constructor
  · rw [layout_internal]
    exact internalData_valid A R q cap M room.frames room.capPositive (by have := room.two;omega) room.dimensions room.offsets
  · rw [layout_edges]
    exact edgeValid p A R q M (by have := room.frames;omega) room.readouts room.two room.edgeOffsets room.forms
  · rw [layout_forms]
    exact formValid p A R q rs (by have := room.frames;omega) room.readouts room.oldInput length room.radicalDimensions
  · simpa [Layout.internalCount,layout,ringDimensions,FramePairEncoding.word] using room.candidates
  · simp only [Layout.selected,layout_flags,internalKeep_total A R q cap room.dimensions]
    have sz : FiniteCode.size (OldOutputIndex A R q) =
        FiniteCode.size (InternalIndex A R q) + FiniteCode.size (EdgeIndex A q) := rfl
    simpa only [Layout.edgeCount,layout,edgeIncidences,List.length_ofFn,←edgeIndex_size A q,←sz] using room.outputs
  · have f := formData_forms p A R q rs
    simpa [Layout.matrixCount,layout,IncidenceFormMatrix.forms,formData,edgeIncidences,←f] using room.matrix

structure CanonicalOutput (T : State) : Prop where
  u0 : T.array u0Port = (wedgeDescriptors p A R q).u0
  v0 : T.array v0Port = (wedgeDescriptors p A R q).v0
  u1 : T.array u1Port = (wedgeDescriptors p A R q).u1
  v1 : T.array v1Port = (wedgeDescriptors p A R q).v1
  second : T.array secondPort = (wedgeDescriptors p A R q).second
  matrix : T.array formPort = formMatrix p A R q

theorem program_runs (rs : List ℕ) (M : ℕ) (room : Room p A R q cap M)
    (length : rs.length=FiniteCode.size I*FiniteCode.size J*FiniteCode.size I)
    (spec : RadicalTableSpec p A R rs) (values : ∀x∈rs,x<p)
    (S : State) (bounded : S.Bounded M) (input : Input (layout p A R q cap rs) (inputState S)) :
    ∃t≤cost (layout p A R q cap rs),∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      Input (layout p A R q cap rs) (inputState T) ∧ CanonicalOutput p A R q T := by
  obtain ⟨t,ht,T,run,hT,src,out⟩ := tables_runs _ M (layout_valid p A R q cap rs M room length) S bounded input
  have hf := layout_field p A R q cap rs room.dimensions
  exact ⟨t,ht,T,run,hT,src.prepared.toInput,out.u0.trans (hf .u0),out.v0.trans (hf .v0),
    out.u1.trans (hf .u1),out.v1.trans (hf .v1),out.second.trans (hf .second),
    out.matrix.trans (layout_matrix p A R q cap rs spec values)⟩

end GroupWL.MachinePrograms.DescriptorPipeline
