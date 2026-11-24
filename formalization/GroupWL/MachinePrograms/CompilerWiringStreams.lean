import GroupWL.MachinePrograms.CompilerSchemas
import GroupWL.MachinePrograms.CompilerLoops
import GroupWL.FiniteCodeEnumeration

/-! Polynomial-time nested streams of the cellular wiring schemas. -/
namespace GroupWL.MachinePrograms.Structured

open AddressedCircuit BinaryAddress CellularTableau CircuitDescription

def spatialLoopRegisters : Fin 5 ↪ Fin 8 := ⟨![0,4,5,1,7],by decide⟩
def temporalLoopRegisters : Fin 5 ↪ Fin 8 := ⟨![0,2,3,1,7],by decide⟩

def spatialWord {Alphabet : Type*} [FiniteCode Alphabet] {d : ℕ}
    (mode : SchemaMode) (rule : Alphabet → Alphabet → Alphabet → Alphabet)
    (x y z : Alphabet) (h : Fin d) : List Bool :=
  (List.ofFn (fun k : Fin d => schemaWord (TableauWiring.schema rule (mode.index x y z h k)))).flatten

def emitSpatial {K Alphabet : Type*} [FiniteCode Alphabet] (reg : Fin 8 ↪ K)
    (mode : SchemaMode) (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) : Program K :=
  enumerateCoordinates (spatialLoopRegisters.trans reg) (emitSchema reg mode rule x y z)

theorem emitSpatial_writes {K Alphabet : Type*} [DecidableEq K] [FiniteCode Alphabet]
    (S : Store K) (reg : Fin 8 ↪ K) (mode : SchemaMode)
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) {d : ℕ} (h : Fin d)
    (hd : S (reg 0) = List.replicate d true)
    (hh : S (reg 2) = List.replicate h.val true)
    (hh' : S (reg 3) = List.replicate (d-h.val-1) true)
    (h₄ : S (reg 4) = []) (h₅ : S (reg 5) = []) (h₆ : S (reg 6) = []) (h₇ : S (reg 7) = []) :
    Writes (reg 1) (emitSpatial reg mode rule x y z) S (spatialWord mode rule x y z h)
      (d*(2*FiniteCode.size (Gate Alphabet)+42*d+25)+4) := by
  have heq (i j : Fin 8) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let word (i : ℕ) := if hi : i < d then
    schemaWord (TableauWiring.schema rule (mode.index x y z h ⟨i,hi⟩)) else []
  have hbody : ∀ i < d, ∃ time ≤ 2*FiniteCode.size (Gate Alphabet)+42*d+13,
      Runs (emitSchema reg mode rule x y z)
        (coordinateCut S (reg 4) (reg 5) (reg 1) d i word) time
        (Function.update (coordinateCut S (reg 4) (reg 5) (reg 1) d i word) (reg 1)
          ((word i).reverse++(coordinateState S (reg 4) (reg 5) (reg 1) d i word) (reg 1))) := by
    intro i hi
    let V := coordinateCut S (reg 4) (reg 5) (reg 1) d i word
    have hv : SchemaReady reg V mode h ⟨i,hi⟩ := by
      refine ⟨?_,?_,?_,?_,?_⟩
      · simp [V,coordinateCut,coordinateState,heq,hd]
      · simp [V,coordinateCut,coordinateState,heq,h₆]
      · simp [V,coordinateCut,coordinateState,heq,h₇]
      · intro _
        simp [BlockSegments,timeBlockRegisters,V,coordinateCut,coordinateState,heq,hh,hh']
      · intro _
        simp [BlockSegments,spaceBlockRegisters,V,coordinateCut,coordinateState,heq]
    obtain ⟨time,ht,hr⟩ := emitSchema_writes V reg mode rule x y z h ⟨i,hi⟩ hv
    refine ⟨time,ht,?_⟩
    simpa only [V,word,dif_pos hi,coordinateCut,
      Function.update_of_ne (show reg 1 ≠ reg 5 from fun h =>
        (by decide : (1 : Fin 8) ≠ 5) (reg.injective h))] using hr
  have h := enumerateCoordinates_runs S (spatialLoopRegisters.trans reg) d
    (2*FiniteCode.size (Gate Alphabet)+42*d+13) word (emitSchema reg mode rule x y z)
    hd h₄ h₅ h₇ hbody
  simpa [Writes,emitSpatial,spatialWord,prefixWord_ofFn,word,spatialLoopRegisters,
    Nat.add_assoc] using h

inductive WiringRow where
  | left | center | right
  deriving DecidableEq

def WiringRow.prelude : WiringRow → SchemaMode
  | .left => .leftWrap | .center => .center | .right => .rightWrap

def WiringRow.step : WiringRow → SchemaMode
  | .left => .leftStep | .center => .center | .right => .rightStep

def rowWord {Alphabet : Type*} [FiniteCode Alphabet] {d : ℕ}
    (row : WiringRow) (rule : Alphabet → Alphabet → Alphabet → Alphabet)
    (x y z : Alphabet) (h : Fin d) : List Bool :=
  schemaWord (TableauWiring.schema rule (row.prelude.index x y z h h)) ++
    if row = .center then [] else spatialWord row.step rule x y z h

def emitRow {K Alphabet : Type*} [FiniteCode Alphabet] (reg : Fin 8 ↪ K)
    (row : WiringRow) (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) : Program K :=
  .seq (emitSchema reg row.prelude rule x y z)
    (if row = .center then .skip else emitSpatial reg row.step rule x y z)

def rowBound (N d : ℕ) := (2*N+42*d+13)+(d*(2*N+42*d+25)+4)

theorem emitRow_writes {K Alphabet : Type*} [DecidableEq K] [FiniteCode Alphabet]
    (S : Store K) (reg : Fin 8 ↪ K) (row : WiringRow)
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) {d : ℕ} (h : Fin d)
    (hd : S (reg 0) = List.replicate d true)
    (hh : S (reg 2) = List.replicate h.val true)
    (hh' : S (reg 3) = List.replicate (d-h.val-1) true)
    (h₄ : S (reg 4) = []) (h₅ : S (reg 5) = []) (h₆ : S (reg 6) = []) (h₇ : S (reg 7) = []) :
    Writes (reg 1) (emitRow reg row rule x y z) S (rowWord row rule x y z h)
      (rowBound (FiniteCode.size (Gate Alphabet)) d) := by
  have heq (i j : Fin 8) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  have hv : SchemaReady reg S row.prelude h h := by
    refine ⟨hd,h₆,h₇,?_,?_⟩
    · intro _
      simpa [BlockSegments,timeBlockRegisters] using And.intro hh hh'
    · cases row <;> simp [WiringRow.prelude]
  have first := emitSchema_writes S reg row.prelude rule x y z h h hv
  let V := Function.update S (reg 1)
    ((schemaWord (TableauWiring.schema rule (row.prelude.index x y z h h))).reverse++S (reg 1))
  by_cases hc : row = .center
  · subst row
    have last : Writes (reg 1) (.skip : Program K) V []
        (d*(2*FiniteCode.size (Gate Alphabet)+42*d+25)+4) := by
      refine ⟨0,Nat.zero_le _,?_⟩
      simpa using Runs.skip V
    simpa [emitRow,rowWord,rowBound] using first.seq last
  · have last := emitSpatial_writes V reg row.step rule x y z h
      (by simpa [V,heq] using hd) (by simpa [V,heq] using hh)
      (by simpa [V,heq] using hh') (by simpa [V,heq] using h₄)
      (by simpa [V,heq] using h₅) (by simpa [V,heq] using h₆) (by simpa [V,heq] using h₇)
    simpa [emitRow,rowWord,rowBound,hc] using first.seq last

def WiringReady {K : Type*} (reg : Fin 8 ↪ K) (S : Store K) (d : ℕ) : Prop :=
  S (reg 0) = List.replicate d true ∧ ∀ i : Fin 8, 2 ≤ i.val → S (reg i) = []

theorem WiringReady.update_output {K : Type*} [DecidableEq K] {reg : Fin 8 ↪ K}
    {S : Store K} {d : ℕ} (hs : WiringReady reg S d) (word : List Bool) :
    WiringReady reg (Function.update S (reg 1) word) d := by
  have heq (i j : Fin 8) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  refine ⟨by simpa [heq] using hs.1,?_⟩
  intro i hi
  have hne : i ≠ 1 := by intro h; subst i; contradiction
  simpa [heq,hne] using hs.2 i hi

def temporalWord {Alphabet : Type*} [FiniteCode Alphabet] (d : ℕ)
    (row : WiringRow) (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) : List Bool :=
  (List.ofFn (rowWord row rule x y z : Fin d → List Bool)).flatten

def emitTemporal {K Alphabet : Type*} [FiniteCode Alphabet] (reg : Fin 8 ↪ K)
    (row : WiringRow) (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) : Program K :=
  enumerateCoordinates (temporalLoopRegisters.trans reg) (emitRow reg row rule x y z)

def temporalBound (N d : ℕ) := d*(rowBound N d+12)+4

theorem emitTemporal_writes {K Alphabet : Type*} [DecidableEq K] [FiniteCode Alphabet]
    (S : Store K) (reg : Fin 8 ↪ K) (row : WiringRow)
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) (d : ℕ)
    (hs : WiringReady reg S d) :
    Writes (reg 1) (emitTemporal reg row rule x y z) S (temporalWord d row rule x y z)
      (temporalBound (FiniteCode.size (Gate Alphabet)) d) := by
  have heq (i j : Fin 8) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let word (i : ℕ) := if hi : i < d then rowWord row rule x y z ⟨i,hi⟩ else []
  have hbody : ∀ i < d, ∃ time ≤ rowBound (FiniteCode.size (Gate Alphabet)) d,
      Runs (emitRow reg row rule x y z)
        (coordinateCut S (reg 2) (reg 3) (reg 1) d i word) time
        (Function.update (coordinateCut S (reg 2) (reg 3) (reg 1) d i word) (reg 1)
          ((word i).reverse++(coordinateState S (reg 2) (reg 3) (reg 1) d i word) (reg 1))) := by
    intro i hi
    let V := coordinateCut S (reg 2) (reg 3) (reg 1) d i word
    obtain ⟨time,ht,hr⟩ := emitRow_writes V reg row rule x y z ⟨i,hi⟩
      (by simp [V,coordinateCut,coordinateState,heq,hs.1])
      (by simp [V,coordinateCut,coordinateState,heq])
      (by simp [V,coordinateCut,coordinateState,heq])
      (by simp [V,coordinateCut,coordinateState,heq,hs.2 4 (by decide)])
      (by simp [V,coordinateCut,coordinateState,heq,hs.2 5 (by decide)])
      (by simp [V,coordinateCut,coordinateState,heq,hs.2 6 (by decide)])
      (by simp [V,coordinateCut,coordinateState,heq,hs.2 7 (by decide)])
    refine ⟨time,ht,?_⟩
    simpa only [V,word,dif_pos hi,coordinateCut,
      Function.update_of_ne (show reg 1 ≠ reg 3 from fun h =>
        (by decide : (1 : Fin 8) ≠ 3) (reg.injective h))] using hr
  have h := enumerateCoordinates_runs S (temporalLoopRegisters.trans reg) d
    (rowBound (FiniteCode.size (Gate Alphabet)) d) word (emitRow reg row rule x y z)
    hs.1 (hs.2 2 (by decide)) (hs.2 3 (by decide)) (hs.2 7 (by decide)) hbody
  simpa [Writes,emitTemporal,temporalWord,temporalBound,prefixWord_ofFn,word,temporalLoopRegisters] using h

def tripleWord {Alphabet : Type*} [FiniteCode Alphabet] (d : ℕ)
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) : List Bool :=
  temporalWord d .left rule x y z ++ temporalWord d .center rule x y z ++
    temporalWord d .right rule x y z ++
    schemaWord (TableauWiring.schema (d := d) rule ((x,y,z),.inr (.inr (.inr false)))) ++
    schemaWord (TableauWiring.schema (d := d) rule ((x,y,z),.inr (.inr (.inr true))))

def emitTriple {K Alphabet : Type*} [FiniteCode Alphabet] (reg : Fin 8 ↪ K)
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) : Program K :=
  .seq (emitTemporal reg .left rule x y z)
    (.seq (emitTemporal reg .center rule x y z)
      (.seq (emitTemporal reg .right rule x y z)
        (.seq (emitSchema reg .pair rule x y z) (emitSchema reg .output rule x y z))))

def tripleBound (N d : ℕ) := 3*temporalBound N d+2*(2*N+42*d+13)

theorem emitTriple_writes {K Alphabet : Type*} [DecidableEq K] [FiniteCode Alphabet]
    (S : Store K) (reg : Fin 8 ↪ K)
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) (d : ℕ)
    (hd : 0 < d) (hs : WiringReady reg S d) :
    Writes (reg 1) (emitTriple reg rule x y z) S (tripleWord d rule x y z)
      (tripleBound (FiniteCode.size (Gate Alphabet)) d) := by
  let h : Fin d := ⟨0,hd⟩
  have temporal (V : Store K) (hv : WiringReady reg V d) (row : WiringRow) :=
    emitTemporal_writes V reg row rule x y z d hv
  have last (V : Store K) (hv : WiringReady reg V d) (mode : SchemaMode)
      (hm : mode = .pair ∨ mode = .output) :=
    emitSchema_writes V reg mode rule x y z h h (by
      refine ⟨hv.1,hv.2 6 (by decide),hv.2 7 (by decide),?_,?_⟩
      · rcases hm with rfl | rfl <;> simp
      · rcases hm with rfl | rfl <;> simp)
  let V₁ := Function.update S (reg 1) ((temporalWord d .left rule x y z).reverse++S (reg 1))
  let V₂ := Function.update V₁ (reg 1) ((temporalWord d .center rule x y z).reverse++V₁ (reg 1))
  let V₃ := Function.update V₂ (reg 1) ((temporalWord d .right rule x y z).reverse++V₂ (reg 1))
  let V₄ := Function.update V₃ (reg 1)
    ((schemaWord (TableauWiring.schema (d := d) rule ((x,y,z),.inr (.inr (.inr false))))).reverse++V₃ (reg 1))
  have h₁ : WiringReady reg V₁ d := hs.update_output _
  have h₂ : WiringReady reg V₂ d := h₁.update_output _
  have h₃ : WiringReady reg V₃ d := h₂.update_output _
  have h₄ : WiringReady reg V₄ d := h₃.update_output _
  have result := (temporal S hs .left).seq ((temporal V₁ h₁ .center).seq
    ((temporal V₂ h₂ .right).seq ((last V₃ h₃ .pair (Or.inl rfl)).seq
      (last V₄ h₄ .output (Or.inr rfl)))))
  convert result using 1 <;> simp only [emitTriple,tripleWord,SchemaMode.index,List.append_assoc,tripleBound] <;> ring

def emitSequence {K α : Type*} (f : α → Program K) : List α → Program K
  | [] => .skip
  | a::as => .seq (f a) (emitSequence f as)

theorem emitSequence_writes {K α : Type*} [DecidableEq K]
    (output : K) (P : Store K → Prop) (f : α → Program K) (word : α → List Bool) (B : ℕ)
    (hP : ∀ S, P S → ∀ w, P (Function.update S output w))
    (hf : ∀ S, P S → ∀ a, Writes output (f a) S (word a) B)
    (as : List α) (S : Store K) (hs : P S) :
    Writes output (emitSequence f as) S (as.map word).flatten (as.length*B) := by
  induction as generalizing S with
  | nil =>
    refine ⟨0,Nat.zero_le _,?_⟩
    simpa [emitSequence] using Runs.skip S
  | cons a as ih =>
    have first := hf S hs a
    have last := ih (Function.update S output ((word a).reverse++S output))
      (hP S hs ((word a).reverse++S output))
    simpa [emitSequence,Nat.add_mul,Nat.add_comm] using first.seq last

def wiringWord {Alphabet : Type*} [FiniteCode Alphabet] (d : ℕ)
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) : List Bool :=
  ((FiniteCode.enumeration (Alphabet × Alphabet × Alphabet)).map
    (fun xyz => tripleWord d rule xyz.1 xyz.2.1 xyz.2.2)).flatten

def emitWiring {K Alphabet : Type*} [FiniteCode Alphabet] (reg : Fin 8 ↪ K)
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) : Program K :=
  emitSequence (fun xyz : Alphabet × Alphabet × Alphabet =>
    emitTriple reg rule xyz.1 xyz.2.1 xyz.2.2) (FiniteCode.enumeration _)

theorem emitWiring_writes {K Alphabet : Type*} [DecidableEq K] [FiniteCode Alphabet]
    (S : Store K) (reg : Fin 8 ↪ K)
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) (d : ℕ)
    (hd : 0 < d) (hs : WiringReady reg S d) :
    Writes (reg 1) (emitWiring reg rule) S (wiringWord d rule)
      ((FiniteCode.size Alphabet)^3*tripleBound (FiniteCode.size (Gate Alphabet)) d) := by
  have result := emitSequence_writes (reg 1) (fun S => WiringReady reg S d)
    (fun xyz : Alphabet × Alphabet × Alphabet => emitTriple reg rule xyz.1 xyz.2.1 xyz.2.2)
    (fun xyz => tripleWord d rule xyz.1 xyz.2.1 xyz.2.2)
    (tripleBound (FiniteCode.size (Gate Alphabet)) d)
    (fun _ h _ => h.update_output _) (fun _ h xyz => emitTriple_writes _ _ _ _ _ _ _ hd h)
    (FiniteCode.enumeration _) S hs
  convert result using 1
  simp only [FiniteCode.enumeration,List.length_ofFn]
  change (FiniteCode.size Alphabet)^3*_ =
    (FiniteCode.size Alphabet*(FiniteCode.size Alphabet*FiniteCode.size Alphabet))*_
  ring

end GroupWL.MachinePrograms.Structured
