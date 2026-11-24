import GroupWL.MachinePrograms.CircuitParserStages

/-! Fixed register initialization and section-size arithmetic for circuit parsing. -/
namespace GroupWL.MachinePrograms.CircuitParserStages
open NatArrayLanguage CircuitRecordParser AddressedCircuit
open NatArrayLowering (bitNat)
set_option maxHeartbeats 2000000

structure Ready (w : List Bool) (S : State) : Prop where
  length : S.scalar (cr .length)=w.length
  valid : S.scalar (cr .valid)=1
  input : S.array (ca .input)=w.map bitNat
  zero : S.scalar (wr .zero)=0
  one : S.scalar (wr .one)=1
  two : S.scalar (wr .two)=2
  three : S.scalar (wr .three)=3

variable {T : Type*} [FiniteCode T] {r : ℕ}
structure Metadata (C : Circuit T r) (S : State) : Prop where
  types : S.scalar (wr .types)=FiniteCode.size T
  coordinates : S.scalar (wr .coordinates)=r
  edges : S.scalar (wr .edges)=C.edges
  seeds : S.scalar (wr .seeds)=C.seedCount
  tests : S.scalar (wr .tests)=C.testCount

structure Budget (C : Circuit T r) (M : ℕ) : Prop where
  room : 5≤M
  triple : 3*r≤M
  schemaStride : 3+3*r≤M
  schemas : C.edges*(3+3*r)≤M
  double : 2*r≤M
  requestStride : 1+2*r≤M
  seeds : C.seedCount*(1+2*r)≤M
  tests : C.testCount*(1+2*r)≤M

def initAtoms : List (Atom Reg Arr) := [
  .arrayLength (cr .length) (ca .input),.const (cr .cursor) 0,.const (cr .valid) 1,
  .const (wr .zero) 0,.const (wr .one) 1,.const (wr .two) 2,.const (wr .three) 3,
  .const (wr .count) 5,.const (wr .stride) 5,.const (wr .unaryCount) 5]
def loadHeaderAtoms : List (Atom Reg Arr) := [
  .const (wr .index) 0,.read (wr .types) (wa .header) (wr .index),
  .const (wr .index) 1,.read (wr .coordinates) (wa .header) (wr .index),
  .const (wr .index) 2,.read (wr .edges) (wa .header) (wr .index),
  .const (wr .index) 3,.read (wr .seeds) (wa .header) (wr .index),
  .const (wr .index) 4,.read (wr .tests) (wa .header) (wr .index)]
def kindAtoms : List (Atom Reg Arr) := [
  .copy (wr .count) (wr .types),.copy (wr .stride) (wr .types),.const (wr .unaryCount) 0]
def schemaAtoms : List (Atom Reg Arr) := [
  .binary .mul (wr .stride) (wr .coordinates) (wr .three),
  .binary .add (wr .stride) (wr .stride) (wr .three),
  .binary .mul (wr .count) (wr .edges) (wr .stride),.const (wr .unaryCount) 2]
def requestAtoms (which : WorkReg) : List (Atom Reg Arr) := [
  .binary .mul (wr .stride) (wr .coordinates) (wr .two),
  .binary .add (wr .stride) (wr .stride) (wr .one),
  .binary .mul (wr .count) (wr which) (wr .stride),.const (wr .unaryCount) 1]

theorem init_runs (w : List Bool) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (room : 5≤M) (input : S.array (ca .input)=w.map bitNat) :
    Runs (storageBound Reg Arr M) (atoms initAtoms) S 10 (applyAtoms initAtoms S) ∧
      (applyAtoms initAtoms S).Bounded M ∧ Ready w (applyAtoms initAtoms S) ∧
      (applyAtoms initAtoms S).scalar (cr .cursor)=0 ∧
      (applyAtoms initAtoms S).scalar (wr .count)=5 ∧
      (applyAtoms initAtoms S).scalar (wr .stride)=5 ∧
      (applyAtoms initAtoms S).scalar (wr .unaryCount)=5 := by
  have valid : ValidAtoms M initAtoms S := by
    simp [initAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult]
    omega
  obtain ⟨run,hU⟩ := atoms_runs bounded initAtoms valid
  refine ⟨run,hU,?_,?_,?_,?_,?_⟩
  · constructor <;> simp [initAtoms,applyAtoms,Atom.apply,Store.setScalar,Store.setArray,input]
  all_goals simp [initAtoms,applyAtoms,Atom.apply,Store.setScalar,Store.setArray]

theorem loadHeader_runs (C : Circuit T r) (w : List Bool) (S : State) (M : ℕ)
    (bounded : S.Bounded M) (room : 5≤M) (ready : Ready w S)
    (header : S.array (wa .header)=List.ofFn (headerValues C)) :
    Runs (storageBound Reg Arr M) (atoms loadHeaderAtoms) S 10 (applyAtoms loadHeaderAtoms S) ∧
      (applyAtoms loadHeaderAtoms S).Bounded M ∧ Ready w (applyAtoms loadHeaderAtoms S) ∧
      Metadata C (applyAtoms loadHeaderAtoms S) ∧
      (applyAtoms loadHeaderAtoms S).scalar (cr .cursor)=S.scalar (cr .cursor) ∧
      (applyAtoms loadHeaderAtoms S).array=S.array := by
  have valid : ValidAtoms M loadHeaderAtoms S := by
    simp [loadHeaderAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,header]
    omega
  obtain ⟨run,hU⟩ := atoms_runs bounded loadHeaderAtoms valid
  refine ⟨run,hU,?_,?_,?_,?_⟩
  · rcases ready with ⟨hl,hv,hi,hz,ho,ht,hth⟩
    constructor <;> simp [loadHeaderAtoms,applyAtoms,Atom.apply,Store.setScalar,hl,hv,hi,hz,ho,ht,hth]
  · constructor <;> simp [loadHeaderAtoms,applyAtoms,Atom.apply,Store.setScalar,header,headerValues]
  · simp [loadHeaderAtoms,applyAtoms,Atom.apply,Store.setScalar]
  · rfl

theorem Ready.of_stage {w : List Bool} {S U : State}
    (h : Ready w S) (left : U.left.scalar=S.left.scalar)
    (length : U.scalar (cr .length)=w.length) (valid : U.scalar (cr .valid)=1)
    (input : U.array (ca .input)=w.map bitNat) : Ready w U := by
  have hs (a : WorkReg) : U.scalar (wr a)=S.scalar (wr a) := congrFun left a
  exact ⟨length,valid,input,(hs _).trans h.zero,(hs _).trans h.one,(hs _).trans h.two,(hs _).trans h.three⟩

theorem Metadata.of_stage {C : Circuit T r} {S U : State}
    (h : Metadata C S) (left : U.left.scalar=S.left.scalar) : Metadata C U := by
  have hs (a : WorkReg) : U.scalar (wr a)=S.scalar (wr a) := congrFun left a
  exact ⟨(hs _).trans h.types,(hs _).trans h.coordinates,(hs _).trans h.edges,
    (hs _).trans h.seeds,(hs _).trans h.tests⟩

def PureControls (as : List (Atom Reg Arr)) : Prop := ∀ S : State,
  (applyAtoms as S).array=S.array ∧ ∀a : Reg,
    a≠wr .count → a≠wr .stride → a≠wr .unaryCount → (applyAtoms as S).scalar a=S.scalar a

theorem kind_pure : PureControls kindAtoms := by
  intro S
  refine ⟨rfl,?_⟩
  intro a h₁ h₂ h₃
  simp [kindAtoms,applyAtoms,Atom.apply,Store.setScalar,h₁,h₂,h₃]
theorem schema_pure : PureControls schemaAtoms := by
  intro S
  refine ⟨rfl,?_⟩
  intro a h₁ h₂ h₃
  simp [schemaAtoms,applyAtoms,Atom.apply,Store.setScalar,h₁,h₂,h₃]
theorem request_pure (which : WorkReg) : PureControls (requestAtoms which) := by
  intro S
  refine ⟨rfl,?_⟩
  intro a h₁ h₂ h₃
  simp [requestAtoms,applyAtoms,Atom.apply,Store.setScalar,h₁,h₂,h₃]

theorem PureControls.ready {as : List (Atom Reg Arr)} (h : PureControls as)
    {w : List Bool} {S : State} (ready : Ready w S) : Ready w (applyAtoms as S) := by
  have hs := (h S).2
  refine ⟨(hs _ (by decide) (by decide) (by decide)).trans ready.length,
    (hs _ (by decide) (by decide) (by decide)).trans ready.valid,?_,
    (hs _ (by decide) (by decide) (by decide)).trans ready.zero,
    (hs _ (by decide) (by decide) (by decide)).trans ready.one,
    (hs _ (by decide) (by decide) (by decide)).trans ready.two,
    (hs _ (by decide) (by decide) (by decide)).trans ready.three⟩
  rw [(h S).1]
  exact ready.input

theorem PureControls.metadata {as : List (Atom Reg Arr)} (h : PureControls as)
    {C : Circuit T r} {S : State} (metadata : Metadata C S) : Metadata C (applyAtoms as S) := by
  have hs := (h S).2
  exact ⟨(hs _ (by decide) (by decide) (by decide)).trans metadata.types,
    (hs _ (by decide) (by decide) (by decide)).trans metadata.coordinates,
    (hs _ (by decide) (by decide) (by decide)).trans metadata.edges,
    (hs _ (by decide) (by decide) (by decide)).trans metadata.seeds,
    (hs _ (by decide) (by decide) (by decide)).trans metadata.tests⟩

theorem PureControls.cursor {as : List (Atom Reg Arr)} (h : PureControls as) (S : State) :
    (applyAtoms as S).scalar (cr .cursor)=S.scalar (cr .cursor) :=
  (h S).2 _ (by decide) (by decide) (by decide)

theorem kind_prepared (C : Circuit T r) (S : State) (M : ℕ) (metadata : Metadata C S) :
    ValidAtoms M kindAtoms S ∧
    (applyAtoms kindAtoms S).scalar (wr .stride)=FiniteCode.size T ∧
    (applyAtoms kindAtoms S).scalar (wr .unaryCount)=0 ∧
    (applyAtoms kindAtoms S).scalar (wr .count)=FiniteCode.size T := by
  simp [kindAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,applyAtoms,Atom.apply,Store.setScalar,metadata.types]

theorem schema_prepared (C : Circuit T r) (w : List Bool) (S : State) (M : ℕ)
    (metadata : Metadata C S) (ready : Ready w S) (budget : Budget C M) :
    ValidAtoms M schemaAtoms S ∧
    (applyAtoms schemaAtoms S).scalar (wr .stride)=3+3*r ∧
    (applyAtoms schemaAtoms S).scalar (wr .unaryCount)=2 ∧
    (applyAtoms schemaAtoms S).scalar (wr .count)=C.edges*(3+3*r) := by
  simp [schemaAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,applyAtoms,Atom.apply,BinaryOp.eval,
    Store.setScalar,metadata.coordinates,metadata.edges,ready.three,Nat.mul_comm,Nat.add_comm,
    budget.triple,budget.schemaStride,budget.schemas]
  have h₁ := budget.triple
  have h₂ := budget.schemaStride
  have h₃ : C.edges*(3+r*3)≤M := by simpa [Nat.mul_comm] using budget.schemas
  have h₄ := budget.room
  omega

theorem request_prepared (C : Circuit T r) (w : List Bool) (S : State) (M count : ℕ)
    (which : WorkReg) (hc : S.scalar (wr which)=count) (hwhich : which≠.stride)
    (metadata : Metadata C S) (ready : Ready w S) (budget : Budget C M) (bound : count*(1+2*r)≤M) :
    ValidAtoms M (requestAtoms which) S ∧
    (applyAtoms (requestAtoms which) S).scalar (wr .stride)=1+2*r ∧
    (applyAtoms (requestAtoms which) S).scalar (wr .unaryCount)=1 ∧
    (applyAtoms (requestAtoms which) S).scalar (wr .count)=count*(1+2*r) := by
  simp [requestAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,applyAtoms,Atom.apply,BinaryOp.eval,
    Store.setScalar,metadata.coordinates,ready.two,ready.one,Nat.mul_comm,Nat.add_comm,hwhich,hc,
    budget.double,budget.requestStride,bound]
  have h₀ : count*(1+r*2)≤M := by simpa [Nat.mul_comm] using bound
  have h₁ := budget.double
  have h₂ := budget.requestStride
  have h₃ := budget.room
  omega

end GroupWL.MachinePrograms.CircuitParserStages
