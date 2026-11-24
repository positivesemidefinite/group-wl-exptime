import GroupWL.MachinePrograms.SourceRadicalColumnBounds
import GroupWL.MachinePrograms.ArrayTabulation

/-! The fixed outer loop materializes all readout radicals in one padded
block-by-readout array, with one separate width per readout. -/
namespace GroupWL.MachinePrograms.SourceRadicalTables
open NatArrayLanguage
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

inductive Admin where
  | blocks | readouts | index | remaining | one | zero | dimension | stride | size
  deriving DecidableEq,Fintype
inductive OuterArr where | scope | coefficients | dimensions | output | widths deriving DecidableEq,Fintype
abbrev Reg := SourceRadicalColumn.Reg ⊕ Admin
abbrev Arr := SourceRadicalColumn.Arr ⊕ OuterArr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

abbrev nr (r : SourceNeighbors.Reg) : Reg := .inl (.inl (.inl (.inl r)))
abbrev na (a : SourceNeighbors.Arr) : Arr := .inl (.inl (.inl (.inl a)))
abbrev rr (r : SourceRelationMatrix.Reg) : Reg := .inl (.inl (.inl (.inr r)))
abbrev ra (a : SourceRelationMatrix.Arr) : Arr := .inl (.inl (.inl (.inr a)))
abbrev kr (r : KernelProgram.Reg) : Reg := .inl (.inl (.inr r))
abbrev sr (r : MatrixScatter.Reg) : Reg := .inl (.inr r)
abbrev sa (a : MatrixScatter.Arr) : Arr := .inl (.inr a)

def setup : List (Atom Reg Arr) := [
  .read (.inr .dimension) (.inr .dimensions) (.inr .index),
  .copy (nr .length) (.inr .blocks),.copy (nr .stride) (.inr .readouts),.copy (nr .offset) (.inr .index),
  .copy (rr .readouts) (.inr .readouts),.copy (rr .readout) (.inr .index),.copy (rr .total) (.inr .dimension),
  .copy (kr (KernelProgram.wr .rows)) (.inr .dimension),
  .copyArray (na .input) (.inr .scope),.copyArray (ra .coefficients) (.inr .coefficients),
  .copy (sr .stride) (.inr .stride),.binary .mul (sr .offset) (.inr .index) (.inr .blocks),
  .copyArray (sa .output) (.inr .output)]

def finish : List (Atom Reg Arr) := [
  .copyArray (.inr .output) (sa .output),
  .write (.inr .widths) (.inr .index) (kr (KernelProgram.wr .width))]

def body (p : ℕ) : Code := .seq (atoms setup)
  (.seq ((SourceRadicalColumn.program p).map Sum.inl Sum.inl) (atoms finish))

def initialAtoms : List (Atom Reg Arr) := [
  .const (.inr .one) 1,.const (.inr .zero) 0,
  .binary .mul (.inr .stride) (.inr .readouts) (.inr .blocks),
  .binary .mul (.inr .size) (.inr .blocks) (.inr .stride),
  .allocate (.inr .output) (.inr .size) (.inr .zero),
  .allocate (.inr .widths) (.inr .readouts) (.inr .zero)]

def program (p : ℕ) : Code := .seq (atoms initialAtoms)
  (countedLoop (.inr .index) (.inr .remaining) (.inr .readouts) (.inr .one) (body p))

def width (p : ℕ) (scope coefficients dimensions : List ℕ) (b r j : ℕ) : ℕ :=
  (SourceRadicalClient.data p scope coefficients b r j (dimensions[j]?.getD 0)).width

def update (p : ℕ) (scope coefficients dimensions initial : List ℕ) (b r j : ℕ) : List ℕ :=
  SourceRadicalColumn.update p scope coefficients initial b r j (dimensions[j]?.getD 0) (r*b) (j*b)

def collect (p : ℕ) (scope coefficients dimensions : List ℕ) (b r : ℕ) : ℕ → List ℕ
  | 0 => List.replicate (b*r*b) 0
  | j+1 => update p scope coefficients dimensions (collect p scope coefficients dimensions b r j) b r j

@[simp] theorem update_length (p : ℕ) (scope coefficients dimensions initial : List ℕ) (b r j : ℕ) :
    (update p scope coefficients dimensions initial b r j).length=initial.length :=
  MatrixScatter.scatter_length _ _ _ _ _ _ _

@[simp] theorem collect_length (p : ℕ) (scope coefficients dimensions : List ℕ) (b r i : ℕ) :
    (collect p scope coefficients dimensions b r i).length=b*r*b := by
  induction i with
  | zero => simp [collect]
  | succ i ih => simpa [collect] using ih

def Ready (scope coefficients dimensions : List ℕ) (b r : ℕ) (S : State) : Prop :=
  S.array (.inr .scope)=scope ∧ S.array (.inr .coefficients)=coefficients ∧
  S.array (.inr .dimensions)=dimensions ∧ S.scalar (.inr .blocks)=b ∧ S.scalar (.inr .readouts)=r ∧
  S.scalar (.inr .stride)=r*b ∧ (S.array (.inr .output)).length=b*r*b ∧ (S.array (.inr .widths)).length=r

theorem body_runs (p : ℕ) [NeZero p] (scope coefficients dimensions : List ℕ) (b r M : ℕ)
    (hp : 1<p) (hscope : b*r≤scope.length) (hcoeff : b*r*2≤coefficients.length)
    (values : ∀ x∈coefficients,x<p) (hdims : r≤dimensions.length)
    (dims : ∀ i<r,dimensions[i]?.getD 0≤2)
    (hM : 2*b+2≤M) (hpM : p*p+p≤M) (hbM : b*b≤M)
    (S : State) (bounded : S.Bounded M) (ready : Ready scope coefficients dimensions b r S)
    (hi : S.scalar (.inr .index)<r) :
    ∃ t≤290*(b+p+4)^4+15, ∃ T, Runs (storageBound Reg Arr M) (body p) S t T ∧ T.Bounded M ∧
      Ready scope coefficients dimensions b r T ∧
      T.array (.inr .output)=update p scope coefficients dimensions (S.array (.inr .output)) b r (S.scalar (.inr .index)) ∧
      T.array (.inr .widths)=(S.array (.inr .widths)).set (S.scalar (.inr .index))
        (width p scope coefficients dimensions b r (S.scalar (.inr .index))) ∧
      ∀ a : Admin, a≠.dimension → T.scalar (.inr a)=S.scalar (.inr a) := by
  rcases ready with ⟨hsc,hco,hdi,hb,hr,hs,hout,hws⟩
  have hidx : S.scalar (.inr .index)<dimensions.length := hi.trans_le hdims
  have hprod : S.scalar (.inr .index)*b≤M := by
    have h := bounded.1 (.inr .stride)
    rw [hs] at h
    exact (Nat.mul_le_mul_right b hi.le).trans h
  have valid : ValidAtoms M setup S := by
    simp [setup,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,hdi,hb,hidx,hprod]
  obtain ⟨prepared,hUB⟩ := atoms_runs bounded setup valid
  let U := applyAtoms setup S
  have uscope : U.left.left.left.left.array .input=scope := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.left,hsc]
  have ublocks : U.left.left.left.left.scalar .length=b := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.left,hb]
  have ustride : U.left.left.left.left.scalar .stride=r := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.left,hr]
  have uoffset : U.left.left.left.left.scalar .offset=S.scalar (.inr .index) := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.left]
  have uc : U.left.left.left.right.array .coefficients=coefficients := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.left,Store.right,hco]
  have ur : U.left.left.left.right.scalar .readouts=r := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.left,Store.right,hr]
  have uj : U.left.left.left.right.scalar .readout=S.scalar (.inr .index) := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.left,Store.right]
  have ud : U.left.left.left.right.scalar .total=dimensions[S.scalar (.inr .index)]?.getD 0 := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.left,Store.right,hdi]
  have uk : U.left.left.right.scalar (KernelProgram.wr .rows)=dimensions[S.scalar (.inr .index)]?.getD 0 := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.left,Store.right,hdi]
  have uout : U.left.right.array .output=S.array (.inr .output) := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.left,Store.right]
  have us : U.left.right.scalar .stride=r*b := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.left,Store.right,hs]
  have uoff : U.left.right.scalar .offset=S.scalar (.inr .index)*b := by
    simp [U,setup,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,Store.left,Store.right,hb]
  obtain ⟨t,ht,V,column,hVB,hVout,hVwidth⟩ := SourceRadicalColumn.program_runs p scope coefficients
    (S.array (.inr .output)) b r (S.scalar (.inr .index)) (dimensions[S.scalar (.inr .index)]?.getD 0)
    (r*b) (S.scalar (.inr .index)*b) M hp hi (dims _ hi) hscope hcoeff values hM hpM hbM
    U.left hUB.left uscope ublocks ustride uoffset uc ur uj ud uk uout us uoff
    (fun i hi' => by rw [hout]; exact SourceRadicalColumn.target_bound p scope coefficients b r _ _ i hp hi hi')
  have columnRun := column.left_bounded hUB
  let W := V.join U.right
  have hWB : W.Bounded M := hVB.join hUB.right
  have windex : W.scalar (.inr .index)=S.scalar (.inr .index) := rfl
  have wwidths : W.array (.inr .widths)=S.array (.inr .widths) := rfl
  have finishValid : ValidAtoms M finish W := by
    simp [finish,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setArray,windex,wwidths,hws,hi]
  obtain ⟨last,hTB⟩ := atoms_runs hWB finish finishValid
  let T := applyAtoms finish W
  have run : Runs (storageBound Reg Arr M) (body p) S (13+(t+2)) T := prepared.seq (columnRun.seq last)
  have scalar (a : Admin) (ha : a≠.dimension) : T.scalar (.inr a)=S.scalar (.inr a) := by
    cases a <;> first | rfl | exact False.elim (ha rfl)
  have arrays (a : OuterArr) (ha : a≠.output) (hb' : a≠.widths) : T.array (.inr a)=S.array (.inr a) := by
    cases a <;> first | rfl | exact False.elim (ha rfl) | exact False.elim (hb' rfl)
  have tout : T.array (.inr .output)=update p scope coefficients dimensions (S.array (.inr .output)) b r (S.scalar (.inr .index)) := by
    simpa [T,finish,applyAtoms,Atom.apply,Store.setArray,W,Store.join,update,
      -Sum.elim_update_left,-Sum.elim_update_right] using hVout
  have twidths : T.array (.inr .widths)=(S.array (.inr .widths)).set (S.scalar (.inr .index))
        (width p scope coefficients dimensions b r (S.scalar (.inr .index))) := by
    simp [T,finish,applyAtoms,Atom.apply,Store.setArray,windex,wwidths]
    exact congrArg ((S.array (.inr .widths)).set (S.scalar (.inr .index))) hVwidth
  refine ⟨13+(t+2),?_,T,run,hTB,?_,tout,twidths,scalar⟩
  · have hcost := ht.trans (SourceRadicalColumn.cost_le p scope coefficients b r _ _ hp (dims _ hi))
    omega
  · refine ⟨(arrays .scope (by decide) (by decide)).trans hsc,
      (arrays .coefficients (by decide) (by decide)).trans hco,
      (arrays .dimensions (by decide) (by decide)).trans hdi,
      (scalar .blocks (by decide)).trans hb,(scalar .readouts (by decide)).trans hr,
      (scalar .stride (by decide)).trans hs,?_,?_⟩
    · rw [tout,update_length,hout]
    · rw [twidths,List.length_set,hws]

end GroupWL.MachinePrograms.SourceRadicalTables
