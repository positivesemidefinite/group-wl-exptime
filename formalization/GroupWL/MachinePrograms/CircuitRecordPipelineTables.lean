import GroupWL.MachinePrograms.CircuitMetadataTable
import GroupWL.MachinePrograms.KernelToTensor
import GroupWL.CircuitMetadataCorrectness

/-! Seven fixed expression-table programs sharing the decoded circuit and packed gate ports. -/
namespace GroupWL.MachinePrograms.CircuitRecordPipeline
open NatArrayLanguage NatArrayExpressions CircuitMetadataValues

open CircuitMetadataExpressions (Field)
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536

abbrev BaseReg := CircuitMetadataExpressions.Reg ⊕ Field
abbrev Base := Store BaseReg CircuitMetadataExpressions.Input

def baseData (S : Base) : Store CircuitMetadataExpressions.Reg CircuitMetadataExpressions.Input := ⟨fun r => S.scalar (.inl r), S.array⟩

def fieldSize (D : Data) : Field → ℕ
  | .dimension => D.realTypes
  | .source | .target => D.comparisons
  | .sourceForm | .targetForm => D.comparisons * 2
  | .domain => D.comparisons * D.coordinates * 2
  | .permutation => D.comparisons * D.coordinates

def fieldWord (D : Data) (f : Field) : List ℕ :=
  List.ofFn (fun i : Fin (fieldSize D f) => CircuitMetadataExpressions.value D f i.val)

def tableWord (C : ComparisonMetadata.Table) : Field → List ℕ
  | .dimension => C.dimensions
  | .source => C.source
  | .target => C.target
  | .sourceForm => C.sourceForm
  | .targetForm => C.targetForm
  | .domain => C.domain
  | .permutation => C.permutation

theorem fieldWord_eq (D : Data) (f : Field) : fieldWord D f = tableWord D.table f := by
  have div (x : ℕ) {n : ℕ} (k : Fin n) : (x*n+k.val)/n=x := by
    rw [Nat.mul_comm x n,Nat.mul_add_div (Nat.zero_lt_of_lt k.isLt),Nat.div_eq_of_lt k.isLt,Nat.add_zero]
  cases f <;> simp only [fieldWord,fieldSize,tableWord,Data.table,CircuitMetadataExpressions.value,
    EvaluationAssembly.entries3, Fin.divNat, Fin.modNat, Nat.div_div_eq_div_mul, Nat.mul_comm 2 D.coordinates]
  all_goals simp [List.ofFn_mul,div,Nat.mod_eq_of_lt (Fin.isLt _)]

abbrev ExprReg (f : Field) := Registers CircuitMetadataExpressions.Reg (CircuitMetadataExpressions.expr f).need

def Reg : List Field → Type
  | [] => BaseReg
  | f :: fs => Reg fs ⊕ ExprReg f

def Arr : List Field → Type
  | [] => CircuitMetadataExpressions.Input
  | _ :: fs => Arr fs ⊕ CircuitMetadataExpressions.Arr

instance instRegDec : ∀ fs, DecidableEq (Reg fs)
  | [] => inferInstanceAs (DecidableEq BaseReg)
  | f :: fs => letI := instRegDec fs; inferInstanceAs (DecidableEq (Reg fs ⊕ ExprReg f))
instance instArrDec : ∀ fs, DecidableEq (Arr fs)
  | [] => inferInstanceAs (DecidableEq CircuitMetadataExpressions.Input)
  | _ :: fs => letI := instArrDec fs; inferInstanceAs (DecidableEq (Arr fs ⊕ CircuitMetadataExpressions.Arr))
noncomputable instance instRegFin : ∀ fs, Fintype (Reg fs)
  | [] => inferInstanceAs (Fintype BaseReg)
  | f :: fs => letI := instRegFin fs; inferInstanceAs (Fintype (Reg fs ⊕ ExprReg f))
noncomputable instance instArrFin : ∀ fs, Fintype (Arr fs)
  | [] => inferInstanceAs (Fintype CircuitMetadataExpressions.Input)
  | _ :: fs => letI := instArrFin fs; inferInstanceAs (Fintype (Arr fs ⊕ CircuitMetadataExpressions.Arr))

def baseReg : (fs : List Field) → BaseReg → Reg fs
  | [], r => r
  | _ :: fs, r => .inl (baseReg fs r)
def baseArray : (fs : List Field) → CircuitMetadataExpressions.Input → Arr fs
  | [], a => a
  | _ :: fs, a => .inl (baseArray fs a)
def outputArray (f : Field) : (fs : List Field) → Arr fs
  | [] => .kinds
  | g :: fs => if f = g then .inr (.inr ()) else .inl (outputArray f fs)

def extractBase (fs : List Field) (S : Store (Reg fs) (Arr fs)) : Base :=
  ⟨fun r => S.scalar (baseReg fs r), fun a => S.array (baseArray fs a)⟩

def scalarWire (fs : List Field) (f : Field) : ExprReg f → Ports.Scalar (Reg fs) (Arr fs)
  | .inr _ => .literal 0
  | .inl .length => .scalar (baseReg fs (.inr f))
  | .inl r => .scalar (baseReg fs (.inl r))
def arrayWire (fs : List Field) : CircuitMetadataExpressions.Arr → Option (Arr fs)
  | .inl a => some (baseArray fs a)
  | .inr _ => none

noncomputable def tables : (fs : List Field) → NatArrayLanguage.Program (Reg fs) (Arr fs)
  | [] => .skip
  | f :: fs => Ports.thenRun (tables fs) (scalarWire fs f) (arrayWire fs) (CircuitMetadataExpressions.program f)

def tableTime (B : ℕ) : List Field → ℕ
  | [] => 0
  | f :: fs => tableTime B fs + (Fintype.card (ExprReg f) + Fintype.card CircuitMetadataExpressions.Arr + (B * ((CircuitMetadataExpressions.expr f).cost + 4) + 6))

structure Prepared (D : Data) (B M : ℕ) (S : Base) : Prop where
  data : CircuitMetadataExpressions.readData (baseData S) = D
  lengths : ∀ a, S.scalar (.inl (CircuitMetadataExpressions.sizeRegister a)) = (S.array a).length
  sizes : ∀ f, S.scalar (.inr f) = fieldSize D f
  room : 6 ≤ B
  scalars : ∀ r, CircuitMetadataExpressions.static r → S.scalar (.inl r) ≤ B
  arrays : ∀ a x, x ∈ S.array a → x ≤ B
  sizeBound : ∀ f, fieldSize D f ≤ B
  budget : ∀ f, (B+2)^(2*((CircuitMetadataExpressions.entry f).expression CircuitMetadataExpressions.sizeRegister).cost) ≤ M

private theorem literals (fs : List Field) (f : Field) (i : ExprReg f) (k : ℕ)
    (h : scalarWire fs f i = .literal k) (M : ℕ) : k ≤ M := by
  cases i with
  | inl i => cases i <;> contradiction
  | inr i => cases h; exact Nat.zero_le _

theorem tables_runs (fs : List Field) (D : Data) (B M : ℕ) (S : Store (Reg fs) (Arr fs))
    (bounded : S.Bounded M) (pre : Prepared D B M (extractBase fs S)) :
    ∃ t ≤ tableTime B fs, ∃ U, Runs (storageBound (Reg fs) (Arr fs) M) (tables fs) S t U ∧
      U.Bounded M ∧ extractBase fs U = extractBase fs S ∧
      ∀ f ∈ fs, U.array (outputArray f fs) = fieldWord D f := by
  induction fs with
  | nil =>
    exact ⟨0,le_rfl,S,.skip (Store.size_le_of_bounded bounded),bounded,rfl,by simp⟩
  | cons f fs ih =>
    obtain ⟨t,ht,P,run,hP,hbase,prev⟩ := ih S.left bounded.left pre
    let X := Ports.target (scalarWire fs f) (arrayWire fs) P
    have wire := Ports.code_runs (scalarWire fs f) (arrayWire fs) P S.right M
      (hP.join bounded.right) (fun i k h => literals fs f i k h M)
    have hp : Prepared D B M (extractBase fs P) := hbase ▸ pre
    let base := baseData (extractBase fs P)
    have frame : CircuitMetadataExpressions.Frame base (inputs X) := by
      constructor
      · intro i hi
        cases i <;> first | exact (hi.1 rfl).elim | rfl
      · intro a; rfl
    obtain ⟨u,hu,Q,last,hQ,_,out⟩ := CircuitMetadataExpressions.program_runs f base B M (fieldSize D f) hp.room hp.lengths
      hp.scalars hp.arrays (hp.sizeBound f) (hp.budget f) X wire.2 frame (hp.sizes f)
    have full := Ports.thenRun_runs (tables fs) (scalarWire fs f) (arrayWire fs) (CircuitMetadataExpressions.program f)
      S.left P S.right Q M t u bounded.left hP bounded.right (fun i k h => literals fs f i k h M) run last
    rw [Store.join_left_right] at full
    refine ⟨_,Nat.add_le_add ht (Nat.add_le_add_left (hu.trans (Nat.add_le_add_right
        (Nat.mul_le_mul_right _ (hp.sizeBound f)) _)) _),P.join Q,full,hP.join hQ,hbase,?_⟩
    intro g hg
    by_cases he : g = f
    · subst g
      have hd : CircuitMetadataExpressions.readData base = D := hp.data
      simpa [outputArray,fieldWord,hd] using out
    · simpa only [outputArray,if_neg he,Store.join_array_left] using prev g (List.mem_of_ne_of_mem he hg)

end GroupWL.MachinePrograms.CircuitRecordPipeline
