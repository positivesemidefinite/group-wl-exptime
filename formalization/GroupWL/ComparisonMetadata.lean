import GroupWL.SourceFiniteCodes
import GroupWL.MachinePrograms.EvaluationAssemblyCorrectness

/-! Numeric comparison records consumed by the uniform site-and-square builder. -/
namespace GroupWL.ComparisonMetadata
open SourceLayout

structure Table where
  types : ℕ
  comparisons : ℕ
  coordinates : ℕ
  dimensions : List ℕ
  source : List ℕ
  target : List ℕ
  sourceForm : List ℕ
  targetForm : List ℕ
  domain : List ℕ
  permutation : List ℕ

variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r)

def unit (t : T) (k : Fin 2) : Fin (C.dim t) → ZMod p := fun i => if i.val=k.val then 1 else 0

def dimensions : List ℕ := List.ofFn (fun i : Fin (FiniteCode.size T) => C.dim (FiniteCode.equiv.symm i))
def source : List ℕ := List.ofFn (fun i : Fin (FiniteCode.size E) =>
  (FiniteCode.equiv (C.source (FiniteCode.equiv.symm i))).val)
def target : List ℕ := List.ofFn (fun i : Fin (FiniteCode.size E) =>
  (FiniteCode.equiv (C.target (FiniteCode.equiv.symm i))).val)
def sourceForm : List ℕ := (List.ofFn (fun i : Fin (FiniteCode.size E) =>
  let e := (FiniteCode.equiv (α:=E)).symm i
  List.ofFn (fun k : Fin 2 => (C.sourceForm e (unit p C (C.source e) k)).val))).flatten
def targetForm : List ℕ := (List.ofFn (fun i : Fin (FiniteCode.size E) =>
  let e := (FiniteCode.equiv (α:=E)).symm i
  List.ofFn (fun k : Fin 2 => (C.targetForm e (unit p C (C.target e) k)).val))).flatten
def domain : List ℕ := MachinePrograms.EvaluationAssembly.entries3
  (fun (i : Fin (FiniteCode.size E)) (j : Fin r) (a : Fin 2) =>
    if finTwoEquiv a ∈ C.domain (FiniteCode.equiv.symm i) j then 1 else 0)
def permutation : List ℕ := (List.ofFn (fun i : Fin (FiniteCode.size E) =>
  List.ofFn (fun j : Fin r => if C.permutation (FiniteCode.equiv.symm i) j false then 1 else 0))).flatten

def ofComparison : Table where
  types := FiniteCode.size T
  comparisons := FiniteCode.size E
  coordinates := r
  dimensions := dimensions p C
  source := source p C
  target := target p C
  sourceForm := sourceForm p C
  targetForm := targetForm p C
  domain := domain p C
  permutation := permutation p C

@[simp] theorem dimensions_length : (dimensions p C).length=FiniteCode.size T := by simp [dimensions]
@[simp] theorem source_length : (source p C).length=FiniteCode.size E := by simp [source]
@[simp] theorem target_length : (target p C).length=FiniteCode.size E := by simp [target]
@[simp] theorem sourceForm_length : (sourceForm p C).length=FiniteCode.size E*2 := by
  simp [sourceForm,List.length_flatten,List.sum_ofFn]
@[simp] theorem targetForm_length : (targetForm p C).length=FiniteCode.size E*2 := by
  simp [targetForm,List.length_flatten,List.sum_ofFn]
@[simp] theorem domain_length : (domain p C).length=FiniteCode.size E*r*2 := by
  simp [domain,MachinePrograms.EvaluationAssembly.entries3,Nat.mul_assoc]
@[simp] theorem permutation_length : (permutation p C).length=FiniteCode.size E*r := by
  simp [permutation,List.length_flatten,List.sum_ofFn]

end GroupWL.ComparisonMetadata
