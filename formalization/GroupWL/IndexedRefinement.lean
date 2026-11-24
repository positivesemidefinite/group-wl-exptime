import GroupWL.CompressedRefinement
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange

/-! Explicit natural-number array addresses for equality-matrix refinement. -/
namespace GroupWL.IndexedRefinement

open CompressedRefinement
variable {n k b : ℕ}

def read (xs : List ℕ) (i : ℕ) : ℕ := xs[i]?.getD 0
def boolNat (x : Bool) : ℕ := if x then 1 else 0

@[simp] theorem boolNat_eq_one (x : Bool) : boolNat x=1 ↔ x=true := by cases x <;> decide
@[simp] theorem boolNat_le_one (x : Bool) : boolNat x≤1 := by cases x <;> decide

def matrixWord (R : Finset (Fin n × Fin n)) : List ℕ :=
  List.ofFn (fun i : Fin (n*n) => boolNat (decide (finProdFinEquiv.symm i ∈ R)))

@[simp] theorem matrixWord_length (R : Finset (Fin n × Fin n)) :
    (matrixWord R).length=n*n := List.length_ofFn

theorem matrixWord_read (R : Finset (Fin n × Fin n)) (a c : Fin n) :
    read (matrixWord R) (c.val+n*a.val)=boolNat (decide ((a,c) ∈ R)) := by
  have hi : c.val+n*a.val < n*n := (finProdFinEquiv (a,c)).isLt
  simp only [read,matrixWord,List.getElem?_ofFn,dif_pos hi,Option.getD_some]
  change boolNat (decide (finProdFinEquiv.symm (finProdFinEquiv (a,c)) ∈ R))=_
  rw [Equiv.symm_apply_apply]

structure Data (n k b : ℕ) where
  positive : 0 < n
  fanout : Fin n → ℕ
  fanout_le : ∀ a,fanout a≤b
  target : Fin n → Fin b → Fin k → Fin n

def Data.neighbors (D : Data n k b) (a : Fin n) : List (Fin k → Fin n) :=
  List.ofFn (fun x : Fin (D.fanout a) => D.target a ⟨x.val,lt_of_lt_of_le x.isLt (D.fanout_le a)⟩)

def Data.edges (D : Data n k b) (a : Fin n) : Multiset (Fin k → Fin n) := D.neighbors a
def Data.fanoutWord (D : Data n k b) : List ℕ := List.ofFn D.fanout

def Data.targetWord (D : Data n k b) : List ℕ :=
  List.ofFn (fun z : Fin ((n*b)*k) =>
    let ai := finProdFinEquiv.symm z
    let ax := finProdFinEquiv.symm ai.1
    (D.target ax.1 ax.2 ai.2).val)

@[simp] theorem Data.fanoutWord_length (D : Data n k b) : D.fanoutWord.length=n := List.length_ofFn
@[simp] theorem Data.targetWord_length (D : Data n k b) : D.targetWord.length=(n*b)*k := List.length_ofFn

@[simp] theorem Data.fanoutWord_read (D : Data n k b) (a : Fin n) :
    read D.fanoutWord a.val=D.fanout a := by
  simp only [read,Data.fanoutWord,List.getElem?_ofFn,dif_pos a.isLt,Option.getD_some]

theorem Data.targetWord_read (D : Data n k b) (a : Fin n) (x : Fin b) (i : Fin k) :
    read D.targetWord (i.val+k*(x.val+b*a.val))=(D.target a x i).val := by
  have hi : i.val+k*(x.val+b*a.val) < (n*b)*k :=
    (finProdFinEquiv (finProdFinEquiv (a,x),i)).isLt
  simp only [read,Data.targetWord,List.getElem?_ofFn,dif_pos hi,Option.getD_some]
  have hout : finProdFinEquiv.symm (⟨i.val+k*(x.val+b*a.val),hi⟩ : Fin ((n*b)*k))=
      (finProdFinEquiv (a,x),i) := (@finProdFinEquiv (n*b) k).symm_apply_apply (finProdFinEquiv (a,x),i)
  rw [hout]
  simp only [Equiv.symm_apply_apply]

/-- The vector enumeration uses ordinary quotient and remainder. -/
def digit (n value index : ℕ) : ℕ := value/n^index%n

theorem digit_equiv (v : Fin (n^k)) (i : Fin k) :
    digit n v.val i.val=(finFunctionFinEquiv.symm v i).val := rfl

def vectorWord (n k value : ℕ) : List ℕ := List.ofFn (fun i : Fin k => digit n value i.val)

@[simp] theorem vectorWord_length (n k value : ℕ) : (vectorWord n k value).length=k :=
  List.length_ofFn

@[simp] theorem vectorWord_read (n k value : ℕ) (i : Fin k) :
    read (vectorWord n k value) i.val=digit n value i.val := by
  simp only [read,vectorWord,List.getElem?_ofFn,dif_pos i.isLt,Option.getD_some]

def vectorMatches (D : Data n k b) (R : List ℕ) (a x value : ℕ) : Bool :=
  (List.range k).all (fun i =>
    read R (read D.targetWord (i+k*(x+b*a))+n*digit n value i)==1)

theorem vectorMatches_correct (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a : Fin n) (x : Fin b) (v : Fin (n^k)) :
    vectorMatches D (matrixWord R) a.val x.val v.val=true ↔
      ∀ i : Fin k,(finFunctionFinEquiv.symm v i,D.target a x i) ∈ R := by
  simp only [vectorMatches,List.all_eq_true]
  constructor
  · intro h i
    have hi := h i.val (List.mem_range.mpr i.isLt)
    rw [D.targetWord_read a x i,digit_equiv v i,matrixWord_read] at hi
    simpa only [beq_iff_eq,boolNat_eq_one,decide_eq_true_eq] using hi
  · intro h i hi
    let j : Fin k := ⟨i,List.mem_range.mp hi⟩
    have hh := h j
    change (read (matrixWord R) (read D.targetWord (j.val+k*(x.val+b*a.val))+
      n*digit n v.val j.val)==1)=true
    rw [D.targetWord_read a x j,digit_equiv v j,matrixWord_read]
    simpa only [beq_iff_eq,boolNat_eq_one,decide_eq_true_eq] using hh

def vectorCount (D : Data n k b) (R : List ℕ) (a value : ℕ) : ℕ :=
  (List.range (read D.fanoutWord a)).countP (fun x => vectorMatches D R a x value)

def nextEntry (D : Data n k b) (R : List ℕ) (a c : ℕ) : ℕ :=
  if read R (c+n*a)=1 ∧ ∀ value<n^k,vectorCount D R a value=vectorCount D R c value then 1 else 0

def nextMatrix (D : Data n k b) (R : List ℕ) : List ℕ :=
  List.ofFn (fun z : Fin (n*n) =>
    let ac := finProdFinEquiv.symm z
    nextEntry D R ac.1.val ac.2.val)


private theorem range_eq_map_finRange (m : ℕ) :
    List.range m=(List.finRange m).map Fin.val := by
  apply List.ext_getElem?
  intro i
  by_cases h : i<m
  · simp [List.finRange,h]
  · have hh : (List.range m)[i]?=none := List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h)
    simp [List.finRange,h,hh]

theorem vectorCount_correct (D : Data n k b) (R : Finset (Fin n×Fin n))
    (a : Fin n) (v : Fin (n^k)) :
    vectorCount D (matrixWord R) a.val v.val=
      (D.edges a).countP (fun w => ∀ i,(finFunctionFinEquiv.symm v i,w i) ∈ R) := by
  rw [vectorCount,D.fanoutWord_read,range_eq_map_finRange]
  simp only [List.countP_map,Data.edges,Data.neighbors,Multiset.coe_countP,
    List.ofFn_eq_map,List.countP_map]
  apply List.countP_congr
  intro x _
  simpa only [Function.comp_apply,decide_eq_true_eq] using
    vectorMatches_correct D R a ⟨x.val,lt_of_lt_of_le x.isLt (D.fanout_le a)⟩ v

theorem nextEntry_correct (D : Data n k b) (R : Finset (Fin n×Fin n)) (a c : Fin n) :
    nextEntry D (matrixWord R) a.val c.val=boolNat (decide ((a,c) ∈ step D.edges R)) := by
  have hv : (∀ value<n^k,vectorCount D (matrixWord R) a.val value=
      vectorCount D (matrixWord R) c.val value) ↔
      ∀ v : Fin k → Fin n,(D.edges a).countP (fun w => ∀ i,(v i,w i) ∈ R)=
        (D.edges c).countP (fun w => ∀ i,(v i,w i) ∈ R) := by
    constructor
    · intro h v
      have hh := h (finFunctionFinEquiv v).val (finFunctionFinEquiv v).isLt
      rw [vectorCount_correct D R a (finFunctionFinEquiv v),
        vectorCount_correct D R c (finFunctionFinEquiv v)] at hh
      simpa only [Equiv.symm_apply_apply] using hh
    · intro h value hlt
      have hh := h (finFunctionFinEquiv.symm (⟨value,hlt⟩ : Fin (n^k)))
      simpa only [vectorCount_correct D R a ⟨value,hlt⟩,
        vectorCount_correct D R c ⟨value,hlt⟩] using hh
  rw [nextEntry,matrixWord_read]
  simp only [boolNat_eq_one,decide_eq_true_eq,hv]
  simp [step,boolNat]

theorem nextMatrix_correct (D : Data n k b) (R : Finset (Fin n×Fin n)) :
    nextMatrix D (matrixWord R)=matrixWord (step D.edges R) := by
  unfold nextMatrix matrixWord
  congr 1
  funext z
  exact nextEntry_correct D R (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2

/-- Each step stores the complete next matrix before the following round. -/
def refine (D : Data n k b) (R : List ℕ) : ℕ → List ℕ
  | 0 => R
  | r+1 => nextMatrix D (refine D R r)

theorem refine_correct (D : Data n k b) (initialEq : Fin n → Fin n → Bool) (r : ℕ) :
    refine D (matrixWord (table D.edges initialEq 0)) r=matrixWord (table D.edges initialEq r) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [refine,ih,nextMatrix_correct]; rfl

/-- Selected vertices are stored as ordinary index arrays, including any
multiplicities. In graph version III these are only group-element tuples. -/
def selectedCount (n : ℕ) (R selected : List ℕ) (row : ℕ) : ℕ :=
  (selected.map (fun col => read R (col+n*row))).sum

theorem selectedCount_correct (R : Finset (Fin n×Fin n)) (selected : List (Fin n))
    (row : Fin n) :
    selectedCount n (matrixWord R) (selected.map Fin.val) row.val=
      (selected : Multiset (Fin n)).countP (fun col => (row,col) ∈ R) := by
  induction selected with
  | nil => simp [selectedCount]
  | cons col selected ih =>
      simp only [selectedCount,List.map_cons,List.sum_cons] at *
      rw [matrixWord_read,ih]
      by_cases h : (row,col)∈R <;> simp [h,boolNat,Nat.add_comm]

def sameHistogram (n : ℕ) (R left right : List ℕ) : Bool :=
  (List.range n).all (fun row => selectedCount n R left row == selectedCount n R right row)

theorem sameHistogram_correct (R : Finset (Fin n×Fin n)) (left right : List (Fin n)) :
    sameHistogram n (matrixWord R) (left.map Fin.val) (right.map Fin.val)=true ↔
      CompressedRefinement.sameHistogram R (left : Multiset (Fin n)) (right : Multiset (Fin n))=true := by
  simp only [sameHistogram,List.all_eq_true,beq_iff_eq,
    CompressedRefinement.sameHistogram,decide_eq_true_eq]
  constructor
  · intro h row
    simpa only [selectedCount_correct] using h row.val (List.mem_range.mpr row.isLt)
  · intro h row hrow
    let a : Fin n := ⟨row,List.mem_range.mp hrow⟩
    change selectedCount n (matrixWord R) (left.map Fin.val) a.val=
      selectedCount n (matrixWord R) (right.map Fin.val) a.val
    simpa only [selectedCount_correct] using h a

/-- A complete indexed-array decision, with exactly n^2 stored refinement
rounds followed by class counting on the two designated selections. -/
def run (D : Data n k b) (initial left right : List ℕ) : Bool :=
  sameHistogram n (refine D initial (n*n)) left right

theorem run_correct (D : Data n k b) {C : Type*} [DecidableEq C]
    (initial : Fin n → C) (initialEq : Fin n → Fin n → Bool)
    (heq : ∀ a c,initialEq a c=true ↔ initial a=initial c)
    (left right : List (Fin n)) :
    run D (matrixWord (table D.edges initialEq 0)) (left.map Fin.val) (right.map Fin.val)=true ↔
      ∀ r,(left : Multiset (Fin n)).map (labels D.edges initial r)=
        (right : Multiset (Fin n)).map (labels D.edges initial r) := by
  letI : NeZero n := ⟨Nat.ne_of_gt D.positive⟩
  rw [run,refine_correct,sameHistogram_correct]
  simpa only [Fintype.card_fin,pow_two] using
    sameHistogram_bound_correct D.edges initial initialEq heq
      (left : Multiset (Fin n)) (right : Multiset (Fin n))

end GroupWL.IndexedRefinement

