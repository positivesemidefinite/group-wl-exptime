import GroupWL.MachinePrograms.NatArrayProofs
import Mathlib.Data.Fintype.Prod

/-! Characteristic arrays and prefix scans used by finite subgroup saturation. -/
namespace GroupWL.MachinePrograms.FiniteSetArrays

variable {n : ℕ}

def word (S : Finset (Fin n)) : List ℕ := List.ofFn (fun i => if i∈S then 1 else 0)

@[simp] theorem length_word (S : Finset (Fin n)) : (word S).length=n := by simp [word]

@[simp] theorem read_word (S : Finset (Fin n)) (i : Fin n) :
    (word S)[i.val]?.getD 0=if i∈S then 1 else 0 := by simp [word]

theorem values_word (S : Finset (Fin n)) : ∀ v∈word S,v≤1 := by
  intro v hv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  split_ifs <;> omega

theorem word_insert (S : Finset (Fin n)) (i : Fin n) :
    (word S).set i.val 1 = word (insert i S) := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j<n
  · by_cases he : j=i.val
    · subst j
      rw [List.getElem?_set_self (by simp)]
      simp [word]
    · rw [List.getElem?_set_ne (Ne.symm he)]
      simp [word,hj,show (⟨j,hj⟩ : Fin n)≠i by intro h; exact he (congrArg Fin.val h)]
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [word,hj]

def pairs (n : ℕ) : List (Fin n×Fin n) := List.ofFn (fun i : Fin (n*n) => finProdFinEquiv.symm i)

@[simp] theorem pairs_length (n : ℕ) : (pairs n).length=n*n := by simp [pairs]

theorem mem_pairs (ab : Fin n×Fin n) : ab∈pairs n :=
  List.mem_ofFn.mpr ⟨finProdFinEquiv ab,finProdFinEquiv.symm_apply_apply ab⟩

def addPair (C : Finset (Fin n)) (op : Fin n → Fin n → Fin n)
    (R : Finset (Fin n)) (ab : Fin n×Fin n) : Finset (Fin n) :=
  if ab.1∈C ∧ ab.2∈C then insert (op ab.1 ab.2) R else R

def scanPrefix (C : Finset (Fin n)) (op : Fin n → Fin n → Fin n) (i : ℕ) : Finset (Fin n) :=
  ((pairs n).take i).foldl (addPair C op) C

@[simp] theorem prefix_zero (C : Finset (Fin n)) (op : Fin n → Fin n → Fin n) :
    scanPrefix C op 0=C := rfl

theorem prefix_succ (C : Finset (Fin n)) (op : Fin n → Fin n → Fin n)
    (i : ℕ) (hi : i<n*n) :
    scanPrefix C op (i+1)=addPair C op (scanPrefix C op i) (finProdFinEquiv.symm ⟨i,hi⟩) := by
  unfold scanPrefix
  rw [List.take_succ_eq_append_getElem (by simpa using hi),List.foldl_append]
  simp [pairs]

theorem mem_fold (C R : Finset (Fin n)) (op : Fin n → Fin n → Fin n)
    (xs : List (Fin n×Fin n)) (x : Fin n) :
    x∈xs.foldl (addPair C op) R ↔
      x∈R ∨ ∃ a b,(a,b)∈xs ∧ a∈C ∧ b∈C ∧ op a b=x := by
  induction xs generalizing R with
  | nil => simp
  | cons ab xs ih =>
    rw [List.foldl_cons,ih]
    by_cases hab : ab.1∈C ∧ ab.2∈C
    · simp only [addPair,if_pos hab,Finset.mem_insert,List.mem_cons,Prod.mk.injEq]
      aesop
    · simp only [addPair,if_neg hab,List.mem_cons,Prod.mk.injEq]
      aesop

theorem prefix_complete (C : Finset (Fin n)) (op : Fin n → Fin n → Fin n) :
    scanPrefix C op (n*n)=C ∪ C.biUnion (fun a => C.image (op a)) := by
  ext x
  rw [scanPrefix,List.take_of_length_le (by simp),mem_fold]
  simp only [mem_pairs,true_and,Finset.mem_union,Finset.mem_biUnion,Finset.mem_image]
  aesop

end GroupWL.MachinePrograms.FiniteSetArrays
