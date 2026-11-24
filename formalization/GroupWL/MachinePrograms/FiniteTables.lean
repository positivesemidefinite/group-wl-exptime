import GroupWL.MachinePrograms.UnaryArithmetic

/-! Fixed finite tables compiled into finite pop-branch trees. Table functions
are expanded when constructing the program; no function-evaluation instruction
is present in the operational language. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

def dispatchUnary (source : K) : List (Program K) → Program K
  | [] => .skip
  | p :: ps => .pop source p .skip (dispatchUnary source ps)

/-- Reading the unary index costs one pop per symbol and one empty-stack test. -/
theorem dispatchUnary_runs (source : K) (branches : List (Program K))
    (i : Fin branches.length) (S S' : Store K) (t : ℕ)
    (hi : S source = unary i.val)
    (hbranch : Runs branches[i] (Function.update S source []) t S') :
    Runs (dispatchUnary source branches) S (i.val+1+t) S' := by
  induction branches generalizing S with
  | nil => exact Fin.elim0 i
  | cons branch branches ih =>
      revert hi hbranch
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hi hbranch
        have h : Runs (.pop source branch .skip (dispatchUnary source branches)) S (t+1) S' := by
          apply Runs.pop
          simpa [select,hi,unary] using hbranch
        simpa [dispatchUnary,Nat.add_comm] using h
      · intro hi hbranch
        have hj : S source = unary (j.val+1) := hi
        let S₁ := Function.update S source (unary j.val)
        have hb : Runs branches[j] (Function.update S₁ source []) t S' := by
          simpa [S₁,Function.update_idem] using hbranch
        have hr := ih j S₁ (by simp [S₁]) hb
        have h : Runs (.pop source branch .skip (dispatchUnary source branches)) S
            (j.val+1+t+1) S' := by
          apply Runs.pop
          simpa [select,hj,unary,S₁] using hr
        simpa [dispatchUnary,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def unaryTable {p q : ℕ} (f : Fin p → Fin q) (source target : K) : Program K :=
  dispatchUnary source (List.ofFn (fun i => pushUnary target (f i).val))

theorem unaryTable_runs {p q : ℕ} (f : Fin p → Fin q) (source target : K)
    (hne : source ≠ target) (i : Fin p) (S : Store K)
    (hi : S source = unary i.val) (ht : S target = []) :
    Runs (unaryTable f source target) S (i.val+1+(f i).val)
      (Function.update (Function.update S source []) target (unary (f i).val)) := by
  let branches := List.ofFn (fun i => pushUnary target (f i).val)
  let j : Fin branches.length := ⟨i.val,by simpa [branches] using i.isLt⟩
  apply dispatchUnary_runs source branches j S _ (f i).val hi
  have hp := pushUnary_runs target (f i).val (Function.update S source [])
  simpa [branches,j,Ne.symm hne,ht] using hp

/-- Preserve the source index and restore two empty scratch registers. -/
def unaryTableCopy {p q : ℕ} (f : Fin p → Fin q)
    (source target counter temp : K) : Program K :=
  .seq (copy source counter temp) (unaryTable f counter target)

theorem unaryTableCopy_runs {p q : ℕ} (f : Fin p → Fin q)
    (source target counter temp : K) (hsc : source ≠ counter) (hst : source ≠ temp)
    (hct : counter ≠ temp) (hco : counter ≠ target) (i : Fin p) (S : Store K)
    (hi : S source = unary i.val) (ho : S target = [])
    (hc : S counter = []) (ht : S temp = []) :
    Runs (unaryTableCopy f source target counter temp) S (8*i.val+(f i).val+3)
      (Function.update S target (unary (f i).val)) := by
  let S₁ := Function.update S counter (unary i.val)
  have first : Runs (copy source counter temp) S (7*i.val+2) S₁ := by
    simpa [S₁,hi,hc] using copy_runs S source counter temp hsc hst hct ht
  have last := unaryTable_runs f counter target hco i S₁ (by simp [S₁])
    (by simp [S₁,Ne.symm hco,ho])
  have he : Function.update (Function.update S₁ counter []) target (unary (f i).val) =
      Function.update S target (unary (f i).val) := by
    simp only [S₁,Function.update_idem]
    rw [← hc,Function.update_eq_self]
  rw [he] at last
  have h := Runs.seq first last
  convert h using 1 <;> omega

def binaryTable {p r q : ℕ} (f : Fin p → Fin r → Fin q)
    (left right target : K) : Program K :=
  dispatchUnary left (List.ofFn (fun i => unaryTable (f i) right target))

theorem binaryTable_runs {p r q : ℕ} (f : Fin p → Fin r → Fin q)
    (left right target : K) (hlr : left ≠ right) (hlo : left ≠ target) (hro : right ≠ target)
    (i : Fin p) (j : Fin r) (S : Store K)
    (hi : S left = unary i.val) (hj : S right = unary j.val) (ho : S target = []) :
    Runs (binaryTable f left right target) S (i.val+j.val+(f i j).val+2)
      (Function.update (Function.update (Function.update S left []) right [])
        target (unary (f i j).val)) := by
  let branches := List.ofFn (fun i => unaryTable (f i) right target)
  let l : Fin branches.length := ⟨i.val,by simpa [branches] using i.isLt⟩
  have hb := unaryTable_runs (f i) right target hro j (Function.update S left [])
    (by simp [Ne.symm hlr,hj]) (by simp [Ne.symm hlo,ho])
  have h := dispatchUnary_runs left branches l S _ (j.val+1+(f i j).val) hi
    (by simpa [branches,l] using hb)
  convert h using 1 <;> dsimp [l] <;> omega

/-- Two preserved operands, one result and three restored scratch registers. -/
def binaryTableCopy {p r q : ℕ} (f : Fin p → Fin r → Fin q) (slot : Fin 6 ↪ K) : Program K :=
  .seq (copy (slot 0) (slot 3) (slot 5))
    (.seq (copy (slot 1) (slot 4) (slot 5))
      (binaryTable f (slot 3) (slot 4) (slot 2)))

theorem binaryTableCopy_runs {p r q : ℕ} (f : Fin p → Fin r → Fin q)
    (slot : Fin 6 ↪ K) (i : Fin p) (j : Fin r) (S : Store K)
    (hi : S (slot 0) = unary i.val) (hj : S (slot 1) = unary j.val)
    (ho : S (slot 2) = []) (hx : S (slot 3) = []) (hy : S (slot 4) = [])
    (ht : S (slot 5) = []) :
    Runs (binaryTableCopy f slot) S (8*(i.val+j.val)+(f i j).val+6)
      (Function.update S (slot 2) (unary (f i j).val)) := by
  have ne (i j : Fin 6) (h : i≠j) : slot i ≠ slot j := fun he => h (slot.injective he)
  let S₁ := Function.update S (slot 3) (unary i.val)
  have first : Runs (copy (slot 0) (slot 3) (slot 5)) S (7*i.val+2) S₁ := by
    simpa [S₁,hi,hx] using copy_runs S (slot 0) (slot 3) (slot 5)
      (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) ht
  let S₂ := Function.update S₁ (slot 4) (unary j.val)
  have second : Runs (copy (slot 1) (slot 4) (slot 5)) S₁ (7*j.val+2) S₂ := by
    have h1 : S₁ (slot 1) = unary j.val := by simp [S₁,slot.injective.eq_iff,hj]
    have h4 : S₁ (slot 4) = [] := by simp [S₁,slot.injective.eq_iff,hy]
    have h5 : S₁ (slot 5) = [] := by simp [S₁,slot.injective.eq_iff,ht]
    simpa [S₂,h1,h4] using copy_runs S₁ (slot 1) (slot 4) (slot 5)
      (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) h5
  have last := binaryTable_runs f (slot 3) (slot 4) (slot 2)
    (ne _ _ (by decide)) (ne _ _ (by decide)) (ne _ _ (by decide)) i j S₂
    (by simp [S₂,S₁,slot.injective.eq_iff]) (by simp [S₂])
    (by simp [S₂,S₁,slot.injective.eq_iff,ho])
  have run := Runs.seq first (Runs.seq second last)
  have he : Function.update (Function.update (Function.update S₂ (slot 3) []) (slot 4) [])
      (slot 2) (unary (f i j).val) = Function.update S (slot 2) (unary (f i j).val) := by
    funext k
    by_cases hk : k=slot 2
    · subst k
      simp
    · by_cases hk' : k=slot 4
      · subst k
        simp [slot.injective.eq_iff,hy]
      · by_cases hk'' : k=slot 3
        · subst k
          simp [slot.injective.eq_iff,hx]
        · simp [S₂,S₁,Function.update_of_ne hk,Function.update_of_ne hk',
            Function.update_of_ne hk'']
  rw [he] at run
  convert run using 1 <;> omega

end GroupWL.MachinePrograms.Structured
