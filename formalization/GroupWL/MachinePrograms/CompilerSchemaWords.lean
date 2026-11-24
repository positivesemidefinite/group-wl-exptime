import GroupWL.MachinePrograms.CompilerOutput

/-! The schema coordinates are runs of constant words around a carry position. -/
namespace GroupWL.MachinePrograms.Structured

open AddressedCircuit BinaryAddress CircuitDescription

def segments {α : Type*} {r : ℕ} (h : Fin r) (lo mid hi : α) (i : Fin r) : α :=
  if i < h then lo else if i = h then mid else hi

theorem ofFn_segments {α : Type*} {r : ℕ} (h : Fin r) (lo mid hi : α) :
    List.ofFn (segments h lo mid hi) =
      List.replicate h.val lo ++ mid :: List.replicate (r-h.val-1) hi := by
  induction r with
  | zero => exact Fin.elim0 h
  | succ r ih =>
    refine Fin.cases ?_ (fun h => ?_) h
    · simp [segments,List.ofFn_succ]
    · simpa [segments,List.ofFn_succ,List.replicate_succ] using
        congrArg (List.cons lo) (ih h)

theorem flattened_segments {r : ℕ} (h : Fin r) (lo mid hi : List Bool) :
    (List.ofFn (segments h lo mid hi)).flatten =
      repeatWord lo h.val ++ mid ++ repeatWord hi (r-h.val-1) := by
  rw [ofFn_segments]
  simp [repeatWord,List.flatten_append,List.append_assoc]

theorem domainWord_carry {r : ℕ} (h : Fin r) :
    domainWord (carryDomain h) = repeatWord [false,true] h.val ++ [true,false] ++
      repeatWord [true,true] (r-h.val-1) := by
  rw [← flattened_segments h]
  unfold domainWord
  congr 2
  funext i
  simp only [segments,carryDomain]
  split_ifs <;> simp

theorem domainWord_borrow {r : ℕ} (h : Fin r) :
    domainWord (borrowDomain h) = repeatWord [true,false] h.val ++ [false,true] ++
      repeatWord [true,true] (r-h.val-1) := by
  rw [← flattened_segments h]
  unfold domainWord
  congr 2
  funext i
  simp only [segments,borrowDomain]
  split_ifs <;> simp

theorem permutationWord_prefixFlip {r : ℕ} (h : Fin r) :
    permutationWord (prefixFlip h) =
      List.replicate h.val true ++ [true] ++ List.replicate (r-h.val-1) false := by
  simp only [List.append_assoc,List.singleton_append]
  rw [← ofFn_segments h true true false]
  unfold permutationWord
  congr 1
  funext i
  simp only [segments,prefixFlip]
  by_cases hlt : i < h
  · simp [hlt,show i ≤ h from hlt.le,notEquiv]
  · by_cases heq : i = h
    · subst i; simp [notEquiv]
    · have hgt : ¬ i ≤ h := by omega
      simp [hlt,heq,hgt]

theorem domainWord_full (r : ℕ) :
    domainWord (ProductDomain.full r) = repeatWord [true,true] r := by
  simp [domainWord,ProductDomain.full,repeatWord]

theorem permutationWord_identity (r : ℕ) :
    permutationWord (AddressMap.identity r) = List.replicate r false := by
  simp [permutationWord,AddressMap.identity]

private theorem addCases_castLE {α : Type*} {r s : ℕ} (a : Fin r → α) (b : Fin s → α)
    (h : r ≤ r+s) (i : Fin r) : Fin.addCases a b (Fin.castLE h i) = a i := by
  change Fin.addCases a b (i.castAdd s) = a i
  simp

theorem domainWord_product {r s : ℕ} (D : ProductDomain r) (E : ProductDomain s) :
    domainWord (ProductAddress.domain D E) = domainWord D ++ domainWord E := by
  simp [domainWord,ProductAddress.domain,List.ofFn_add,List.flatten_append,addCases_castLE]

theorem permutationWord_product {r s : ℕ} (f : AddressMap r) (g : AddressMap s) :
    permutationWord (ProductAddress.map f g) = permutationWord f ++ permutationWord g := by
  simp [permutationWord,ProductAddress.map,List.ofFn_add,addCases_castLE]

def beforeRegisters : Fin 4 ↪ Fin 5 := ⟨![0,2,3,4],by decide⟩
def afterRegisters : Fin 4 ↪ Fin 5 := ⟨![1,2,3,4],by decide⟩

/-- Registers 0 and 1 hold the numbers of coordinates before and after the
special bit; register 2 is output and registers 3 and 4 are empty scratch. -/
def emitPieces {K : Type*} (reg : Fin 5 ↪ K) (lo mid hi : List Bool) : Program K :=
  .seq (repeatEmit (beforeRegisters.trans reg) lo)
    (.seq (emitFixed (reg 2) mid) (repeatEmit (afterRegisters.trans reg) hi))

theorem emitPieces_runs {K : Type*} [DecidableEq K]
    (S : Store K) (reg : Fin 5 ↪ K) (lo mid hi : List Bool) (n m : ℕ)
    (hn : S (reg 0) = List.replicate n true) (hm : S (reg 1) = List.replicate m true)
    (hc : S (reg 3) = []) (ht : S (reg 4) = []) :
    Runs (emitPieces reg lo mid hi) S
      (n*(lo.length+9)+m*(hi.length+9)+mid.length+6)
      (Function.update S (reg 2)
        ((repeatWord lo n++mid++repeatWord hi m).reverse++S (reg 2))) := by
  have heq (i j : Fin 5) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let S₀ := Function.update S (reg 2) ((repeatWord lo n).reverse++S (reg 2))
  let S₁ := Function.update S₀ (reg 2) (mid.reverse++S₀ (reg 2))
  have first : Runs (repeatEmit (beforeRegisters.trans reg) lo) S (n*(lo.length+9)+3) S₀ := by
    simpa only [beforeRegisters,Function.Embedding.trans_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] using
      repeatEmit_runs S (beforeRegisters.trans reg) lo n hn hc ht
  have second : Runs (emitFixed (reg 2) mid) S₀ mid.length S₁ := emitFixed_runs S₀ _ _
  have third : Runs (repeatEmit (afterRegisters.trans reg) hi) S₁ (m*(hi.length+9)+3)
      (Function.update S (reg 2)
        ((repeatWord lo n++mid++repeatWord hi m).reverse++S (reg 2))) := by
    have run := repeatEmit_runs S₁ (afterRegisters.trans reg) hi m
      (by simpa [afterRegisters,S₁,S₀,heq] using hm)
      (by simpa [afterRegisters,S₁,S₀,heq] using hc)
      (by simpa [afterRegisters,S₁,S₀,heq] using ht)
    simpa [afterRegisters,S₁,S₀,Function.update_idem,List.reverse_append,List.append_assoc] using run
  have run := Runs.seq first (Runs.seq second third)
  convert run using 1
  omega

def emitCarryDomain {K : Type*} (reg : Fin 5 ↪ K) : Program K :=
  emitPieces reg [false,true] [true,false] [true,true]

def emitBorrowDomain {K : Type*} (reg : Fin 5 ↪ K) : Program K :=
  emitPieces reg [true,false] [false,true] [true,true]

def emitPrefixFlip {K : Type*} (reg : Fin 5 ↪ K) : Program K :=
  emitPieces reg [true] [true] [false]

theorem emitCarryDomain_runs {K : Type*} [DecidableEq K]
    (S : Store K) (reg : Fin 5 ↪ K) {r : ℕ} (h : Fin r)
    (hn : S (reg 0) = List.replicate h.val true)
    (hm : S (reg 1) = List.replicate (r-h.val-1) true)
    (hc : S (reg 3) = []) (ht : S (reg 4) = []) :
    ∃ time ≤ 11*r, Runs (emitCarryDomain reg) S time
      (Function.update S (reg 2) ((domainWord (carryDomain h)).reverse++S (reg 2))) := by
  refine ⟨h.val*11+(r-h.val-1)*11+8,?_,?_⟩
  · have := h.isLt
    change h.val*11+(r-h.val-1)*11+8 ≤ 11*r
    omega
  · simpa only [emitCarryDomain,domainWord_carry] using
      emitPieces_runs S reg [false,true] [true,false] [true,true] _ _ hn hm hc ht

theorem emitBorrowDomain_runs {K : Type*} [DecidableEq K]
    (S : Store K) (reg : Fin 5 ↪ K) {r : ℕ} (h : Fin r)
    (hn : S (reg 0) = List.replicate h.val true)
    (hm : S (reg 1) = List.replicate (r-h.val-1) true)
    (hc : S (reg 3) = []) (ht : S (reg 4) = []) :
    ∃ time ≤ 11*r, Runs (emitBorrowDomain reg) S time
      (Function.update S (reg 2) ((domainWord (borrowDomain h)).reverse++S (reg 2))) := by
  refine ⟨h.val*11+(r-h.val-1)*11+8,?_,?_⟩
  · have := h.isLt
    change h.val*11+(r-h.val-1)*11+8 ≤ 11*r
    omega
  · simpa only [emitBorrowDomain,domainWord_borrow] using
      emitPieces_runs S reg [true,false] [false,true] [true,true] _ _ hn hm hc ht

theorem emitPrefixFlip_runs {K : Type*} [DecidableEq K]
    (S : Store K) (reg : Fin 5 ↪ K) {r : ℕ} (h : Fin r)
    (hn : S (reg 0) = List.replicate h.val true)
    (hm : S (reg 1) = List.replicate (r-h.val-1) true)
    (hc : S (reg 3) = []) (ht : S (reg 4) = []) :
    ∃ time ≤ 10*r, Runs (emitPrefixFlip reg) S time
      (Function.update S (reg 2) ((permutationWord (prefixFlip h)).reverse++S (reg 2))) := by
  refine ⟨h.val*10+(r-h.val-1)*10+7,?_,?_⟩
  · have := h.isLt
    change h.val*10+(r-h.val-1)*10+7 ≤ 10*r
    omega
  · simpa [emitPrefixFlip,permutationWord_prefixFlip,repeatWord] using
      emitPieces_runs S reg [true] [true] [false] _ _ hn hm hc ht

end GroupWL.MachinePrograms.Structured
