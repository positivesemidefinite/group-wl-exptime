import GroupWL.MachinePrograms.BinaryEncoding
import GroupWL.MachinePrograms.CompilerBitWords
import GroupWL.MachinePrograms.CompilerSchemaWords

/-! Executable serialization of tableau requests, with runtime address widths. -/
namespace GroupWL.MachinePrograms.Structured

open AddressedCircuit BinaryAddress CircuitDescription MachineCellular Complexity

variable {K : Type*} [DecidableEq K]

theorem domainWord_constant (d : ℕ) (b : Bool) :
    domainWord (ProductDomain.singleton (fun _ : Fin d => b)) = repeatWord [!b,b] d := by
  rw [domainWord_singleton]
  simp [mapWord,repeatWord]

/-- A fixed gate code followed by two runtime-width constant coordinate masks. -/
def emitConstantRequest (reg : Fin 4 ↪ K) (code left right : List Bool) : Program K :=
  .seq (emitFixed (reg 1) code)
    (.seq (repeatEmit reg left) (repeatEmit reg right))

theorem emitConstantRequest_runs (S : Store K) (reg : Fin 4 ↪ K)
    (code left right : List Bool) (d : ℕ)
    (hd : S (reg 0) = unary d) (hc : S (reg 2) = []) (ht : S (reg 3) = []) :
    Writes (reg 1) (emitConstantRequest reg code left right) S
      (code++repeatWord left d++repeatWord right d)
      (code.length+d*(left.length+right.length+18)+6) := by
  have heq (i j : Fin 4) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let A := Function.update S (reg 1) (code.reverse++S (reg 1))
  have hleft : Writes (reg 1) (repeatEmit reg left) A (repeatWord left d)
      (d*(left.length+9)+3) :=
    ⟨_,le_rfl,repeatEmit_runs A reg left d
      (by simpa [A,heq] using hd) (by simp [A,heq,hc]) (by simp [A,heq,ht])⟩
  have hright : Writes (reg 1) (repeatEmit reg right)
      (Function.update A (reg 1) ((repeatWord left d).reverse++A (reg 1)))
      (repeatWord right d) (d*(right.length+9)+3) :=
    ⟨_,le_rfl,repeatEmit_runs _ reg right d
      (by simpa [A,heq] using hd) (by simp [A,heq,hc]) (by simp [A,heq,ht])⟩
  have h := (emitFixed_writes S (reg 1) code).seq (hleft.seq hright)
  convert h using 1 <;> (try simp only [List.append_assoc]) <;> ring

def emitTestRequest (reg : Fin 4 ↪ K) (M : Machine) (s : Symbol M.workSymbols) : Program K :=
  emitConstantRequest reg (codeWord (CellularTableau.Gate.scalar
    ((s,some (.inl true)) : Cell M))) [false,true] [true,true]

theorem emitTestRequest_runs (S : Store K) (reg : Fin 4 ↪ K) (M : Machine)
    (s : Symbol M.workSymbols) (d : ℕ)
    (hd : S (reg 0) = unary d) (hc : S (reg 2) = []) (ht : S (reg 3) = []) :
    Writes (reg 1) (emitTestRequest reg M s) S
      (requestWord (⟨CellularTableau.Gate.scalar ((s,some (.inl true)) : Cell M),
        ProductAddress.domain (ProductDomain.singleton (fun _ : Fin d => true))
          (ProductDomain.full d)⟩ : Request (CellularTableau.Gate (Cell M)) (d+d)))
      ((codeWord (CellularTableau.Gate.scalar ((s,some (.inl true)) : Cell M))).length+22*d+6) := by
  simpa [emitTestRequest,requestWord,domainWord_product,domainWord_constant,
    domainWord_full,Nat.mul_comm] using
    emitConstantRequest_runs S reg
      (codeWord (CellularTableau.Gate.scalar ((s,some (.inl true)) : Cell M)))
      [false,true] [true,true] d hd hc ht

def positionBinaryRegisters : Fin 12 ↪ Fin 13 :=
  ⟨fun i => ⟨i.val,by omega⟩,by intro i j h; exact Fin.ext (congrArg (fun x : Fin 13 => x.val) h)⟩

def positionTimeRegisters : Fin 4 ↪ Fin 13 := ⟨![1,12,3,4],by decide⟩
def positionMaskRegisters : Fin 4 ↪ Fin 13 := ⟨![11,12,3,4],by decide⟩

/-- Registers 0 and 1 hold the unary position and width, 12 is output, and
2 through 11 are scratch. The gate code is fixed by finite control. -/
def emitPositionRequest (reg : Fin 13 ↪ K) (code : List Bool) : Program K :=
  .seq (binaryNatural (positionBinaryRegisters.trans reg))
    (.seq (emitFixed (reg 12) code)
      (.seq (repeatEmit (positionTimeRegisters.trans reg) [true,false])
        (.seq (emitSingletonDomain (positionMaskRegisters.trans reg)) (clear (reg 11)))))

theorem emitPositionRequest_runs (S : Store K) (reg : Fin 13 ↪ K)
    (code : List Bool) (n d : ℕ)
    (hn : S (reg 0) = unary n) (hd : S (reg 1) = unary d)
    (he : ∀ i : Fin 13, 2 ≤ i.val → i.val < 12 → S (reg i) = []) :
    Writes (reg 12) (emitPositionRequest reg code) S
      (code++domainWord (ProductAddress.domain
        (ProductDomain.singleton (fun _ : Fin d => false))
        (ProductDomain.singleton (ofNat d n))))
      (code.length+240*(n+d+1)^2) := by
  have eqreg (i j : Fin 13) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  have hb := binaryNatural_runs S (positionBinaryRegisters.trans reg) n d
    (by simpa [positionBinaryRegisters] using hn)
    (by simpa [positionBinaryRegisters] using hd)
    (by simpa [positionBinaryRegisters] using he 2 (by decide) (by decide))
    (by intro i hi; simpa [positionBinaryRegisters] using
          he ⟨i.val,by omega⟩ (by change 2 ≤ i.val; omega) i.isLt)
  obtain ⟨t,ht,hb⟩ := hb
  let A := Function.update S (reg 11) (binaryWord d n)
  have hb' : Runs (binaryNatural (positionBinaryRegisters.trans reg)) S t A := by
    simpa [A,positionBinaryRegisters] using hb
  let B := Function.update A (reg 12) (code.reverse++A (reg 12))
  have hcode : Runs (emitFixed (reg 12) code) A code.length B := emitFixed_runs A _ _
  let C := Function.update B (reg 12) ((repeatWord [true,false] d).reverse++B (reg 12))
  have htime : Runs (repeatEmit (positionTimeRegisters.trans reg) [true,false]) B
      (11*d+3) C := by
    have h := repeatEmit_runs B (positionTimeRegisters.trans reg) [true,false] d
      (by simpa [positionTimeRegisters,B,A,eqreg] using hd)
      (by simp [positionTimeRegisters,B,A,eqreg,he 3 (by decide) (by decide)])
      (by simp [positionTimeRegisters,B,A,eqreg,he 4 (by decide) (by decide)])
    simpa [C,positionTimeRegisters,Nat.mul_comm] using h
  let D := Function.update C (reg 12)
    ((domainWord (ProductDomain.singleton (ofNat d n))).reverse++C (reg 12))
  have hmask : Runs (emitSingletonDomain (positionMaskRegisters.trans reg)) C (11*d+3) D := by
    have h := emitSingletonDomain_runs C (positionMaskRegisters.trans reg) (ofNat d n)
      (by simp [positionMaskRegisters,C,B,A,eqreg,binaryWord])
      (by simp [positionMaskRegisters,C,B,A,eqreg,he 3 (by decide) (by decide)])
      (by simp [positionMaskRegisters,C,B,A,eqreg,he 4 (by decide) (by decide)])
    simpa [D,positionMaskRegisters] using h
  have hclear := clear_runs D (reg 11)
  have h11 : D (reg 11) = binaryWord d n := by simp [D,C,B,A,eqreg]
  rw [h11,binaryWord_length] at hclear
  have hfinal : Function.update D (reg 11) [] =
      Function.update S (reg 12)
        ((code++domainWord (ProductAddress.domain
          (ProductDomain.singleton (fun _ : Fin d => false))
          (ProductDomain.singleton (ofNat d n)))).reverse++S (reg 12)) := by
    funext k
    by_cases hk : k = reg 11
    · subst k; simp [eqreg,he 11 (by decide) (by decide)]
    · by_cases hk' : k = reg 12
      · subst k
        simp [D,C,B,A,eqreg,domainWord_product,domainWord_constant,
          List.reverse_append,List.append_assoc]
      · simp [D,C,B,A,Function.update_of_ne hk,Function.update_of_ne hk']
  rw [hfinal] at hclear
  refine ⟨t+(code.length+((11*d+3)+((11*d+3)+(2*d+1)))),?_,
    Runs.seq hb' (Runs.seq hcode (Runs.seq htime (Runs.seq hmask hclear)))⟩
  have hbig : d+1 ≤ (n+d+1)^2 :=
    (by omega : d+1 ≤ n+d+1).trans (Nat.le_self_pow (by decide : 2 ≠ 0) _)
  omega

def testRequestsWord (M : Machine) (d : ℕ) (symbols : List (Symbol M.workSymbols)) : List Bool :=
  (symbols.map (fun s => requestWord
    (⟨CellularTableau.Gate.scalar ((s,some (.inl true)) : Cell M),
      ProductAddress.domain (ProductDomain.singleton (fun _ : Fin d => true))
        (ProductDomain.full d)⟩ : Request (CellularTableau.Gate (Cell M)) (d+d)))).flatten

def emitTestRequestsList (reg : Fin 4 ↪ K) (M : Machine) : List (Symbol M.workSymbols) → Program K
  | [] => .skip
  | s::ss => .seq (emitTestRequest reg M s) (emitTestRequestsList reg M ss)

theorem emitTestRequestsList_runs (reg : Fin 4 ↪ K) (M : Machine)
    (symbols : List (Symbol M.workSymbols)) (d : ℕ) :
    ∀ S : Store K, S (reg 0) = unary d → S (reg 2) = [] → S (reg 3) = [] →
    Writes (reg 1) (emitTestRequestsList reg M symbols) S (testRequestsWord M d symbols)
      (symbols.length*(FiniteCode.size (CellularTableau.Gate (Cell M))+22*d+6)) := by
  induction symbols with
  | nil =>
    intro S hd hc ht
    exact ⟨0,by simp,by simpa [emitTestRequestsList,testRequestsWord] using Runs.skip S⟩
  | cons s ss ih =>
    intro S hd hc ht
    have heq (i j : Fin 4) : reg i = reg j ↔ i = j := reg.injective.eq_iff
    have first := (emitTestRequest_runs S reg M s d hd hc ht).mono
      (Nat.add_le_add_right (Nat.add_le_add_right (length_codeWord _) _) _)
    have rest := ih (Function.update S (reg 1)
      ((testRequestsWord M d [s]).reverse++S (reg 1))) (by simpa [heq] using hd)
      (by simp [heq,hc]) (by simp [heq,ht])
    simp only [testRequestsWord,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,
      List.append_nil] at rest
    have run := first.seq rest
    convert run using 1 <;> simp [emitTestRequestsList,testRequestsWord,Nat.add_mul]
      <;> ring

def emitTestRequests (reg : Fin 4 ↪ K) (M : Machine) : Program K :=
  emitTestRequestsList reg M (List.ofFn (FiniteCode.equiv (α := Symbol M.workSymbols)).symm)

theorem emitTestRequests_runs (S : Store K) (reg : Fin 4 ↪ K) (M : Machine) (d : ℕ)
    (hd : S (reg 0) = unary d) (hc : S (reg 2) = []) (ht : S (reg 3) = []) :
    Writes (reg 1) (emitTestRequests reg M) S
      (arrayWord requestWord (MachineCircuit.compile M [] d).test)
      (FiniteCode.size (Symbol M.workSymbols)*
        (FiniteCode.size (CellularTableau.Gate (Cell M))+22*d+6)) := by
  simpa [emitTestRequests,testRequestsWord,arrayWord,MachineCircuit.compile,
    TableauCircuit.circuit,MachineCircuit.tests,List.map_ofFn] using
    emitTestRequestsList_runs reg M
      (List.ofFn (FiniteCode.equiv (α := Symbol M.workSymbols)).symm) d S hd hc ht

def initialLetter (M : Machine) (n : ℕ) (symbol : Option Bool) : Cell M :=
  (.inl symbol,if n = 0 then some (.inr M.start) else none)

def initialPositionWord (M : Machine) (d n : ℕ) (symbol : Option Bool) : List Bool :=
  codeWord (CellularTableau.Gate.scalar (initialLetter M n symbol))++
    domainWord (ProductAddress.domain (ProductDomain.singleton (fun _ : Fin d => false))
      (ProductDomain.singleton (ofNat d n)))

def currentPositionRegisters : Fin 13 ↪ Fin 14 :=
  ⟨fun i => ⟨i.val,by omega⟩,
    by intro i j h; exact Fin.ext (congrArg (fun x : Fin 14 => x.val) h)⟩

def emitCurrentBranch (reg : Fin 14 ↪ K) (M : Machine) (head : Bool) : Program K :=
  let emit (symbol : Option Bool) := emitPositionRequest (currentPositionRegisters.trans reg)
    (codeWord (CellularTableau.Gate.scalar
      ((.inl symbol,if head then some (.inr M.start) else none) : Cell M)))
  .peek (reg 13) (emit none) (emit (some false)) (emit (some true))

def emitCurrentPosition (reg : Fin 14 ↪ K) (M : Machine) : Program K :=
  .peek (reg 0) (emitCurrentBranch reg M true)
    (emitCurrentBranch reg M false) (emitCurrentBranch reg M false)

theorem emitCurrentBranch_runs (S : Store K) (reg : Fin 14 ↪ K) (M : Machine)
    (head : Bool) (n d : ℕ) (hn : S (reg 0) = unary n) (hd : S (reg 1) = unary d)
    (he : ∀ i : Fin 14, 2 ≤ i.val → i.val < 12 → S (reg i) = []) :
    Writes (reg 12) (emitCurrentBranch reg M head) S
      (codeWord (CellularTableau.Gate.scalar
        ((.inl (S (reg 13)).head?,if head then some (.inr M.start) else none) : Cell M))++
        domainWord (ProductAddress.domain (ProductDomain.singleton (fun _ : Fin d => false))
          (ProductDomain.singleton (ofNat d n))))
      (FiniteCode.size (CellularTableau.Gate (Cell M))+240*(n+d+1)^2+1) := by
  let word (symbol : Option Bool) := codeWord (CellularTableau.Gate.scalar
    ((.inl symbol,if head then some (.inr M.start) else none) : Cell M))
  have hrun (symbol : Option Bool) := emitPositionRequest_runs S
    (currentPositionRegisters.trans reg) (word symbol) n d
    (by simpa [currentPositionRegisters] using hn)
    (by simpa [currentPositionRegisters] using hd)
    (by intro i hi hj; exact he ⟨i.val,by omega⟩ hi hj)
  obtain ⟨t,ht,hr⟩ := hrun (S (reg 13)).head?
  refine ⟨t+1,?_,?_⟩
  · have hw : (word (S (reg 13)).head?).length ≤
        FiniteCode.size (CellularTableau.Gate (Cell M)) := length_codeWord _
    omega
  · apply Runs.peek
    cases hs : (S (reg 13)).head? with
    | none => simpa [emitCurrentBranch,select,hs,word,currentPositionRegisters] using hr
    | some b => cases b <;>
        simpa [emitCurrentBranch,select,hs,word,currentPositionRegisters] using hr

theorem emitCurrentPosition_runs (S : Store K) (reg : Fin 14 ↪ K) (M : Machine)
    (n d : ℕ) (hn : S (reg 0) = unary n) (hd : S (reg 1) = unary d)
    (he : ∀ i : Fin 14, 2 ≤ i.val → i.val < 12 → S (reg i) = []) :
    Writes (reg 12) (emitCurrentPosition reg M) S
      (initialPositionWord M d n (S (reg 13)).head?)
      (FiniteCode.size (CellularTableau.Gate (Cell M))+240*(n+d+1)^2+2) := by
  obtain ⟨t,ht,hr⟩ := emitCurrentBranch_runs S reg M (decide (n=0)) n d hn hd he
  refine ⟨t+1,by omega,?_⟩
  apply Runs.peek
  cases n with
  | zero => simpa [select,hn,unary,initialPositionWord,initialLetter] using hr
  | succ n => simpa [select,hn,unary,List.replicate_succ,initialPositionWord,initialLetter] using hr

def initialBitWords (M : Machine) (d : ℕ) : ℕ → List Bool → List Bool
  | _,[] => []
  | n,b::bs => initialPositionWord M d n (some b)++initialBitWords M d (n+1) bs

def emitInitialLoop (reg : Fin 14 ↪ K) (M : Machine) : Program K :=
  .while (reg 13) Option.isSome
    (.seq (emitCurrentPosition reg M) (.seq (discard (reg 13)) (.push (reg 0) true)))

theorem emitInitialLoop_runs (reg : Fin 14 ↪ K) (M : Machine) (d : ℕ) (xs : List Bool) :
    ∀ (S : Store K) (n : ℕ), S (reg 0) = unary n → S (reg 1) = unary d →
      S (reg 13) = xs →
      (∀ i : Fin 14, 2 ≤ i.val → i.val < 12 → S (reg i) = []) →
      ∃ t ≤ xs.length*(FiniteCode.size (CellularTableau.Gate (Cell M))+
          240*(n+xs.length+d+1)^2+5)+1,
        Runs (emitInitialLoop reg M) S t
          (Function.update (Function.update (Function.update S (reg 0) (unary (n+xs.length)))
            (reg 13) []) (reg 12) ((initialBitWords M d n xs).reverse++S (reg 12))) := by
  have eqreg (i j : Fin 14) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  induction xs with
  | nil =>
    intro S n hn hd hs he
    have hfinal : Function.update (Function.update (Function.update S (reg 0) (unary (n+([] : List Bool).length)))
        (reg 13) []) (reg 12) ((initialBitWords M d n []).reverse++S (reg 12)) = S := by
      simp only [List.length_nil,Nat.add_zero,initialBitWords,List.reverse_nil,List.nil_append]
      rw [← hn,Function.update_eq_self,← hs,Function.update_eq_self,Function.update_eq_self]
    rw [hfinal]
    exact ⟨1,by simp,Runs.while_false (by simp [hs])⟩
  | cons b xs ih =>
    intro S n hn hd hs he
    obtain ⟨t,ht,hr⟩ := emitCurrentPosition_runs S reg M n d hn hd he
    let A := Function.update S (reg 12) ((initialPositionWord M d n (some b)).reverse++S (reg 12))
    have hr' : Runs (emitCurrentPosition reg M) S t A := by simpa [A,hs] using hr
    let B := Function.update A (reg 13) xs
    have hdsc : Runs (discard (reg 13)) A 1 B := by
      simpa [B,A,eqreg,hs] using discard_runs A (reg 13)
    let C := Function.update B (reg 0) (unary (n+1))
    have hpush : Runs (.push (reg 0) true) B 1 C := by
      simpa [C,B,A,eqreg,hn,unary,List.replicate_succ] using Runs.push B (reg 0) true
    obtain ⟨u,hu,huRun⟩ := ih C (n+1) (by simp [C]) (by simp [C,B,A,eqreg,hd])
      (by simp [C,B,eqreg])
      (by intro i hi hj; simp [C,B,A,eqreg,show i ≠ 0 by omega,
            show i ≠ 12 by omega,show i ≠ 13 by omega,he i hi hj])
    have hfinal : Function.update (Function.update (Function.update C (reg 0) (unary (n+1+xs.length)))
        (reg 13) []) (reg 12) ((initialBitWords M d (n+1) xs).reverse++C (reg 12)) =
        Function.update (Function.update (Function.update S (reg 0) (unary (n+(b::xs).length)))
          (reg 13) []) (reg 12) ((initialBitWords M d n (b::xs)).reverse++S (reg 12)) := by
      funext k
      by_cases hk : k = reg 12
      · subst k
        simp [C,B,A,eqreg,initialBitWords,List.reverse_append,List.append_assoc]
      · by_cases hk' : k = reg 13
        · subst k; simp [eqreg]
        · by_cases hk'' : k = reg 0
          · subst k; simp [eqreg,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          · simp [C,B,A,Function.update_of_ne hk,Function.update_of_ne hk',Function.update_of_ne hk'']
    rw [hfinal] at huRun
    have run := Runs.while_true (test := Option.isSome) (by simp [hs])
      (Runs.seq hr' (Runs.seq hdsc hpush)) huRun
    refine ⟨(t+(1+1))+u+1,?_,run⟩
    have hpow : (n+d+1)^2 ≤ (n+(b::xs).length+d+1)^2 := Nat.pow_le_pow_left (by simp only [List.length_cons]; omega) 2
    have hsame : n+1+xs.length+d+1 = n+(b::xs).length+d+1 := by simp; omega
    rw [hsame] at hu
    simp only [List.length_cons] at hu hpow ⊢
    simp only [Nat.add_mul,Nat.one_mul]
    omega

def inputLoopRegisters : Fin 14 ↪ Fin 15 :=
  ⟨fun i => ⟨i.val,by omega⟩,
    by intro i j h; exact Fin.ext (congrArg (fun x : Fin 15 => x.val) h)⟩

def initialWords (M : Machine) (d : ℕ) (w : List Bool) : List Bool :=
  initialBitWords M d 0 w++initialPositionWord M d w.length none

/-- Input is preserved in register 14, width in register 1, and output in 12.
All other registers start and finish empty. -/
def emitInitialRequests (reg : Fin 15 ↪ K) (M : Machine) : Program K :=
  .seq (copy (reg 14) (reg 13) (reg 3))
    (.seq (emitInitialLoop (inputLoopRegisters.trans reg) M)
      (.seq (emitCurrentPosition (inputLoopRegisters.trans reg) M) (clear (reg 0))))

theorem emitInitialRequests_runs (S : Store K) (reg : Fin 15 ↪ K) (M : Machine)
    (w : List Bool) (d : ℕ) (hw : S (reg 14) = w) (hd : S (reg 1) = unary d)
    (he : ∀ i : Fin 15, i ≠ 1 → i ≠ 12 → i ≠ 14 → S (reg i) = []) :
    Writes (reg 12) (emitInitialRequests reg M) S (initialWords M d w)
      ((w.length+1)*(FiniteCode.size (CellularTableau.Gate (Cell M))+260*(w.length+d+1)^2)) := by
  have eqreg (i j : Fin 15) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let A := Function.update S (reg 13) w
  have hcopy : Runs (copy (reg 14) (reg 13) (reg 3)) S (7*w.length+2) A := by
    simpa [A,hw,he 13 (by decide) (by decide) (by decide)] using
      copy_runs S (reg 14) (reg 13) (reg 3)
        (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
        (reg.injective.ne (by decide)) (he 3 (by decide) (by decide) (by decide))
  obtain ⟨t,ht,hloop⟩ := emitInitialLoop_runs (inputLoopRegisters.trans reg) M d w A 0
    (by simp [A,inputLoopRegisters,eqreg,unary,he 0 (by decide) (by decide) (by decide)])
    (by simpa [A,inputLoopRegisters,eqreg] using hd)
    (by simp [A,inputLoopRegisters])
    (by intro i hi hj; simp [A,inputLoopRegisters,eqreg,
          show (⟨i.val,by omega⟩ : Fin 15) ≠ 13 by intro h; have := congrArg Fin.val h; simp at this; omega,
          he ⟨i.val,by omega⟩ (by intro h; have := congrArg Fin.val h; simp at this; omega)
            (by intro h; have := congrArg Fin.val h; simp at this; omega)
            (by intro h; have := congrArg Fin.val h; simp at this; omega)])
  let B := Function.update (Function.update S (reg 0) (unary w.length)) (reg 12)
    ((initialBitWords M d 0 w).reverse++S (reg 12))
  have hloop' : Runs (emitInitialLoop (inputLoopRegisters.trans reg) M) A t B := by
    convert hloop using 1
    funext k
    by_cases hk : k = reg 12
    · subst k; simp [B,A,inputLoopRegisters,eqreg]
    · by_cases hk' : k = reg 0
      · subst k; simp [B,inputLoopRegisters,eqreg]
      · by_cases hk'' : k = reg 13
        · subst k; simp [B,inputLoopRegisters,eqreg,he 13 (by decide) (by decide) (by decide)]
        · simp [B,A,inputLoopRegisters,Function.update_of_ne hk,Function.update_of_ne hk',
            Function.update_of_ne hk'']
  obtain ⟨u,hu,hlast⟩ := emitCurrentPosition_runs B (inputLoopRegisters.trans reg) M w.length d
    (by simp [B,inputLoopRegisters,eqreg]) (by simpa [B,inputLoopRegisters,eqreg] using hd)
    (by intro i hi hj; simp [B,inputLoopRegisters,eqreg,
          show (⟨i.val,by omega⟩ : Fin 15) ≠ 0 by intro h; have := congrArg Fin.val h; simp at this; omega,
          show (⟨i.val,by omega⟩ : Fin 15) ≠ 12 by intro h; have := congrArg Fin.val h; simp at this; omega,
          he ⟨i.val,by omega⟩ (by intro h; have := congrArg Fin.val h; simp at this; omega)
            (by intro h; have := congrArg Fin.val h; simp at this; omega)
            (by intro h; have := congrArg Fin.val h; simp at this; omega)])
  let C := Function.update B (reg 12) ((initialPositionWord M d w.length none).reverse++B (reg 12))
  have hlast' : Runs (emitCurrentPosition (inputLoopRegisters.trans reg) M) B u C := by
    simpa [C,B,inputLoopRegisters,eqreg,he 13 (by decide) (by decide) (by decide)] using hlast
  have hclear := clear_runs C (reg 0)
  have hc0 : C (reg 0) = unary w.length := by simp [C,B,eqreg]
  rw [hc0,unary_length] at hclear
  have hfinal : Function.update C (reg 0) [] =
      Function.update S (reg 12) ((initialWords M d w).reverse++S (reg 12)) := by
    funext k
    by_cases hk : k = reg 0
    · subst k; simp [eqreg,he 0 (by decide) (by decide) (by decide)]
    · by_cases hk' : k = reg 12
      · subst k; simp [C,B,eqreg,initialWords,List.reverse_append,List.append_assoc]
      · simp [C,B,Function.update_of_ne hk,Function.update_of_ne hk']
  rw [hfinal] at hclear
  refine ⟨(7*w.length+2)+(t+(u+(2*w.length+1))),?_,
    Runs.seq hcopy (Runs.seq hloop' (Runs.seq hlast' hclear))⟩
  have hsq : w.length+1 ≤ (w.length+d+1)^2 :=
    (by omega : w.length+1 ≤ w.length+d+1).trans (Nat.le_self_pow (by decide : 2 ≠ 0) _)
  simp only [Nat.zero_add] at ht
  nlinarith

end GroupWL.MachinePrograms.Structured
