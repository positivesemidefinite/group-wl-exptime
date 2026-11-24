import GroupWL.MachinePrograms.CompilerSchemaWords

/-! Constant, carry and borrow coordinate blocks emitted by actual stack code. -/
namespace GroupWL.MachinePrograms.Structured

open AddressedCircuit BinaryAddress CircuitDescription

inductive DomainKind where
  | full | zeros | ones | carry | borrow
  deriving DecidableEq

def DomainKind.domain (kind : DomainKind) {r : ℕ} (h : Fin r) : ProductDomain r :=
  match kind with
  | .full => ProductDomain.full r
  | .zeros => ProductDomain.singleton (fun _ => false)
  | .ones => ProductDomain.singleton (fun _ => true)
  | .carry => carryDomain h
  | .borrow => borrowDomain h

def blockRepeatRegisters : Fin 4 ↪ Fin 6 := ⟨![0,3,4,5],by decide⟩
def blockPieceRegisters : Fin 5 ↪ Fin 6 := ⟨![1,2,3,4,5],by decide⟩

/-- Registers: dimension, position, coordinates after that position, output,
loop counter and scratch. Position registers are unused for constant blocks. -/
def emitDomainBlock {K : Type*} (reg : Fin 6 ↪ K) : DomainKind → Program K
  | .full => repeatEmit (blockRepeatRegisters.trans reg) [true,true]
  | .zeros => repeatEmit (blockRepeatRegisters.trans reg) [true,false]
  | .ones => repeatEmit (blockRepeatRegisters.trans reg) [false,true]
  | .carry => emitCarryDomain (blockPieceRegisters.trans reg)
  | .borrow => emitBorrowDomain (blockPieceRegisters.trans reg)

def BlockSegments {K : Type*} (reg : Fin 6 ↪ K) (S : Store K) {r : ℕ} (h : Fin r) : Prop :=
  S (reg 1) = List.replicate h.val true ∧ S (reg 2) = List.replicate (r-h.val-1) true

theorem domainWord_zeros (r : ℕ) :
    domainWord (ProductDomain.singleton (fun _ : Fin r => false)) = repeatWord [true,false] r := by
  simp [domainWord,ProductDomain.singleton,repeatWord]

theorem domainWord_ones (r : ℕ) :
    domainWord (ProductDomain.singleton (fun _ : Fin r => true)) = repeatWord [false,true] r := by
  simp [domainWord,ProductDomain.singleton,repeatWord]

theorem emitDomainBlock_writes {K : Type*} [DecidableEq K] (S : Store K) (reg : Fin 6 ↪ K)
    (kind : DomainKind) {r : ℕ} (h : Fin r)
    (hr : S (reg 0) = List.replicate r true)
    (hs : kind = .carry ∨ kind = .borrow → BlockSegments reg S h)
    (hc : S (reg 4) = []) (ht : S (reg 5) = []) :
    Writes (reg 3) (emitDomainBlock reg kind) S (domainWord (kind.domain h)) (11*r+3) := by
  cases kind with
  | full =>
    refine ⟨11*r+3,le_rfl,?_⟩
    simpa [emitDomainBlock,DomainKind.domain,blockRepeatRegisters,domainWord_full,Nat.mul_comm] using
      repeatEmit_runs S (blockRepeatRegisters.trans reg) [true,true] r hr hc ht
  | zeros =>
    refine ⟨11*r+3,le_rfl,?_⟩
    simpa [emitDomainBlock,DomainKind.domain,blockRepeatRegisters,domainWord_zeros,Nat.mul_comm] using
      repeatEmit_runs S (blockRepeatRegisters.trans reg) [true,false] r hr hc ht
  | ones =>
    refine ⟨11*r+3,le_rfl,?_⟩
    simpa [emitDomainBlock,DomainKind.domain,blockRepeatRegisters,domainWord_ones,Nat.mul_comm] using
      repeatEmit_runs S (blockRepeatRegisters.trans reg) [false,true] r hr hc ht
  | carry =>
    obtain ⟨hn,hm⟩ := hs (Or.inl rfl)
    have run := emitCarryDomain_runs S (blockPieceRegisters.trans reg) h hn hm hc ht
    obtain ⟨time,hbound,hrun⟩ := run
    refine ⟨time,by omega,?_⟩
    simpa [emitDomainBlock,DomainKind.domain,blockPieceRegisters] using hrun
  | borrow =>
    obtain ⟨hn,hm⟩ := hs (Or.inr rfl)
    have run := emitBorrowDomain_runs S (blockPieceRegisters.trans reg) h hn hm hc ht
    obtain ⟨time,hbound,hrun⟩ := run
    refine ⟨time,by omega,?_⟩
    simpa [emitDomainBlock,DomainKind.domain,blockPieceRegisters] using hrun

inductive PermutationKind where
  | identity | all | initial
  deriving DecidableEq

def PermutationKind.permutation (kind : PermutationKind) {r : ℕ} (h : Fin r) : AddressMap r :=
  match kind with
  | .identity => AddressMap.identity r
  | .all => flipAll r
  | .initial => prefixFlip h

def emitPermutationBlock {K : Type*} (reg : Fin 6 ↪ K) : PermutationKind → Program K
  | .identity => repeatEmit (blockRepeatRegisters.trans reg) [false]
  | .all => repeatEmit (blockRepeatRegisters.trans reg) [true]
  | .initial => emitPrefixFlip (blockPieceRegisters.trans reg)

theorem permutationWord_flipAll (r : ℕ) : permutationWord (flipAll r) = List.replicate r true := by
  simp [permutationWord,flipAll,notEquiv]

theorem emitPermutationBlock_writes {K : Type*} [DecidableEq K] (S : Store K) (reg : Fin 6 ↪ K)
    (kind : PermutationKind) {r : ℕ} (h : Fin r)
    (hr : S (reg 0) = List.replicate r true)
    (hs : kind = .initial → BlockSegments reg S h)
    (hc : S (reg 4) = []) (ht : S (reg 5) = []) :
    Writes (reg 3) (emitPermutationBlock reg kind) S (permutationWord (kind.permutation h)) (10*r+3) := by
  cases kind with
  | identity =>
    refine ⟨10*r+3,le_rfl,?_⟩
    simpa [emitPermutationBlock,PermutationKind.permutation,blockRepeatRegisters,
      permutationWord_identity,repeatWord,Nat.mul_comm] using
      repeatEmit_runs S (blockRepeatRegisters.trans reg) [false] r hr hc ht
  | all =>
    refine ⟨10*r+3,le_rfl,?_⟩
    simpa [emitPermutationBlock,PermutationKind.permutation,blockRepeatRegisters,
      permutationWord_flipAll,repeatWord,Nat.mul_comm] using
      repeatEmit_runs S (blockRepeatRegisters.trans reg) [true] r hr hc ht
  | initial =>
    obtain ⟨hn,hm⟩ := hs rfl
    obtain ⟨time,hbound,hrun⟩ := emitPrefixFlip_runs S (blockPieceRegisters.trans reg) h hn hm hc ht
    refine ⟨time,by omega,?_⟩
    simpa [emitPermutationBlock,PermutationKind.permutation,blockPieceRegisters] using hrun

end GroupWL.MachinePrograms.Structured
