import GroupWL.MachinePrograms.CompilerBlocks

/-! Actual finite-control output of every cellular wiring schema. -/
namespace GroupWL.MachinePrograms.Structured

open AddressedCircuit BinaryAddress CellularTableau CircuitDescription

inductive SchemaMode where
  | leftWrap | leftStep | center | rightWrap | rightStep | pair | output
  deriving DecidableEq

def SchemaMode.timeDomain : SchemaMode → DomainKind
  | .pair | .output => .full
  | _ => .carry

def SchemaMode.spaceDomain : SchemaMode → DomainKind
  | .leftWrap => .ones
  | .leftStep => .carry
  | .rightWrap => .zeros
  | .rightStep => .borrow
  | _ => .full

def SchemaMode.timePermutation : SchemaMode → PermutationKind
  | .pair | .output => .identity
  | _ => .initial

def SchemaMode.spacePermutation : SchemaMode → PermutationKind
  | .leftWrap | .rightWrap => .all
  | .leftStep | .rightStep => .initial
  | _ => .identity

def SchemaMode.index {Alphabet : Type*} {d : ℕ} (mode : SchemaMode)
    (x y z : Alphabet) (h k : Fin d) : TableauWiring.Index Alphabet d :=
  ((x,y,z),match mode with
    | .leftWrap => .inl (h,none)
    | .leftStep => .inl (h,some k)
    | .center => .inr (.inl h)
    | .rightWrap => .inr (.inr (.inl (h,none)))
    | .rightStep => .inr (.inr (.inl (h,some k)))
    | .pair => .inr (.inr (.inr false))
    | .output => .inr (.inr (.inr true)))

def SchemaMode.header {Alphabet : Type*} [FiniteCode Alphabet]
    (mode : SchemaMode) (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) : List Bool :=
  match mode with
  | .leftWrap | .leftStep => codeWord (Gate.scalar x)++codeWord (Gate.pair x y z)++[false]
  | .center => codeWord (Gate.scalar y)++codeWord (Gate.pair x y z)++[true]
  | .rightWrap | .rightStep => codeWord (Gate.scalar z)++codeWord (Gate.triple x y z)++[true]
  | .pair => codeWord (Gate.pair x y z)++codeWord (Gate.triple x y z)++[false]
  | .output => codeWord (Gate.triple x y z)++codeWord (Gate.scalar (rule x y z))++[false]

theorem SchemaMode.header_length {Alphabet : Type*} [FiniteCode Alphabet]
    (mode : SchemaMode) (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) :
    (mode.header rule x y z).length ≤ 2*FiniteCode.size (Gate Alphabet)+1 := by
  cases mode <;> simp only [header,List.length_append,List.length_cons,List.length_nil]
  all_goals have h₁ := length_codeWord (Gate.scalar x)
  all_goals have h₂ := length_codeWord (Gate.scalar y)
  all_goals have h₃ := length_codeWord (Gate.scalar z)
  all_goals have h₄ := length_codeWord (Gate.pair x y z)
  all_goals have h₅ := length_codeWord (Gate.triple x y z)
  all_goals have h₆ := length_codeWord (Gate.scalar (rule x y z))
  all_goals omega

theorem schemaWord_parts {Alphabet : Type*} [FiniteCode Alphabet] {d : ℕ}
    (mode : SchemaMode) (rule : Alphabet → Alphabet → Alphabet → Alphabet)
    (x y z : Alphabet) (h k : Fin d) :
    schemaWord (TableauWiring.schema rule (mode.index x y z h k)) =
      mode.header rule x y z ++ domainWord (mode.timeDomain.domain h) ++
        domainWord (mode.spaceDomain.domain k) ++
        permutationWord (mode.timePermutation.permutation h) ++
        permutationWord (mode.spacePermutation.permutation k) := by
  cases mode <;>
    simp only [SchemaMode.index,TableauWiring.schema,SchemaMode.header,schemaWord,
      SchemaMode.timeDomain,SchemaMode.spaceDomain,SchemaMode.timePermutation,SchemaMode.spacePermutation,
      DomainKind.domain,PermutationKind.permutation,successorDomain,predecessorDomain,stepMap,
      domainWord_product,permutationWord_product,domainWord_full,permutationWord_identity,
      repeatWord,List.replicate_add,List.flatten_append,List.append_assoc]

def timeBlockRegisters : Fin 6 ↪ Fin 8 := ⟨![0,2,3,1,6,7],by decide⟩
def spaceBlockRegisters : Fin 6 ↪ Fin 8 := ⟨![0,4,5,1,6,7],by decide⟩

def SchemaReady {K : Type*} (reg : Fin 8 ↪ K) (S : Store K) {d : ℕ}
    (mode : SchemaMode) (h k : Fin d) : Prop :=
  S (reg 0) = List.replicate d true ∧ S (reg 6) = [] ∧ S (reg 7) = [] ∧
    (mode ≠ .pair ∧ mode ≠ .output → BlockSegments (timeBlockRegisters.trans reg) S h) ∧
    (mode = .leftStep ∨ mode = .rightStep → BlockSegments (spaceBlockRegisters.trans reg) S k)

theorem SchemaReady.update_output {K : Type*} [DecidableEq K] {reg : Fin 8 ↪ K} {S : Store K}
    {d : ℕ} {mode : SchemaMode} {h k : Fin d} (hs : SchemaReady reg S mode h k) (word : List Bool) :
    SchemaReady reg (Function.update S (reg 1) word) mode h k := by
  have heq (i j : Fin 8) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  simpa [SchemaReady,BlockSegments,timeBlockRegisters,spaceBlockRegisters,heq] using hs

/-- Registers: dimension, output, temporal before/after, spatial before/after,
counter and scratch. Only the output changes. -/
def emitSchema {K Alphabet : Type*} [FiniteCode Alphabet] (reg : Fin 8 ↪ K)
    (mode : SchemaMode) (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) : Program K :=
  .seq (emitFixed (reg 1) (mode.header rule x y z))
    (.seq (emitDomainBlock (timeBlockRegisters.trans reg) mode.timeDomain)
      (.seq (emitDomainBlock (spaceBlockRegisters.trans reg) mode.spaceDomain)
        (.seq (emitPermutationBlock (timeBlockRegisters.trans reg) mode.timePermutation)
          (emitPermutationBlock (spaceBlockRegisters.trans reg) mode.spacePermutation))))

theorem emitSchema_writes {K Alphabet : Type*} [DecidableEq K] [FiniteCode Alphabet]
    (S : Store K) (reg : Fin 8 ↪ K) (mode : SchemaMode)
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) {d : ℕ} (h k : Fin d)
    (hs : SchemaReady reg S mode h k) :
    Writes (reg 1) (emitSchema reg mode rule x y z) S
      (schemaWord (TableauWiring.schema rule (mode.index x y z h k)))
      (2*FiniteCode.size (Gate Alphabet)+42*d+13) := by
  have htd : mode.timeDomain = .carry ∨ mode.timeDomain = .borrow → mode ≠ .pair ∧ mode ≠ .output := by
    cases mode <;> simp [SchemaMode.timeDomain]
  have htp : mode.timePermutation = .initial → mode ≠ .pair ∧ mode ≠ .output := by
    cases mode <;> simp [SchemaMode.timePermutation]
  have hsd : mode.spaceDomain = .carry ∨ mode.spaceDomain = .borrow → mode = .leftStep ∨ mode = .rightStep := by
    cases mode <;> simp [SchemaMode.spaceDomain]
  have hsp : mode.spacePermutation = .initial → mode = .leftStep ∨ mode = .rightStep := by
    cases mode <;> simp [SchemaMode.spacePermutation]
  have td (V : Store K) (hv : SchemaReady reg V mode h k) :
      Writes (reg 1) (emitDomainBlock (timeBlockRegisters.trans reg) mode.timeDomain) V
        (domainWord (mode.timeDomain.domain h)) (11*d+3) :=
    emitDomainBlock_writes V (timeBlockRegisters.trans reg) mode.timeDomain h hv.1
      (fun hh => hv.2.2.2.1 (htd hh)) hv.2.1 hv.2.2.1
  have sd (V : Store K) (hv : SchemaReady reg V mode h k) :
      Writes (reg 1) (emitDomainBlock (spaceBlockRegisters.trans reg) mode.spaceDomain) V
        (domainWord (mode.spaceDomain.domain k)) (11*d+3) :=
    emitDomainBlock_writes V (spaceBlockRegisters.trans reg) mode.spaceDomain k hv.1
      (fun hh => hv.2.2.2.2 (hsd hh)) hv.2.1 hv.2.2.1
  have tp (V : Store K) (hv : SchemaReady reg V mode h k) :
      Writes (reg 1) (emitPermutationBlock (timeBlockRegisters.trans reg) mode.timePermutation) V
        (permutationWord (mode.timePermutation.permutation h)) (10*d+3) :=
    emitPermutationBlock_writes V (timeBlockRegisters.trans reg) mode.timePermutation h hv.1
      (fun hh => hv.2.2.2.1 (htp hh)) hv.2.1 hv.2.2.1
  have sp (V : Store K) (hv : SchemaReady reg V mode h k) :
      Writes (reg 1) (emitPermutationBlock (spaceBlockRegisters.trans reg) mode.spacePermutation) V
        (permutationWord (mode.spacePermutation.permutation k)) (10*d+3) :=
    emitPermutationBlock_writes V (spaceBlockRegisters.trans reg) mode.spacePermutation k hv.1
      (fun hh => hv.2.2.2.2 (hsp hh)) hv.2.1 hv.2.2.1
  have hp := emitFixed_writes S (reg 1) (mode.header rule x y z)
  let V₁ := Function.update S (reg 1) ((mode.header rule x y z).reverse++S (reg 1))
  let V₂ := Function.update V₁ (reg 1) ((domainWord (mode.timeDomain.domain h)).reverse++V₁ (reg 1))
  let V₃ := Function.update V₂ (reg 1) ((domainWord (mode.spaceDomain.domain k)).reverse++V₂ (reg 1))
  let V₄ := Function.update V₃ (reg 1) ((permutationWord (mode.timePermutation.permutation h)).reverse++V₃ (reg 1))
  have h₁ : SchemaReady reg V₁ mode h k := hs.update_output _
  have h₂ : SchemaReady reg V₂ mode h k := h₁.update_output _
  have h₃ : SchemaReady reg V₃ mode h k := h₂.update_output _
  have h₄ : SchemaReady reg V₄ mode h k := h₃.update_output _
  have result := hp.seq ((td _ h₁).seq ((sd _ h₂).seq ((tp _ h₃).seq (sp _ h₄))))
  have bound : (mode.header rule x y z).length+((11*d+3)+((11*d+3)+((10*d+3)+(10*d+3)))) ≤
      2*FiniteCode.size (Gate Alphabet)+42*d+13 := by
    have := mode.header_length rule x y z
    omega
  have result' := result.mono bound
  simpa only [emitSchema,schemaWord_parts,List.append_assoc] using result'

end GroupWL.MachinePrograms.Structured
