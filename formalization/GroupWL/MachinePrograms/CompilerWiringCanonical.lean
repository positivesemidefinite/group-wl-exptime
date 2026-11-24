import GroupWL.MachinePrograms.CompilerWiringStreams

/-! Canonical order and polynomial cost of the complete wiring emitter. -/
namespace GroupWL.MachinePrograms.Structured

open AddressedCircuit CellularTableau CircuitDescription

theorem spatialWord_canonical {γ : Type*} (d : ℕ)
    (f : TableauWiring.SpatialCase d → List γ) :
    (List.ofFn (fun i => f ((FiniteCode.equiv (α := TableauWiring.SpatialCase d)).symm i))).flatten =
      (List.ofFn (fun h : Fin d => f (h,none) ++ (List.ofFn (fun k : Fin d => f (h,some k))).flatten)).flatten := by
  rw [FiniteCode.ofFn_prod f,List.flatten_flatten,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext h
  change (List.ofFn (fun i => f (h,(FiniteCode.equiv (α := Option (Fin d))).symm i))).flatten = _
  rw [FiniteCode.ofFn_option (fun k => f (h,k))]
  rfl

theorem tripleWord_canonical {Alphabet : Type*} [FiniteCode Alphabet] (d : ℕ)
    (rule : Alphabet → Alphabet → Alphabet → Alphabet) (x y z : Alphabet) :
    tripleWord d rule x y z =
      (List.ofFn (fun i : Fin (FiniteCode.size (TableauWiring.Case d)) =>
        schemaWord (TableauWiring.schema rule ((x,y,z),(FiniteCode.equiv (α := TableauWiring.Case d)).symm i)))).flatten := by
  let f : TableauWiring.Case d → List Bool := fun i => schemaWord (TableauWiring.schema rule ((x,y,z),i))
  change _ = (List.ofFn (fun i => f ((FiniteCode.equiv (α := TableauWiring.Case d)).symm i))).flatten
  rw [FiniteCode.ofFn_sum f,List.flatten_append]
  rw [FiniteCode.ofFn_sum (fun i : Fin d ⊕ (TableauWiring.SpatialCase d ⊕ Bool) => f (.inr i)),
    List.flatten_append]
  rw [FiniteCode.ofFn_sum (fun i : TableauWiring.SpatialCase d ⊕ Bool => f (.inr (.inr i))),
    List.flatten_append]
  rw [spatialWord_canonical d (fun i => f (.inl i)),
    spatialWord_canonical d (fun i => f (.inr (.inr (.inl i))))]
  rw [FiniteCode.ofFn_bool (fun b => f (.inr (.inr (.inr b))))]
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  dsimp [tripleWord,temporalWord,rowWord,spatialWord,WiringRow.prelude,WiringRow.step,
    SchemaMode.index,f]
  simp only [List.append_assoc]
  have hc : rowWord .center rule x y z = (fun h : Fin d =>
      schemaWord (TableauWiring.schema rule ((x,y,z),.inr (.inl h)))) := by
    funext h
    exact List.append_nil _
  rw [hc]
  rfl

theorem wiringWord_canonical {Alphabet : Type*} [FiniteCode Alphabet] {d s t : ℕ}
    (rule : Alphabet → Alphabet → Alphabet → Alphabet)
    (seeds : Fin s → TableauCircuit.ScalarRequest Alphabet (d+d))
    (tests : Fin t → TableauCircuit.ScalarRequest Alphabet (d+d)) :
    wiringWord d rule = arrayWord schemaWord (TableauCircuit.circuit rule seeds tests).schema := by
  simp only [wiringWord,FiniteCode.enumeration,List.map_ofFn,arrayWord,TableauCircuit.circuit]
  rw [FiniteCode.ofFn_prod (fun i : TableauWiring.Index Alphabet d => schemaWord (TableauWiring.schema rule i)),
    List.flatten_flatten,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact tripleWord_canonical d rule _ _ _

theorem tripleBound_le (N d : ℕ) : tripleBound N d ≤ (16*N+600)*(d+1)^3 := by
  simp only [tripleBound,temporalBound,rowBound]
  nlinarith [Nat.zero_le (N*d),Nat.zero_le (N*d*d),Nat.zero_le (N*d*d*d),
    Nat.zero_le (d*d),Nat.zero_le (d*d*d)]

theorem emitWiring_canonical {K Alphabet : Type*} [DecidableEq K] [FiniteCode Alphabet]
    (S : Store K) (reg : Fin 8 ↪ K) {d s t : ℕ}
    (rule : Alphabet → Alphabet → Alphabet → Alphabet)
    (seeds : Fin s → TableauCircuit.ScalarRequest Alphabet (d+d))
    (tests : Fin t → TableauCircuit.ScalarRequest Alphabet (d+d))
    (hd : 0 < d) (hs : WiringReady reg S d) :
    Writes (reg 1) (emitWiring reg rule) S
      (arrayWord schemaWord (TableauCircuit.circuit rule seeds tests).schema)
      ((FiniteCode.size Alphabet)^3*(16*FiniteCode.size (Gate Alphabet)+600)*(d+1)^3) := by
  have h := (emitWiring_writes S reg rule d hd hs).mono
    (Nat.mul_le_mul_left ((FiniteCode.size Alphabet)^3) (tripleBound_le (FiniteCode.size (Gate Alphabet)) d))
  simpa only [wiringWord_canonical rule seeds tests,Nat.mul_assoc] using h

end GroupWL.MachinePrograms.Structured
