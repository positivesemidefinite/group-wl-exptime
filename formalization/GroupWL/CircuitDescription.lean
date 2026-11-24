import GroupWL.MachineCircuit

/-! An executable bit-string serialization of compact addressed circuits.
The description lists schemas, never the expanded exponential tableau. -/
namespace GroupWL.CircuitDescription

open AddressedCircuit Complexity

def gateEquiv (Alphabet : Type*) : CellularTableau.Gate Alphabet ≃
    Alphabet ⊕ ((Alphabet × Alphabet × Alphabet) ⊕ (Alphabet × Alphabet × Alphabet)) where
  toFun
    | .scalar a => .inl a
    | .pair a b c => .inr (.inl (a,b,c))
    | .triple a b c => .inr (.inr (a,b,c))
  invFun
    | .inl a => .scalar a
    | .inr (.inl (a,b,c)) => .pair a b c
    | .inr (.inr (a,b,c)) => .triple a b c
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with a | ⟨a,b,c⟩ | ⟨a,b,c⟩ <;> rfl

instance {Alphabet : Type*} [FiniteCode Alphabet] : FiniteCode (CellularTableau.Gate Alphabet) :=
  ⟨FiniteCode.size (Alphabet ⊕ ((Alphabet × Alphabet × Alphabet) ⊕ (Alphabet × Alphabet × Alphabet))),
    (gateEquiv Alphabet).trans (FiniteCode.equiv (α := _))⟩

theorem gate_size (Alphabet : Type*) [FiniteCode Alphabet] :
    FiniteCode.size (CellularTableau.Gate Alphabet) =
      FiniteCode.size Alphabet + 2*(FiniteCode.size Alphabet)^3 := by
  change FiniteCode.size Alphabet +
    (FiniteCode.size Alphabet*(FiniteCode.size Alphabet*FiniteCode.size Alphabet) +
      FiniteCode.size Alphabet*(FiniteCode.size Alphabet*FiniteCode.size Alphabet)) = _
  ring

def natWord (n : ℕ) : BitString := List.replicate n true ++ [false]

@[simp] theorem length_natWord (n : ℕ) : (natWord n).length = n+1 := by simp [natWord]

def codeWord {α : Type*} [FiniteCode α] (a : α) : BitString :=
  natWord (FiniteCode.equiv (α := α) a).val

theorem length_codeWord {α : Type*} [FiniteCode α] (a : α) :
    (codeWord a).length ≤ FiniteCode.size α := by
  simp only [codeWord,length_natWord]
  exact Nat.succ_le_of_lt (FiniteCode.equiv (α := α) a).isLt

def domainWord {r : ℕ} (D : ProductDomain r) : BitString :=
  (List.ofFn (fun i => [decide (false ∈ D.coordinate i),decide (true ∈ D.coordinate i)])).flatten

def permutationWord {r : ℕ} (f : AddressMap r) : BitString := List.ofFn (fun i => f i false)

@[simp] theorem length_domainWord {r : ℕ} (D : ProductDomain r) :
    (domainWord D).length = 2*r := by
  simp [domainWord,List.length_flatten,List.sum_ofFn]
  omega

@[simp] theorem length_permutationWord {r : ℕ} (f : AddressMap r) :
    (permutationWord f).length = r := by simp [permutationWord]

def schemaWord {T : Type*} [FiniteCode T] {r : ℕ} (e : Schema T r) : BitString :=
  codeWord e.source ++ codeWord e.target ++ [e.port] ++ domainWord e.domain ++
    permutationWord e.permutation

def requestWord {T : Type*} [FiniteCode T] {r : ℕ} (q : Request T r) : BitString :=
  codeWord q.gate ++ domainWord q.domain

theorem length_schemaWord {T : Type*} [FiniteCode T] {r : ℕ} (e : Schema T r) :
    (schemaWord e).length ≤ 2*FiniteCode.size T+1+3*r := by
  have hs := length_codeWord e.source
  have ht := length_codeWord e.target
  simp only [schemaWord,List.length_append,List.length_cons,List.length_nil,
    length_domainWord,length_permutationWord]
  omega

theorem length_requestWord {T : Type*} [FiniteCode T] {r : ℕ} (q : Request T r) :
    (requestWord q).length ≤ FiniteCode.size T+2*r := by
  simpa only [requestWord,List.length_append,length_domainWord] using
    Nat.add_le_add_right (length_codeWord q.gate) (2*r)

def kindWord {T : Type*} [FiniteCode T] {r : ℕ} (C : Circuit T r) : BitString :=
  List.ofFn (fun i : Fin (FiniteCode.size T) =>
    match C.kind ((FiniteCode.equiv (α := T)).symm i) with
    | .scalar => false
    | .andGate => true)

def arrayWord {α : Type*} (f : α → BitString) {n : ℕ} (a : Fin n → α) : BitString :=
  (List.ofFn (fun i => f (a i))).flatten

theorem length_arrayWord_le {α : Type*} (f : α → BitString) {n : ℕ} (a : Fin n → α)
    (B : ℕ) (h : ∀ x, (f x).length ≤ B) : (arrayWord f a).length ≤ n*B := by
  simp only [arrayWord,List.length_flatten,List.map_ofFn,List.sum_ofFn]
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h (a i))

def circuitWord {T : Type*} [FiniteCode T] {r : ℕ} (C : Circuit T r) : BitString :=
  natWord (FiniteCode.size T) ++ natWord r ++ natWord C.edges ++
    natWord C.seedCount ++ natWord C.testCount ++ kindWord C ++
    arrayWord schemaWord C.schema ++ arrayWord requestWord C.seed ++ arrayWord requestWord C.test

theorem length_circuitWord_le {T : Type*} [FiniteCode T] {r : ℕ} (C : Circuit T r) :
    (circuitWord C).length ≤
      2*FiniteCode.size T+r+C.edges+C.seedCount+C.testCount+5+
      C.edges*(2*FiniteCode.size T+1+3*r)+
      (C.seedCount+C.testCount)*(FiniteCode.size T+2*r) := by
  have he := length_arrayWord_le schemaWord C.schema _ (length_schemaWord (T := T) (r := r))
  have hs := length_arrayWord_le requestWord C.seed _ (length_requestWord (T := T) (r := r))
  have ht := length_arrayWord_le requestWord C.test _ (length_requestWord (T := T) (r := r))
  simp only [circuitWord,List.length_append,length_natWord,kindWord,List.length_ofFn]
  nlinarith

/-- A cubic bound in the address budget from the explicit list counts. -/
theorem length_circuitWord_cubic {T : Type*} [FiniteCode T] {r : ℕ} (C : Circuit T r)
    (B R E S : ℕ) (hB : 1 ≤ B) (hr : r ≤ R*B)
    (he : C.edges ≤ E*B^2) (hs : C.seedCount+C.testCount ≤ S*B) :
    (circuitWord C).length ≤
      (2*FiniteCode.size T+R+E+S+5+
        E*(2*FiniteCode.size T+1+3*R)+S*(FiniteCode.size T+2*R))*B^3 := by
  let N := FiniteCode.size T
  have hB2 : B ≤ B^2 := by nlinarith
  have hB3 : B^2 ≤ B^3 := by nlinarith [Nat.mul_le_mul_left B hB2]
  have h13 : 1 ≤ B^3 := by nlinarith
  have h01 : 2*N+1+3*r ≤ (2*N+1+3*R)*B := by nlinarith
  have h02 : N+2*r ≤ (N+2*R)*B := by nlinarith
  have hEdge := Nat.mul_le_mul he h01
  have hReq := Nat.mul_le_mul hs h02
  have hEdge' : C.edges*(2*N+1+3*r) ≤ (E*(2*N+1+3*R))*B^3 := by
    nlinarith [hEdge]
  have hReq' : (C.seedCount+C.testCount)*(N+2*r) ≤ (S*(N+2*R))*B^3 := by
    calc
      _ ≤ (S*B)*((N+2*R)*B) := hReq
      _ = (S*(N+2*R))*B^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hB3
  have hr' : r ≤ R*B^3 := hr.trans (Nat.mul_le_mul_left R (hB2.trans hB3))
  have he' : C.edges ≤ E*B^3 := he.trans (Nat.mul_le_mul_left E hB3)
  have hs' : C.seedCount+C.testCount ≤ S*B^3 :=
    hs.trans (Nat.mul_le_mul_left S (hB2.trans hB3))
  have hn' : 2*N+5 ≤ (2*N+5)*B^3 := by nlinarith
  have hlength := length_circuitWord_le C
  change (circuitWord C).length ≤
    (2*N+R+E+S+5+E*(2*N+1+3*R)+S*(N+2*R))*B^3
  change (circuitWord C).length ≤
    2*N+r+C.edges+C.seedCount+C.testCount+5+
      C.edges*(2*N+1+3*r)+(C.seedCount+C.testCount)*(N+2*r) at hlength
  nlinarith

def machineSizeConstant (M : Machine) : ℕ :=
  let A := (3+M.workSymbols)*(3+M.states)
  let N := A+2*A^3
  let E := 7*A^3
  let S := 5+M.workSymbols
  2*N+2+E+S+5+E*(2*N+7)+S*(N+4)

theorem machineWord_cubic (M : Machine) (w : BitString) (d : ℕ) (hw : w.length ≤ d) :
    (circuitWord (MachineCircuit.compile M w d)).length ≤ machineSizeConstant M*(d+1)^3 := by
  let A := (3+M.workSymbols)*(3+M.states)
  have hA : FiniteCode.size (MachineCellular.Cell M) = A := by
    change ((2+1)+M.workSymbols)*((2+M.states)+1) = _
    dsimp [A]; ring
  have hr : d+d ≤ 2*(d+1) := by omega
  have he : (MachineCircuit.compile M w d).edges ≤ (7*A^3)*(d+1)^2 := by
    rw [MachineCircuit.edge_count]
    change A^3*(2*d^2+3*d+2) ≤ _
    have h : 2*d^2+3*d+2 ≤ 7*(d+1)^2 := by nlinarith
    exact (Nat.mul_le_mul_left (A^3) h).trans_eq (by ring)
  have hs : (MachineCircuit.compile M w d).seedCount+
      (MachineCircuit.compile M w d).testCount ≤ (5+M.workSymbols)*(d+1) := by
    rw [MachineCircuit.seed_count,MachineCircuit.test_count]
    nlinarith
  have h := length_circuitWord_cubic (MachineCircuit.compile M w d)
    (d+1) 2 (7*A^3) (5+M.workSymbols) (by omega) hr he hs
  simpa only [gate_size,hA,machineSizeConstant,A] using h

def machineWord (M : Machine) (c e : ℕ) (w : BitString) : BitString :=
  circuitWord (MachineCircuit.compile M w (MachineCircuit.addressBits c e w.length))

theorem machineWord_polynomial (M : Machine) (c e : ℕ) (w : BitString) :
    (machineWord M c e w).length ≤
      (machineSizeConstant M*(c+4)^3)*(w.length+1)^(3*(e+1)) := by
  have hd := MachineCircuit.addressBits_polynomial c e w.length
  have hp : 1 ≤ (w.length+1)^(e+1) :=
    Nat.succ_le_of_lt (pow_pos (Nat.succ_pos w.length) (e+1))
  have hd' : MachineCircuit.addressBits c e w.length+1 ≤ (c+4)*(w.length+1)^(e+1) := by
    nlinarith
  have h := machineWord_cubic M w (MachineCircuit.addressBits c e w.length)
    (by simp only [MachineCircuit.addressBits]; omega)
  apply h.trans
  calc
    _ ≤ machineSizeConstant M*((c+4)*(w.length+1)^(e+1))^3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd' 3)
    _ = _ := by
      rw [mul_pow,← pow_mul,Nat.mul_comm (e+1) 3]
      exact (Nat.mul_assoc _ _ _).symm

end GroupWL.CircuitDescription
