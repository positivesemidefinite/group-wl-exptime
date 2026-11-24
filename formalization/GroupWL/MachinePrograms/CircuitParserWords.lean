import GroupWL.MachinePrograms.CircuitRecordWords

/-! The mixed-record parser's exact numeric output for a compact circuit. -/
namespace GroupWL.MachinePrograms.CircuitRecordParser
open CircuitDescription AddressedCircuit

def bitsOfWord (w : List Bool) (n : ℕ) (h : w.length=n) (i : Fin n) : Bool :=
  w[i.val]'(by simpa only [h] using i.isLt)

theorem ofFn_bitsOfWord (w : List Bool) (n : ℕ) (h : w.length=n) :
    List.ofFn (bitsOfWord w n h)=w := by
  apply List.ext_getElem (by simp [h])
  intro i hi hi'
  simp [bitsOfWord]

variable {T : Type*} [FiniteCode T] {r : ℕ}

def schemaValues (e : Schema T r) : Fin 2 → ℕ :=
  ![(FiniteCode.equiv e.source).val,(FiniteCode.equiv e.target).val]
def schemaBits (e : Schema T r) : Fin (1+3*r) → Bool :=
  bitsOfWord ([e.port]++domainWord e.domain++permutationWord e.permutation) (1+3*r)
    (by simp; omega)
def requestValues (q : Request T r) : Fin 1 → ℕ := ![(FiniteCode.equiv q.gate).val]
def requestBits (q : Request T r) : Fin (2*r) → Bool :=
  bitsOfWord (domainWord q.domain) (2*r) (length_domainWord q.domain)

theorem schema_recordWord (e : Schema T r) : recordWord (schemaValues e) (schemaBits e)=schemaWord e := by
  unfold recordWord schemaBits
  rw [ofFn_bitsOfWord]
  simp [schemaValues,schemaWord,codeWord,List.ofFn_succ,List.append_assoc]

theorem request_recordWord (q : Request T r) : recordWord (requestValues q) (requestBits q)=requestWord q := by
  unfold recordWord requestBits
  rw [ofFn_bitsOfWord]
  simp [requestValues,requestWord,codeWord,List.ofFn_succ,List.append_assoc]

def headerValues (C : Circuit T r) : Fin 5 → ℕ :=
  ![FiniteCode.size T,r,C.edges,C.seedCount,C.testCount]
def headerWord (C : Circuit T r) : List Bool :=
  recordWord (headerValues C) (Fin.elim0 : Fin 0 → Bool)
def kindBits (C : Circuit T r) : Fin (FiniteCode.size T) → Bool :=
  bitsOfWord (kindWord C) (FiniteCode.size T) (by simp [kindWord])

theorem headerWord_eq (C : Circuit T r) : headerWord C=
    natWord (FiniteCode.size T)++natWord r++natWord C.edges++natWord C.seedCount++natWord C.testCount := by
  simp [headerWord,recordWord,headerValues,List.ofFn_succ,List.append_assoc]

theorem kind_recordWord (C : Circuit T r) :
    recordWord (Fin.elim0 : Fin 0 → ℕ) (kindBits C)=kindWord C := by
  simp only [recordWord,List.ofFn_zero,List.flatten_nil,List.nil_append,kindBits,ofFn_bitsOfWord]

def schemaRecords (C : Circuit T r) : List Token :=
  records (fun i => schemaValues (C.schema i)) (fun i => schemaBits (C.schema i))
def seedRecords (C : Circuit T r) : List Token :=
  records (fun i => requestValues (C.seed i)) (fun i => requestBits (C.seed i))
def testRecords (C : Circuit T r) : List Token :=
  records (fun i => requestValues (C.test i)) (fun i => requestBits (C.test i))

theorem schemaRecords_stream (C : Circuit T r) : stream (schemaRecords C)=arrayWord schemaWord C.schema := by
  simp only [schemaRecords,stream_records,recordsWord,schema_recordWord,arrayWord]
theorem seedRecords_stream (C : Circuit T r) : stream (seedRecords C)=arrayWord requestWord C.seed := by
  simp only [seedRecords,stream_records,recordsWord,request_recordWord,arrayWord]
theorem testRecords_stream (C : Circuit T r) : stream (testRecords C)=arrayWord requestWord C.test := by
  simp only [testRecords,stream_records,recordsWord,request_recordWord,arrayWord]

theorem circuitWord_records (C : Circuit T r) : circuitWord C=
    headerWord C++kindWord C++stream (schemaRecords C)++stream (seedRecords C)++stream (testRecords C) := by
  rw [headerWord_eq,schemaRecords_stream,seedRecords_stream,testRecords_stream]
  rfl

def headerTokens (C : Circuit T r) : List Token := List.ofFn (fun i => Token.nat (headerValues C i))
def kindTokens (C : Circuit T r) : List Token := (kindWord C).map Token.bit

@[simp] theorem headerTokens_length (C : Circuit T r) : (headerTokens C).length=5 := by simp [headerTokens]
@[simp] theorem kindTokens_length (C : Circuit T r) : (kindTokens C).length=FiniteCode.size T := by simp [kindTokens,kindWord]
theorem headerTokens_stream (C : Circuit T r) : stream (headerTokens C)=headerWord C := by
  simp only [stream,headerTokens,flatMap_eq,List.map_ofFn,Function.comp_def,Token.word,
    headerWord,recordWord,List.ofFn_zero,List.append_nil]
theorem kindTokens_stream (C : Circuit T r) : stream (kindTokens C)=kindWord C := by
  simp only [stream,kindTokens,List.flatMap_map,Function.comp_def,Token.word]
  exact flatMap_singletons _
theorem headerTokens_values (C : Circuit T r) : (headerTokens C).map Token.value=List.ofFn (headerValues C) := by
  simp [headerTokens,Token.value]
theorem kindTokens_values (C : Circuit T r) : (kindTokens C).map Token.value=(kindWord C).map NatArrayLowering.bitNat := by
  simp [kindTokens,Token.value,List.map_map,Function.comp_def]
theorem headerTokens_kind (C : Circuit T r) (i : Fin (headerTokens C).length) :
    (headerTokens C)[i].isNat=decide (i.val%5<5) := by
  simp only [headerTokens]
  erw [List.getElem_ofFn]
  simp [Token.isNat,Nat.mod_lt i.val (by decide : 0<5)]
theorem kindTokens_kind (C : Circuit T r) (i : Fin (kindTokens C).length) :
    (kindTokens C)[i].isNat=decide (i.val%FiniteCode.size T<0) := by
  simp only [kindTokens]
  erw [List.getElem_map]
  simp [Token.isNat]

end GroupWL.MachinePrograms.CircuitRecordParser
