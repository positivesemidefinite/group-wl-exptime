import GroupWL.MachinePrograms.CircuitParserWords

/-! Constant-offset reads from the decoded circuit record arrays. -/
namespace GroupWL.MachinePrograms.CircuitRecordParser
open CircuitDescription AddressedCircuit NatArrayLowering

theorem records_read {n u v : ℕ} (values : Fin n → Fin u → ℕ) (bits : Fin n → Fin v → Bool)
    (i : Fin n) (j : Fin (u+v)) :
    ((records values bits).map Token.value)[i.val*(u+v)+j.val]?=
      some ((record (values i) (bits i) j).value) := by
  have hp : 0<u+v := Nat.zero_lt_of_lt j.isLt
  have hi : i.val*(u+v)+j.val<n*(u+v) := by
    simpa [Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (i,j)).isLt
  have hd : (i.val*(u+v)+j.val)/(u+v)=i.val := by
    rw [Nat.mul_comm i.val _,Nat.mul_add_div hp,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have hm : (i.val*(u+v)+j.val)%(u+v)=j.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  have hd' : (⟨i.val*(u+v)+j.val,hi⟩ : Fin (n*(u+v))).divNat=i := Fin.ext hd
  have hm' : (⟨i.val*(u+v)+j.val,hi⟩ : Fin (n*(u+v))).modNat=j := Fin.ext hm
  simp only [records,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dif_pos hi,hd',hm']

theorem records_read_nat {n u v : ℕ} (values : Fin n → Fin u → ℕ) (bits : Fin n → Fin v → Bool)
    (i : Fin n) (j : Fin u) :
    ((records values bits).map Token.value)[i.val*(u+v)+j.val]?=some (values i j) := by
  simpa [record,Fin.addCases_left,Token.value] using records_read values bits i (Fin.castAdd v j)

theorem records_read_bit {n u v : ℕ} (values : Fin n → Fin u → ℕ) (bits : Fin n → Fin v → Bool)
    (i : Fin n) (j : Fin v) :
    ((records values bits).map Token.value)[i.val*(u+v)+u+j.val]?=some (bitNat (bits i j)) := by
  simpa [record,Fin.addCases_right,Token.value,Nat.add_assoc] using records_read values bits i (Fin.natAdd u j)

variable {T : Type*} [FiniteCode T] {r : ℕ}
theorem schema_read_source (C : Circuit T r) (i : Fin C.edges) :
    ((schemaRecords C).map Token.value)[i.val*(3+3*r)]?=some (FiniteCode.equiv (C.schema i).source).val := by
  have h := records_read_nat (fun i => schemaValues (C.schema i)) (fun i => schemaBits (C.schema i)) i 0
  have he : 2+(1+3*r)=3+3*r := by omega
  simpa only [schemaValues,Matrix.cons_val_zero,Fin.val_zero,Nat.add_zero,he] using h

theorem schema_read_target (C : Circuit T r) (i : Fin C.edges) :
    ((schemaRecords C).map Token.value)[i.val*(3+3*r)+1]?=some (FiniteCode.equiv (C.schema i).target).val := by
  have h := records_read_nat (fun i => schemaValues (C.schema i)) (fun i => schemaBits (C.schema i)) i 1
  have he : 2+(1+3*r)=3+3*r := by omega
  simpa only [schemaValues,Matrix.cons_val_one,Fin.val_one,he] using h


theorem schema_read_port (C : Circuit T r) (i : Fin C.edges) :
    ((schemaRecords C).map Token.value)[i.val*(3+3*r)+2]?=some (bitNat (C.schema i).port) := by
  have h := records_read_bit (fun i => schemaValues (C.schema i)) (fun i => schemaBits (C.schema i)) i 0
  have he : 2+(1+3*r)=3+3*r := by omega
  simpa [he,schemaBits,bitsOfWord] using h

theorem request_read_gate {n : ℕ} (qs : Fin n → Request T r) (i : Fin n) :
    ((records (fun i => requestValues (qs i)) (fun i => requestBits (qs i))).map Token.value)[i.val*(1+2*r)]?=
      some (FiniteCode.equiv (qs i).gate).val := by
  simpa [requestValues] using records_read_nat (fun i => requestValues (qs i)) (fun i => requestBits (qs i)) i 0

theorem nested_read {n m : ℕ} (f : Fin n → Fin m → Bool) (i : Fin n) (j : Fin m) :
    ((List.ofFn (fun i => List.ofFn (f i))).flatten)[i.val*m+j.val]?=some (f i j) := by
  have hm : 0<m := Nat.zero_lt_of_lt j.isLt
  have hi : i.val*m+j.val<n*m := by
    simpa [Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (i,j)).isLt
  have hd : (i.val*m+j.val)/m=i.val := by
    rw [Nat.mul_comm i.val m,Nat.mul_add_div hm,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have hr : (i.val*m+j.val)%m=j.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  have hd' : (⟨i.val*m+j.val,hi⟩ : Fin (n*m)).divNat=i := Fin.ext hd
  have hr' : (⟨i.val*m+j.val,hi⟩ : Fin (n*m)).modNat=j := Fin.ext hr
  have he : (List.ofFn (fun a : Fin (n*m) => f a.divNat a.modNat))=
      (List.ofFn (fun i => List.ofFn (f i))).flatten := by
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext x
    apply congrArg List.ofFn
    funext y
    have hd : (x.val*m+y.val)/m=x.val := by
      rw [Nat.mul_comm x.val m,Nat.mul_add_div hm,Nat.div_eq_of_lt y.isLt,Nat.add_zero]
    congr 1 <;> apply Fin.ext <;> simp [Fin.divNat,Fin.modNat,hd,Nat.add_mod,Nat.mod_eq_of_lt]
  rw [←he]
  simp only [List.getElem?_ofFn,dif_pos hi,hd',hr']

theorem domainWord_read (D : ProductDomain r) (i : Fin r) (a : Fin 2) :
    (domainWord D)[2*i.val+a.val]?=some (decide (finTwoEquiv a ∈ D.coordinate i)) := by
  have he : domainWord D=(List.ofFn (fun j => List.ofFn (fun b : Fin 2 =>
      decide (finTwoEquiv b ∈ D.coordinate j)))).flatten := by
    simp [domainWord,List.ofFn_succ,finTwoEquiv]
    rfl
  rw [he]
  simpa [Nat.mul_comm] using nested_read (fun (j : Fin r) (b : Fin 2) => decide (finTwoEquiv b∈D.coordinate j)) i a


theorem bitsOfWord_some (w : List Bool) (n : ℕ) (h : w.length=n) (i : Fin n) :
    some (bitsOfWord w n h i)=w[i.val]? := by
  have hi : i.val<w.length := by simpa [h] using i.isLt
  simp [bitsOfWord,List.getElem?_eq_getElem,hi]

theorem schemaBits_domain (e : Schema T r) (i : Fin r) (a : Fin 2) :
    schemaBits e ⟨1+2*i.val+a.val,by omega⟩=decide (finTwoEquiv a∈e.domain.coordinate i) := by
  apply Option.some.inj
  rw [schemaBits,bitsOfWord_some,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [show 1+2*i.val+a.val-1=2*i.val+a.val by omega]
  rw [List.getElem?_append_left (by rw [length_domainWord]; omega)]
  exact domainWord_read e.domain i a

theorem schemaBits_permutation (e : Schema T r) (i : Fin r) :
    schemaBits e ⟨1+2*r+i.val,by omega⟩=e.permutation i false := by
  apply Option.some.inj
  rw [schemaBits,bitsOfWord_some,List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_cons,List.length_nil]; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [List.getElem?_append_right (by rw [length_domainWord]; omega),length_domainWord]
  rw [show 1+2*r+i.val-1-2*r=i.val by omega]
  simp [permutationWord,List.getElem?_ofFn,i.isLt]

theorem schema_read_domain (C : Circuit T r) (e : Fin C.edges) (i : Fin r) (a : Fin 2) :
    ((schemaRecords C).map Token.value)[e.val*(3+3*r)+3+2*i.val+a.val]?=
      some (bitNat (decide (finTwoEquiv a∈(C.schema e).domain.coordinate i))) := by
  have h := records_read_bit (fun i => schemaValues (C.schema i)) (fun i => schemaBits (C.schema i))
    e ⟨1+2*i.val+a.val,by omega⟩
  have he : 2+(1+3*r)=3+3*r := by omega
  rw [schemaBits_domain (C.schema e) i a] at h
  simp only [Fin.val_mk,he] at h
  convert h using 1 <;> congr 1 <;> omega

theorem schema_read_permutation (C : Circuit T r) (e : Fin C.edges) (i : Fin r) :
    ((schemaRecords C).map Token.value)[e.val*(3+3*r)+3+2*r+i.val]?=
      some (bitNat ((C.schema e).permutation i false)) := by
  have h := records_read_bit (fun i => schemaValues (C.schema i)) (fun i => schemaBits (C.schema i))
    e ⟨1+2*r+i.val,by omega⟩
  have he : 2+(1+3*r)=3+3*r := by omega
  rw [schemaBits_permutation (C.schema e) i] at h
  simp only [Fin.val_mk,he] at h
  convert h using 1 <;> congr 1 <;> omega

theorem requestBits_domain (q : Request T r) (i : Fin r) (a : Fin 2) :
    requestBits q ⟨2*i.val+a.val,by omega⟩=decide (finTwoEquiv a∈q.domain.coordinate i) := by
  apply Option.some.inj
  rw [requestBits,bitsOfWord_some]
  exact domainWord_read q.domain i a

theorem request_read_domain {n : ℕ} (qs : Fin n → Request T r) (e : Fin n) (i : Fin r) (a : Fin 2) :
    ((records (fun i => requestValues (qs i)) (fun i => requestBits (qs i))).map Token.value)[e.val*(1+2*r)+1+2*i.val+a.val]?=
      some (bitNat (decide (finTwoEquiv a∈(qs e).domain.coordinate i))) := by
  have h := records_read_bit (fun i => requestValues (qs i)) (fun i => requestBits (qs i))
    e ⟨2*i.val+a.val,by omega⟩
  simpa only [requestBits_domain,Fin.val_mk,Nat.add_assoc] using h

end GroupWL.MachinePrograms.CircuitRecordParser
