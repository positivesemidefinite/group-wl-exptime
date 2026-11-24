import GroupWL.MachinePrograms.CircuitRecordParser

/-! Canonical words for uniform records, with explicit token types and numeric outputs. -/
namespace GroupWL.MachinePrograms.CircuitRecordParser
open NatArrayLanguage
open NatArrayLowering (bitNat)

def record {u v : ℕ} (values : Fin u → ℕ) (bits : Fin v → Bool) : Fin (u+v) → Token :=
  Fin.addCases (fun i => .nat (values i)) (fun i => .bit (bits i))

def records {n u v : ℕ} (values : Fin n → Fin u → ℕ) (bits : Fin n → Fin v → Bool) : List Token :=
  List.ofFn (fun i : Fin (n*(u+v)) => record (values i.divNat) (bits i.divNat) i.modNat)

def recordWord {u v : ℕ} (values : Fin u → ℕ) (bits : Fin v → Bool) : List Bool :=
  (List.ofFn (fun i => CircuitDescription.natWord (values i))).flatten ++ List.ofFn bits

def recordsWord {n u v : ℕ} (values : Fin n → Fin u → ℕ) (bits : Fin n → Fin v → Bool) : List Bool :=
  (List.ofFn (fun i => recordWord (values i) (bits i))).flatten

theorem record_kind {u v : ℕ} (values : Fin u → ℕ) (bits : Fin v → Bool) (i : Fin (u+v)) :
    (record values bits i).isNat=decide (i.val<u) := by
  induction i using Fin.addCases with
  | left i => simp [record,Token.isNat,i.isLt]
  | right i => simp [record,Token.isNat,Fin.val_natAdd]

theorem records_kind {n u v : ℕ} (values : Fin n → Fin u → ℕ) (bits : Fin n → Fin v → Bool)
    (i : Fin (records values bits).length) :
    ((records values bits)[i]).isNat=decide (i.val%(u+v)<u) := by
  simp only [records]
  erw [List.getElem_ofFn]
  exact record_kind _ _ _

theorem flatMap_eq {α β : Type*} (f : α → List β) (xs : List α) :
    xs.flatMap f=(xs.map f).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.map_cons,List.flatten_cons,ih]

theorem flatMap_flatten {α β : Type*} (f : α → List β) (xs : List (List α)) :
    xs.flatten.flatMap f=(xs.map (fun x => x.flatMap f)).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatten_cons,List.flatMap_append,List.map_cons,ih]

theorem flatMap_singletons {α : Type*} (xs : List α) : xs.flatMap (fun x => [x])=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem stream_record {u v : ℕ} (values : Fin u → ℕ) (bits : Fin v → Bool) :
    stream (List.ofFn (record values bits))=recordWord values bits := by
  rw [stream,List.ofFn_add,List.flatMap_append]
  have hc (i : Fin u) (h : u≤u+v) : Fin.castLE h i=Fin.castAdd v i := rfl
  simp only [record,hc,Fin.addCases_left,Fin.addCases_right]
  rw [flatMap_eq,flatMap_eq]
  simp only [List.map_ofFn,Function.comp_def,Token.word,recordWord]
  have he : (List.ofFn (fun i => [bits i])).flatten=List.ofFn bits := by
    simpa only [List.map_ofFn,Function.comp_def] using
      (flatMap_eq (fun b : Bool => [b]) (List.ofFn bits)).symm.trans (flatMap_singletons (List.ofFn bits))
  rw [he]

theorem records_nested {n u v : ℕ} (values : Fin n → Fin u → ℕ) (bits : Fin n → Fin v → Bool) :
    records values bits=(List.ofFn (fun i => List.ofFn (record (values i) (bits i)))).flatten := by
  simp only [records,List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hp : 0<u+v := Nat.zero_lt_of_lt j.isLt
  have hd : (i.val*(u+v)+j.val)/(u+v)=i.val := by
    rw [Nat.mul_comm i.val _,Nat.mul_add_div hp,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have hm : (i.val*(u+v)+j.val)%(u+v)=j.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  have hlt : i.val*(u+v)+j.val<n*(u+v) := by
    simpa [Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (i,j)).isLt
  have hd' : (⟨i.val*(u+v)+j.val,hlt⟩ : Fin (n*(u+v))).divNat=i := Fin.ext hd
  have hm' : (⟨i.val*(u+v)+j.val,hlt⟩ : Fin (n*(u+v))).modNat=j := Fin.ext hm
  rw [hd',hm']

theorem stream_records {n u v : ℕ} (values : Fin n → Fin u → ℕ) (bits : Fin n → Fin v → Bool) :
    stream (records values bits)=recordsWord values bits := by
  rw [records_nested]
  simp only [stream,flatMap_flatten,List.map_ofFn,Function.comp_def]
  change (List.ofFn (fun i => stream (List.ofFn (record (values i) (bits i))))).flatten=_
  simp only [stream_record,recordsWord]

theorem records_program_runs {n u v : ℕ} (values : Fin n → Fin u → ℕ) (bits : Fin n → Fin v → Bool)
    (w tail : List Bool) (M : ℕ) (S : State) (bounded : S.Bounded M) (room : 1≤M)
    (length : S.scalar .length=w.length) (valid : S.scalar .valid=1)
    (input : S.array .input=w.map bitNat) (hs : S.scalar .stride=u+v)
    (hu : S.scalar .unaryCount=u) (hc : S.scalar .count=n*(u+v))
    (word : w.drop (S.scalar .cursor)=recordsWord values bits++tail) :
    ∃t≤n*(u+v)*(7*w.length+18)+6,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.array .output=(records values bits).map Token.value ∧ T.array .input=w.map bitNat ∧
      T.scalar .length=w.length ∧ T.scalar .valid=1 ∧ w.drop (T.scalar .cursor)=tail := by
  simpa only [records,List.length_ofFn] using program_runs (records values bits) w tail M (u+v) u
    S bounded room length valid input hs hu (by simpa [records] using hc)
    (by rwa [stream_records]) (by simp only [records,List.length_ofFn]; intro h; nlinarith)
    (records_kind values bits)

end GroupWL.MachinePrograms.CircuitRecordParser
