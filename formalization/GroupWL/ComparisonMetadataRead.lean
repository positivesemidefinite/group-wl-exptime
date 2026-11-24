import GroupWL.ComparisonMetadata

/-! Direct lookup semantics for numeric comparison records. -/
namespace GroupWL.ComparisonMetadata
open SourceLayout
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r)

theorem source_read (e : E) : (source p C)[(FiniteCode.equiv e).val]?.getD 0=
    (FiniteCode.equiv (C.source e)).val := by
  simp [source,(FiniteCode.equiv e).isLt]

theorem target_read (e : E) : (target p C)[(FiniteCode.equiv e).val]?.getD 0=
    (FiniteCode.equiv (C.target e)).val := by
  simp [target,(FiniteCode.equiv e).isLt]

theorem dimensions_read (t : T) : (dimensions p C)[(FiniteCode.equiv t).val]?.getD 0=C.dim t := by
  simp [dimensions,(FiniteCode.equiv t).isLt]

theorem domain_read (e : E) (i : Fin r) (a : Bool) :
    (domain p C)[2*((FiniteCode.equiv e).val*r+i.val)+(FiniteCode.equiv a).val]?.getD 0=
      if a∈C.domain e i then 1 else 0 := by
  have h := MachinePrograms.EvaluationAssembly.entries3_read
    (fun (j : Fin (FiniteCode.size E)) (i : Fin r) (a : Fin 2) =>
      if finTwoEquiv a∈C.domain (FiniteCode.equiv.symm j) i then 1 else 0)
    (FiniteCode.equiv e) i (FiniteCode.equiv a)
  simpa only [domain,MachinePrograms.EvaluationAssembly.read,Nat.mul_comm,Equiv.symm_apply_apply,show finTwoEquiv (FiniteCode.equiv a)=a from finTwoEquiv.apply_symm_apply a] using h

theorem flatten_ofFn_read {n m : ℕ} (f : Fin n → Fin m → ℕ) (i : Fin n) (j : Fin m) :
    ((List.ofFn fun i => List.ofFn (f i)).flatten)[i.val*m+j.val]?.getD 0=f i j := by
  have he : (List.ofFn fun i => List.ofFn (f i)).flatten=
      List.ofFn (fun z : Fin (n*m) => f (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) := by
    rw [List.ofFn_mul]
    congr 1
    apply congrArg List.ofFn
    funext a
    apply congrArg List.ofFn
    funext b
    have hab : (⟨a.val*m+b.val,by have := (finProdFinEquiv (a,b)).isLt; simpa [finProdFinEquiv,Nat.mul_comm,Nat.add_comm] using this⟩ : Fin (n*m))=
        finProdFinEquiv (a,b) := by apply Fin.ext; simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
    rw [hab,Equiv.symm_apply_apply]
  rw [he]
  have hi : i.val*m+j.val<n*m := by
    simpa [finProdFinEquiv,Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (i,j)).isLt
  simp only [List.getElem?_ofFn,dif_pos hi,Option.getD_some]
  have hij : (⟨i.val*m+j.val,hi⟩ : Fin (n*m))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [hij,Equiv.symm_apply_apply]

theorem permutation_read (e : E) (i : Fin r) :
    (permutation p C)[(FiniteCode.equiv e).val*r+i.val]?.getD 0=
      if C.permutation e i false then 1 else 0 := by
  simpa only [permutation,Equiv.symm_apply_apply] using flatten_ofFn_read
    (fun (j : Fin (FiniteCode.size E)) (i : Fin r) => if C.permutation (FiniteCode.equiv.symm j) i false then 1 else 0)
    (FiniteCode.equiv e) i

theorem sourceForm_read (e : E) (k : Fin 2) :
    (sourceForm p C)[2*(FiniteCode.equiv e).val+k.val]?.getD 0=
      (C.sourceForm e (unit p C (C.source e) k)).val := by
  let f : E → Fin 2 → ℕ := fun e k => (C.sourceForm e (unit p C (C.source e) k)).val
  have h := flatten_ofFn_read (fun (j : Fin (FiniteCode.size E)) (k : Fin 2) => f (FiniteCode.equiv.symm j) k)
    (FiniteCode.equiv e) k
  rw [Equiv.symm_apply_apply] at h
  simpa only [sourceForm,Nat.mul_comm] using h

theorem targetForm_read (e : E) (k : Fin 2) :
    (targetForm p C)[2*(FiniteCode.equiv e).val+k.val]?.getD 0=
      (C.targetForm e (unit p C (C.target e) k)).val := by
  let f : E → Fin 2 → ℕ := fun e k => (C.targetForm e (unit p C (C.target e) k)).val
  have h := flatten_ofFn_read (fun (j : Fin (FiniteCode.size E)) (k : Fin 2) => f (FiniteCode.equiv.symm j) k)
    (FiniteCode.equiv e) k
  rw [Equiv.symm_apply_apply] at h
  simpa only [targetForm,Nat.mul_comm] using h

end GroupWL.ComparisonMetadata
