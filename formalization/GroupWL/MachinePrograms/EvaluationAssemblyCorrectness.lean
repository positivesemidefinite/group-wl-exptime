import GroupWL.MachinePrograms.EvaluationAssembly
import GroupWL.MachinePrograms.NatArrayCompiler
import GroupWL.MachinePrograms.TensorSerialization
import GroupWL.EvaluationTensorCoefficients

/-! Exact coefficient-array correctness for the operational tensor assembler. -/
namespace GroupWL.MachinePrograms.EvaluationAssembly

open ConstructiveCoordinates EvaluationTensorCoefficients

/-- Flat row-major data for a three-index array, with the final index fastest. -/
def entries3 {a b c : ℕ} (f : Fin a → Fin b → Fin c → ℕ) : List ℕ :=
  List.ofFn (fun k : Fin (a*b*c) => f k.divNat.divNat k.divNat.modNat k.modNat)

theorem entries3_length {a b c : ℕ} (f : Fin a → Fin b → Fin c → ℕ) :
    (entries3 f).length=a*b*c := by simp [entries3]

theorem entries3_read {a b c : ℕ} (f : Fin a → Fin b → Fin c → ℕ)
    (i : Fin a) (j : Fin b) (k : Fin c) : read (entries3 f) ((i.val*b+j.val)*c+k.val)=f i j k := by
  have hidx := index2_lt (index2_lt i.isLt j.isLt) k.isLt
  simp only [entries3,read,List.getElem?_ofFn,dif_pos hidx,Option.getD_some]
  have hc : 0<c := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hb : 0<b := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hdiv : ((i.val*b+j.val)*c+k.val)/c=i.val*b+j.val := by
    rw [Nat.mul_comm _ c,Nat.mul_add_div hc,Nat.div_eq_of_lt k.isLt,Nat.add_zero]
  have hdiv' : (i.val*b+j.val)/b=i.val := by
    rw [Nat.mul_comm _ b,Nat.mul_add_div hb,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  congr 1 <;> apply Fin.ext <;>
    simp [Fin.divNat,Fin.modNat,hdiv,hdiv',Nat.add_mod,Nat.mod_eq_of_lt]

theorem entries3_nested {a b c : ℕ} (f : Fin a → Fin b → Fin c → ℕ) :
    entries3 f=(List.ofFn fun i => (List.ofFn fun j => List.ofFn fun k => f i j k).flatten).flatten := by
  simp only [entries3,List.ofFn_mul]
  rw [List.flatten_flatten]
  simp only [List.map_ofFn,Function.comp_def]
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 1
  apply congrArg List.ofFn
  funext j
  apply congrArg List.ofFn
  funext k
  have hc : 0<c := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hb : 0<b := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hdiv : ((i.val*b+j.val)*c+k.val)/c=i.val*b+j.val := by
    rw [Nat.mul_comm _ c,Nat.mul_add_div hc,Nat.div_eq_of_lt k.isLt,Nat.add_zero]
  have hdiv' : (i.val*b+j.val)/b=i.val := by
    rw [Nat.mul_comm _ b,Nat.mul_add_div hb,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  congr 1 <;> apply Fin.ext <;>
    simp [Fin.divNat,Fin.modNat,hdiv,hdiv',Nat.add_mod,Nat.mod_eq_of_lt]

section Tensor
variable (p : ℕ) [Fact p.Prime]
variable {X Z : Type} [AddCommGroup X] [Module (ZMod p) X]
  [AddCommGroup Z] [Module (ZMod p) Z]
variable (D : Coordinates (ZMod p) X) (E : Coordinates (ZMod p) Z)
  (Y : Submodule (ZMod p) (X →ₗ[ZMod p] Z)) (H : Coordinates (ZMod p) Y)
  (ε : AlternatingBilinearMap (ZMod p) X Z)

def operatorEntries : List ℕ :=
  entries3 (fun i z j => (operatorCoefficient D E Y H j i z).val)

def twistEntries : List ℕ := entries3 (fun i j z =>
  (E.equiv (ε (D.equiv.symm (unit i)) (D.equiv.symm (unit j))) z).val)

def description : Statement.TensorDescription p where
  inputDimension := D.dimension+H.dimension
  outputDimension := E.dimension
  tensor := tensor D E Y H ε

theorem coefficient_eq (i j : Fin (D.dimension+H.dimension)) (z : Fin E.dimension) :
    coefficient D.dimension H.dimension p (operatorEntries p D E Y H) (twistEntries p D E ε)
      E.dimension i.val j.val z.val = ((description p D E Y H ε).coefficient p i j z).val := by
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      have hi := i.isLt
      have hj := j.isLt
      simp only [coefficient,Fin.val_castAdd,hi,hj,if_pos]
      rw [twistEntries,entries3_read]
      exact congrArg ZMod.val (coefficient_left_left D E Y H ε i j z).symm
    | right j =>
      have hi := i.isLt
      have hj : ¬D.dimension+j.val<D.dimension := by omega
      simp only [coefficient,Fin.val_castAdd,Fin.val_natAdd,hi,hj,if_pos,if_neg,Nat.add_sub_cancel_left]
      rw [operatorEntries,entries3_read]
      exact congrArg ZMod.val (coefficient_left_right D E Y H ε i j z).symm
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      have hi : ¬D.dimension+i.val<D.dimension := by omega
      have hj := j.isLt
      simp only [coefficient,Fin.val_castAdd,Fin.val_natAdd,hi,hj,if_pos,if_neg,Nat.add_sub_cancel_left]
      rw [operatorEntries,entries3_read]
      rw [← ZMod.neg_val']
      exact congrArg ZMod.val (coefficient_right_left D E Y H ε i j z).symm
    | right j =>
      have hi : ¬D.dimension+i.val<D.dimension := by omega
      have hj : ¬D.dimension+j.val<D.dimension := by omega
      simp only [coefficient,Fin.val_natAdd,hi,hj,if_neg]
      have h := coefficient_right_right D E Y H ε i j z
      change 0=(tensor D E Y H ε (unit _) (unit _) z).val
      rw [h]
      simp

theorem flat_entries_eq :
    List.ofFn (fun k : Fin ((D.dimension+H.dimension)*(D.dimension+H.dimension)*E.dimension) =>
      flatCoefficient D.dimension H.dimension E.dimension p
        (operatorEntries p D E Y H) (twistEntries p D E ε) k.val) =
      TensorSerialization.coefficientList ((description p D E Y H ε).coefficient p) := by
  rw [TensorSerialization.coefficientList,←entries3_nested]
  apply congrArg List.ofFn
  funext k
  exact coefficient_eq p D E Y H ε k.divNat.divNat k.divNat.modNat k.modNat

theorem program_tensor_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (ha : S.scalar .xdim=D.dimension) (hb : S.scalar .ydim=H.dimension)
    (hm : S.scalar .zdim=E.dimension) (hp : S.scalar .modulus=p)
    (hH : S.array .operators=operatorEntries p D E Y H) (hE : S.array .twist=twistEntries p D E ε)
    (sizeBound : (D.dimension+H.dimension)+(D.dimension+H.dimension)*(D.dimension+H.dimension)+
      (D.dimension+H.dimension)*(D.dimension+H.dimension)*E.dimension≤M) :
    ∃t≤19*((D.dimension+H.dimension)*(D.dimension+H.dimension)*E.dimension)+9,
      ∃T,NatArrayLanguage.Runs (NatArrayLanguage.storageBound Reg Arr M) program S t T ∧
        T.Bounded M ∧ T.scalar .inputdim=(description p D E Y H ε).inputDimension ∧
        T.scalar .zdim=(description p D E Y H ε).outputDimension ∧
        T.array .output=TensorSerialization.coefficientList ((description p D E Y H ε).coefficient p) := by
  obtain ⟨t,ht,T,run,bound,hn,hz,out⟩ := program_runs S M bounded
    (by rw [hp]; exact (Fact.out : p.Prime).pos)
    (by simpa only [ha,hb,hm] using sizeBound)
    (by simp only [hH,ha,hb,hm,operatorEntries,entries3_length])
    (by simp only [hE,ha,hm,twistEntries,entries3_length])
  refine ⟨t,by simpa only [ha,hb,hm] using ht,T,run,bound,?_,?_,?_⟩
  · simpa only [description,ha,hb] using hn
  · simpa only [description,hm] using hz
  · simp only [entry,ha,hb,hm,hp,hH,hE] at out
    exact out.trans (flat_entries_eq p D E Y H ε)

def serializedProgram : Structured.Program (NatArrayLowering.StackIndex Reg Arr) :=
  .seq (NatArrayLowering.compileProgram program)
    (TensorSerialization.encodedProgram Reg.inputdim Reg.zdim Arr.output)

theorem serializedProgram_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (ha : S.scalar .xdim=D.dimension) (hb : S.scalar .ydim=H.dimension)
    (hm : S.scalar .zdim=E.dimension) (hp : S.scalar .modulus=p)
    (hH : S.array .operators=operatorEntries p D E Y H) (hE : S.array .twist=twistEntries p D E ε)
    (sizeBound : (D.dimension+H.dimension)+(D.dimension+H.dimension)*(D.dimension+H.dimension)+
      (D.dimension+H.dimension)*(D.dimension+H.dimension)*E.dimension≤M) :
    ∃t≤10000*(NatArrayLanguage.storageBound Reg Arr M+1)^4*
        (19*((D.dimension+H.dimension)*(D.dimension+H.dimension)*E.dimension)+9)+
        3*((description p D E Y H ε).denseWord p).length+5,
      ∃U,Structured.Runs serializedProgram (NatArrayLowering.encodeStore S) t U ∧
        (U (NatArrayLowering.scratchSlot 0)).reverse=(description p D E Y H ε).denseWord p := by
  obtain ⟨t,ht,T,run,bound,hn,hz,out⟩ := program_tensor_runs p D E Y H ε S M bounded ha hb hm hp hH hE sizeBound
  obtain ⟨u,hu,compiled⟩ := NatArrayLowering.compileProgram_runs run
  obtain ⟨v,hv,U,serializer,hout⟩ := TensorSerialization.encoded_program_runs p Reg.inputdim Reg.zdim
    Arr.output (by decide) T (description p D E Y H ε) hn hz out
  refine ⟨u+v,?_,U,.seq compiled serializer,hout⟩
  have h := Nat.mul_le_mul_left (10000*(NatArrayLanguage.storageBound Reg Arr M+1)^4) ht
  omega

end Tensor
end GroupWL.MachinePrograms.EvaluationAssembly
