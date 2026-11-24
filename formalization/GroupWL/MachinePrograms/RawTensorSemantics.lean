import GroupWL.MachinePrograms.RawTensorParser
import GroupWL.MachinePrograms.BilinearSemantics

/-! Exact relation between the materialized parser and the tensor encoding. -/
namespace GroupWL.MachinePrograms.NatArrayParser

theorem readNatFields_word (p : ℕ) (xs : List ℕ) (h : ∀x∈xs,x<p) (tail : List Bool) :
    readNatFields p xs.length (Structured.arrayWord xs++tail)=some (xs,tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr := ih (fun a ha => h a (by simp [ha]))
    have hf : readNatField p (Statement.unary x++(Structured.arrayWord xs++tail))=
        some (x,Structured.arrayWord xs++tail) :=
      readNatField_some.mpr ⟨Statement.readUnary_unary _ _,hx⟩
    change (do
      let (a,rest) ← readNatField p (Structured.arrayWord (x::xs)++tail)
      let (as,last) ← readNatFields p xs.length rest
      pure (a::as,last))=some (x::xs,tail)
    have hw : Structured.arrayWord (x::xs)++tail=
        Statement.unary x++(Structured.arrayWord xs++tail) := by
      simp [Statement.unary,List.append_assoc]
    rw [hw,hf]
    simp [hr]

theorem readNatFields_sound {p n : ℕ} {w tail : List Bool} {xs : List ℕ}
    (h : readNatFields p n w=some (xs,tail)) :
    w=Structured.arrayWord xs++tail ∧ xs.length=n ∧ ∀x∈xs,x<p := by
  induction n generalizing w xs with
  | zero =>
    simp only [readNatFields,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    simp
  | succ n ih =>
    cases hf : readNatField p w with
    | none => simp [readNatFields,hf] at h
    | some first =>
      rcases first with ⟨a,rest⟩
      cases ht : readNatFields p n rest with
      | none => simp [readNatFields,hf,ht] at h
      | some last =>
        rcases last with ⟨as,last⟩
        simp only [readNatFields,hf,ht,Option.bind_eq_bind,Option.bind_some,
          Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        obtain ⟨hrest,hlen,hsmall⟩ := ih ht
        obtain ⟨hfirst,ha⟩ := readNatField_some.mp hf
        refine ⟨?_,by simp [hlen],?_⟩
        · rw [Statement.readUnary_sound hfirst,hrest]
          simp [Statement.unary,List.append_assoc]
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hsmall x hx

theorem readDimensions_word (n m : ℕ) (tail : List Bool) :
    readDimensions (Statement.unary n++Statement.unary m++tail)=some (n,m,tail) := by
  simp [readDimensions,List.append_assoc]

theorem readDimensions_sound {n m : ℕ} {w tail : List Bool}
    (h : readDimensions w=some (n,m,tail)) :
    w=Statement.unary n++Statement.unary m++tail := by
  cases hf : Statement.readUnary w with
  | none => simp [readDimensions,hf] at h
  | some first =>
    rcases first with ⟨a,rest⟩
    cases ht : Statement.readUnary rest with
    | none => simp [readDimensions,hf,ht] at h
    | some last =>
      rcases last with ⟨b,last⟩
      simp only [readDimensions,hf,ht,Option.bind_eq_bind,Option.bind_some,
        Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      rw [Statement.readUnary_sound hf,Statement.readUnary_sound ht,List.append_assoc]

def RawTensor.WellFormed (p : ℕ) (R : RawTensor) : Prop :=
  R.coefficients.length=R.inputDimension*R.inputDimension*R.outputDimension ∧
    ∀x∈R.coefficients,x<p

def RawTensor.word (R : RawTensor) : List Bool :=
  Statement.unary R.inputDimension++Statement.unary R.outputDimension++Structured.arrayWord R.coefficients

theorem readRawTensor_word (p : ℕ) (R : RawTensor) (h : R.WellFormed p) (tail : List Bool) :
    readRawTensor p (R.word++tail)=some (R,tail) := by
  unfold RawTensor.word readRawTensor
  rw [List.append_assoc _ _ tail,readDimensions_word]
  simp only [Option.bind_eq_bind,Option.bind_some]
  rw [←h.1,readNatFields_word p R.coefficients h.2]
  rfl

theorem readRawTensor_sound {p : ℕ} {R : RawTensor} {w tail : List Bool}
    (h : readRawTensor p w=some (R,tail)) : w=R.word++tail ∧ R.WellFormed p := by
  cases hh : readDimensions w with
  | none => simp [readRawTensor,hh] at h
  | some dims =>
    rcases dims with ⟨n,m,rest⟩
    cases hf : readNatFields p (n*n*m) rest with
    | none => simp [readRawTensor,hh,hf] at h
    | some value =>
      rcases value with ⟨entries,last⟩
      simp only [readRawTensor,hh,hf,Option.bind_eq_bind,Option.bind_some,
        Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      obtain ⟨hw,hlen,hsmall⟩ := readNatFields_sound hf
      refine ⟨?_,hlen,hsmall⟩
      rw [readDimensions_sound hh,hw]
      simp [RawTensor.word,List.append_assoc]

variable (p : ℕ) [Fact p.Prime]

def RawTensor.coefficient (R : RawTensor) :
    Fin R.inputDimension → Fin R.inputDimension → Fin R.outputDimension → ZMod p :=
  fun i j z => (BilinearEvaluation.read R.coefficients
    ((i.val*R.inputDimension+j.val)*R.outputDimension+z.val) : ZMod p)

theorem RawTensor.coefficientList (R : RawTensor) (h : R.WellFormed p) :
    TensorSerialization.coefficientList (R.coefficient p)=R.coefficients := by
  rw [TensorSerialization.coefficientList,←EvaluationAssembly.entries3_nested]
  apply List.ext_getElem?
  intro i
  by_cases hi : i<R.coefficients.length
  · have hi' : i<R.inputDimension*R.inputDimension*R.outputDimension := by rwa [←h.1]
    simp only [EvaluationAssembly.entries3,List.getElem?_ofFn,dif_pos hi']
    have haddr : ((i/R.outputDimension/R.inputDimension)*R.inputDimension+
        (i/R.outputDimension)%R.inputDimension)*R.outputDimension+i%R.outputDimension=i := by
      rw [Nat.mul_comm (i/R.outputDimension/R.inputDimension),Nat.div_add_mod,
        Nat.mul_comm (i/R.outputDimension),Nat.div_add_mod]
    have hv : R.coefficients[i]<p := h.2 _ (List.getElem_mem hi)
    simp [RawTensor.coefficient,Fin.divNat,Fin.modNat,haddr,BilinearEvaluation.read,
      List.getElem?_eq_getElem hi,ZMod.val_natCast,Nat.mod_eq_of_lt hv]
  · have hi' : ¬i<R.inputDimension*R.inputDimension*R.outputDimension := by rwa [←h.1]
    simp [EvaluationAssembly.entries3,hi',List.getElem?_eq_none (Nat.le_of_not_gt hi)]

def rawOfTensor (T : Statement.TensorDescription p) : RawTensor :=
  ⟨T.inputDimension,T.outputDimension,TensorSerialization.coefficientList (T.coefficient p)⟩

theorem rawOfTensor_wellFormed (T : Statement.TensorDescription p) :
    (rawOfTensor p T).WellFormed p :=
  ⟨BilinearEvaluation.coefficientList_length p _,BilinearEvaluation.coefficientList_lt p _⟩

theorem rawOfTensor_word (T : Statement.TensorDescription p) :
    (rawOfTensor p T).word=T.denseWord p := by
  simp only [RawTensor.word,rawOfTensor,TensorSerialization.coefficientList_word,
    Statement.denseWord_eq_coefficients]

theorem readRawTensor_denseWord (T : Statement.TensorDescription p) (tail : List Bool) :
    readRawTensor p (T.denseWord p++tail)=some (rawOfTensor p T,tail) := by
  rw [←rawOfTensor_word p T]
  exact readRawTensor_word p _ (rawOfTensor_wellFormed p T) tail

end GroupWL.MachinePrograms.NatArrayParser
