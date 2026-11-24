import GroupWL.MachinePrograms.RawTensorSemantics

/-! The finite tensor checks recover exactly the original input parser. -/
namespace GroupWL.MachinePrograms.NatArrayParser

variable (p : ℕ) [Fact p.Prime]

def RawTensor.Alternating (R : RawTensor) : Prop :=
  ∀x,Statement.coefficientBilinear p (R.coefficient p) x x=0

instance RawTensor.decidableAlternating (R : RawTensor) : Decidable (R.Alternating p) := by
  unfold RawTensor.Alternating
  infer_instance

def RawTensor.toTensor (R : RawTensor) (h : R.Alternating p) : Statement.TensorDescription p :=
  ⟨R.inputDimension,R.outputDimension,⟨Statement.coefficientBilinear p (R.coefficient p),h⟩⟩

theorem RawTensor.toTensor_coefficient (R : RawTensor) (h : R.Alternating p) :
    (R.toTensor p h).coefficient p=R.coefficient p := by
  funext i j z
  change Statement.coefficientBilinear p (R.coefficient p) (Pi.single i 1) (Pi.single j 1) z=R.coefficient p i j z
  exact congrFun (Statement.coefficientBilinear_basis p (R.coefficient p) i j) z

theorem RawTensor.toTensor_word (R : RawTensor) (hf : R.WellFormed p) (ha : R.Alternating p) :
    (R.toTensor p ha).denseWord p=R.word := by
  rw [Statement.denseWord_eq_coefficients,RawTensor.toTensor_coefficient p R ha]
  have hw := TensorSerialization.coefficientList_word p (R.coefficient p)
  rw [RawTensor.coefficientList p R hf] at hw
  exact congrArg (fun bits => Statement.unary R.inputDimension++Statement.unary R.outputDimension++bits) hw.symm

theorem rawOfTensor_coefficient (T : Statement.TensorDescription p) :
    (rawOfTensor p T).coefficient p=T.coefficient p := by
  funext i j z
  simp only [RawTensor.coefficient,rawOfTensor,BilinearEvaluation.coefficientList_read,
    ZMod.natCast_zmod_val]

theorem rawOfTensor_alternating (T : Statement.TensorDescription p) :
    (rawOfTensor p T).Alternating p := by
  unfold RawTensor.Alternating
  rw [rawOfTensor_coefficient p T]
  intro x
  change Statement.coefficientBilinear p (T.coefficient p) x x=0
  rw [Statement.coefficientBilinear_coefficient p T]
  exact T.tensor.map_self_eq_zero x

theorem readTensor_rawWord (R : RawTensor) (hf : R.WellFormed p) (tail : List Bool) :
    Statement.readTensor p (R.word++tail)=
      if ha : R.Alternating p then some (R.toTensor p ha,tail) else none := by
  by_cases ha : R.Alternating p
  · rw [dif_pos ha,←R.toTensor_word p hf ha]
    exact Statement.readTensor_denseWord p _ _
  · rw [dif_neg ha]
    cases ht : Statement.readTensor p (R.word++tail) with
    | none => rfl
    | some value =>
      rcases value with ⟨T,last⟩
      have hw := Statement.readTensor_sound p ht
      have hp := readRawTensor_word p R hf tail
      rw [hw,readRawTensor_denseWord] at hp
      have he : rawOfTensor p T=R := congrArg Prod.fst (Option.some.inj hp)
      rw [←he] at ha
      exact (ha (rawOfTensor_alternating p T)).elim

def readValidatedTensor (w : List Bool) : Option (Statement.TensorDescription p × List Bool) := do
  let (R,tail) ← readRawTensor p w
  if h : R.Alternating p then some (R.toTensor p h,tail) else none

theorem readValidatedTensor_eq (w : List Bool) :
    readValidatedTensor p w=Statement.readTensor p w := by
  cases hr : readRawTensor p w with
  | none =>
    simp only [readValidatedTensor,hr,Option.bind_eq_bind,Option.bind_none]
    cases ht : Statement.readTensor p w with
    | none => rfl
    | some value =>
      rcases value with ⟨T,tail⟩
      rw [Statement.readTensor_sound p ht,readRawTensor_denseWord] at hr
      contradiction
  | some value =>
    rcases value with ⟨R,tail⟩
    obtain ⟨hw,hf⟩ := readRawTensor_sound hr
    simp only [readValidatedTensor,hr,Option.bind_eq_bind,Option.bind_some]
    rw [hw,readTensor_rawWord p R hf]

def RawTensor.AllSelfZero (R : RawTensor) : Prop :=
  ∀x : Fin (p^R.inputDimension),∀z : Fin R.outputDimension,
    BilinearEvaluation.partialValue R.coefficients p R.inputDimension R.outputDimension
      x.val x.val z.val R.inputDimension=0

theorem RawTensor.allSelfZero_iff (R : RawTensor) (hf : R.WellFormed p) :
    R.AllSelfZero p ↔ R.Alternating p := by
  unfold RawTensor.AllSelfZero RawTensor.Alternating
  simp_rw [←R.coefficientList p hf,BilinearEvaluation.partialValue_correct,ZMod.val_eq_zero]
  constructor
  · intro h x
    obtain ⟨code,hcode⟩ := (BilinearEvaluation.vectorEquiv p R.inputDimension).symm.surjective x
    subst x
    exact funext (h code)
  · intro h x z
    exact congrFun (h (BilinearEvaluation.decodeVector p R.inputDimension x)) z

end GroupWL.MachinePrograms.NatArrayParser
