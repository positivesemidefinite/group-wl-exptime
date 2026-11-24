import GroupWL.GeneratedCoordinateEntries
import GroupWL.MachinePrograms.EvaluationAssemblyCorrectness
import GroupWL.MatrixEncoding

/-! The Gaussian lift array is already in the exact order consumed by
concrete tensor assembly; no transpose or permutation algorithm is required. -/
namespace GroupWL.MachinePrograms.OperatorAssemblyEncoding
open ConstructiveCoordinates GeneratedCoordinates GeneratedCoordinateEntries
open CachedElimination EvaluationTensorCoefficients EvaluationAssembly
variable (p : ℕ) [Fact p.Prime]
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [FiniteCode ι] [FiniteCode κ]
variable {W : Type} [AddCommGroup W] [Module (ZMod p) W]
variable (D : Coordinates (ZMod p) W) (σ : W →ₗ[ZMod p] ObstructionDuality.MatrixSpace (ZMod p) ι κ)

theorem operatorEntries_eq_lift_word :
    operatorEntries p (Coordinates.pi ι) (Coordinates.pi κ)
      (MatrixEvaluationGroup.operatorSpace σ.range) (operatorCoordinates D σ)=
      MatrixEncoding.word (ofLinear (operatorChart D σ).lift) := by
  let a := FiniteCode.size ι
  let m := FiniteCode.size κ
  let b := (operatorCoordinates D σ).dimension
  have hdim := matrixCoordinates_dimension (F:=ZMod p) (ι:=ι) (κ:=κ)
  have hl : (operatorEntries p (Coordinates.pi ι) (Coordinates.pi κ)
      (MatrixEvaluationGroup.operatorSpace σ.range) (operatorCoordinates D σ)).length=a*m*b := by
    simp [operatorEntries,entries3,a,m,b,Coordinates.pi]
  have hr : (MatrixEncoding.word (ofLinear (operatorChart D σ).lift)).length=a*m*b := by
    rw [MatrixEncoding.word_length]
    change (matrixCoordinates (F:=ZMod p) (ι:=ι) (κ:=κ)).dimension*b=a*m*b
    exact congrArg (fun x => x*b) hdim
  apply List.ext_getElem (hl.trans hr.symm)
  intro k hk hk'
  have hb : k<a*m*b := by rwa [hl] at hk
  let kk : Fin (a*m*b) := ⟨k,hb⟩
  let i : Fin a := kk.divNat.divNat
  let z : Fin m := kk.divNat.modNat
  let j : Fin b := kk.modNat
  have he : k=(i.val*m+z.val)*b+j.val := by
    have h₁ := Nat.mod_add_div k b
    have h₂ := congrArg (fun x => x*b) (Nat.mod_add_div (k/b) m)
    dsimp [i,z,j,kk,Fin.divNat,Fin.modNat]
    nlinarith
  have hread := entries3_read
    (fun i z j => (operatorCoefficient (Coordinates.pi (F:=ZMod p) ι) (Coordinates.pi κ)
      (MatrixEvaluationGroup.operatorSpace σ.range) (operatorCoordinates D σ) j i z).val) i z j
  have hmatrix := MatrixEncoding.word_read (ofLinear (operatorChart D σ).lift)
    (matrixPosition (F:=ZMod p) i z) j
  conv_lhs at hmatrix => rw [matrixPosition_val]
  change MatrixArithmetic.read _ ((i.val*m+z.val)*b+j.val)=_ at hmatrix
  change EvaluationAssembly.read _ ((i.val*m+z.val)*b+j.val)=_ at hread
  rw [←he] at hmatrix hread
  simp only [MatrixArithmetic.read,List.getElem?_eq_getElem hk',Option.getD_some] at hmatrix
  change (operatorEntries p (Coordinates.pi ι) (Coordinates.pi κ)
    (MatrixEvaluationGroup.operatorSpace σ.range) (operatorCoordinates D σ))[k]?.getD 0=_ at hread
  simp only [List.getElem?_eq_getElem hk,Option.getD_some] at hread
  rw [hread,hmatrix]
  erw [ofLinear_entry]
  exact congrArg ZMod.val (operatorCoefficient_lift D σ j i z)

end GroupWL.MachinePrograms.OperatorAssemblyEncoding
