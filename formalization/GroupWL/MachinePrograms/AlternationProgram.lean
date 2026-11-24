import GroupWL.MachinePrograms.AlternationVectors
import GroupWL.MachinePrograms.TensorValidation

/-! The counted exhaustive validator decides alternation of the parsed tensor. -/
namespace GroupWL.MachinePrograms.AlternationCheck

open NatArrayLanguage
open scoped BigOperators

theorem coordinateProduct_eq_one (C : List ℕ) (p n m x j : ℕ) :
    coordinateProduct C p n m x j=1 ↔
      ∀z<j,BilinearEvaluation.partialValue C p n m x x z n=0 := by
  rw [coordinateProduct,Finset.prod_eq_one_iff_of_le_one' (fun i hi => zeroFlag_le_one _)]
  simp

theorem vectorProduct_eq_one (C : List ℕ) (p n m q : ℕ) :
    vectorProduct C p n m q=1 ↔
      ∀x<q,∀z<m,BilinearEvaluation.partialValue C p n m x x z n=0 := by
  rw [vectorProduct,Finset.prod_eq_one_iff_of_le_one' (fun i hi => coordinateProduct_le_one _ _ _ _ _ _)]
  simp [coordinateProduct_eq_one]

theorem program_runs (S : State) (M : ℕ) (bounded : S.Bounded M)
    (positive : 0<S.scalar (l .modulus))
    (room : (S.scalar (l .modulus))^3+S.scalar (l .modulus)≤M)
    (powerRoom : (S.scalar (l .modulus))^(S.scalar (l .inputDimension))≤M)
    (length : (S.array (.inl .coefficients)).length=
      S.scalar (l .inputDimension)*S.scalar (l .inputDimension)*S.scalar (l .outputDimension))
    (small : ∀x∈S.array (.inl .coefficients),x<S.scalar (l .modulus)) :
    ∃t≤(S.scalar (l .modulus))^(S.scalar (l .inputDimension))*
        (S.scalar (l .outputDimension)*(14*(S.scalar (l .inputDimension))^2+
          9*S.scalar (l .inputDimension)+11)+7)+3*S.scalar (l .inputDimension)+10,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.scalar (a .valid)≤1 ∧ (T.scalar (a .valid)=1 ↔
        ∀x<(S.scalar (l .modulus))^(S.scalar (l .inputDimension)),∀z<S.scalar (l .outputDimension),
          BilinearEvaluation.partialValue (S.array (.inl .coefficients)) (S.scalar (l .modulus))
            (S.scalar (l .inputDimension)) (S.scalar (l .outputDimension)) x x z
            (S.scalar (l .inputDimension))=0) := by
  have hM : 1≤M := by omega
  obtain ⟨U,u,hu,first,hU,ubase,uexp,uorder,uremain,uone⟩ := NatArrayPower.program_runs powerRegs S
    (S.scalar (l .modulus)) (S.scalar (l .inputDimension)) M bounded rfl rfl (by omega) powerRoom
  change U.scalar (l .modulus)=S.scalar (l .modulus) at ubase
  change U.scalar (l .inputDimension)=S.scalar (l .inputDimension) at uexp
  change U.scalar (a .order)=(S.scalar (l .modulus))^(S.scalar (l .inputDimension)) at uorder
  have um : U.scalar (l .outputDimension)=S.scalar (l .outputDimension) :=
    first.scalar_eq_of_not_mem _ (by decide)
  have uc : U.array (.inl .coefficients)=S.array (.inl .coefficients) :=
    first.array_eq_of_not_mem _ (by decide)
  let as : List (Atom Reg Arr) := [.const (a .valid) 1,.const (a .zero) 0,.const (l .one) 1]
  let V := applyAtoms as U
  obtain ⟨initRun,hV⟩ := atoms_runs hU as
    (by simp [as,ValidAtoms,Atom.Valid,Atom.SmallResult,hM])
  have vp : V.scalar (l .modulus)=S.scalar (l .modulus) := by
    simpa [V,applyAtoms,as,Atom.apply,Store.setScalar,a,l] using ubase
  have vn : V.scalar (l .inputDimension)=S.scalar (l .inputDimension) := by
    simpa [V,applyAtoms,as,Atom.apply,Store.setScalar,a,l] using uexp
  have vm : V.scalar (l .outputDimension)=S.scalar (l .outputDimension) := by
    simpa [V,applyAtoms,as,Atom.apply,Store.setScalar,a,l] using um
  have vo : V.scalar (a .order)=(S.scalar (l .modulus))^(S.scalar (l .inputDimension)) := by
    simpa [V,applyAtoms,as,Atom.apply,Store.setScalar,a,l] using uorder
  have vc : V.array (.inl .coefficients)=S.array (.inl .coefficients) := by
    simpa [V,applyAtoms,as,Atom.apply] using uc
  have vv : V.scalar (a .valid)=1 := by simp [V,applyAtoms,as,Atom.apply,Store.setScalar,a,l]
  have vz : V.scalar (a .zero)=0 := by simp [V,applyAtoms,as,Atom.apply,Store.setScalar,a,l]
  have v1 : V.scalar (l .one)=1 := by simp [V,applyAtoms,as,Atom.apply,Store.setScalar,a,l]
  obtain ⟨t,ht,T,last,hT,tone,tvalid⟩ := vectors_runs V M hV v1 (by omega)
    (by rwa [vp]) (by simpa only [vc,vn,vm] using length)
    (by simpa only [vc,vp] using small) (by omega) vz
  rw [vo,vm,vn] at ht
  rw [vv,vc,vp,vn,vm,vo,one_mul] at tvalid
  refine ⟨u+(3+t),by omega,T,.seq first (.seq initRun last),hT,?_,?_⟩
  · rw [tvalid]
    exact vectorProduct_le_one _ _ _ _ _
  · rw [tvalid,vectorProduct_eq_one]

theorem rawTensor_runs (p : ℕ) [Fact p.Prime] (R : NatArrayParser.RawTensor)
    (hf : R.WellFormed p) (S : State) (M : ℕ) (bounded : S.Bounded M)
    (hp : S.scalar (l .modulus)=p) (hn : S.scalar (l .inputDimension)=R.inputDimension)
    (hm : S.scalar (l .outputDimension)=R.outputDimension)
    (hc : S.array (.inl .coefficients)=R.coefficients)
    (room : p^3+p≤M) (powerRoom : p^R.inputDimension≤M) :
    ∃t≤p^R.inputDimension*(R.outputDimension*(14*R.inputDimension^2+9*R.inputDimension+11)+7)+
        3*R.inputDimension+10,∃T,
      Runs (storageBound Reg Arr M) program S t T ∧ T.Bounded M ∧
      T.scalar (a .valid)≤1 ∧ (T.scalar (a .valid)=1 ↔ R.Alternating p) := by
  obtain ⟨t,ht,T,run,hT,hvalid,hiff⟩ := program_runs S M bounded
    (by rw [hp]; exact (Fact.out : p.Prime).pos)
    (by rwa [hp]) (by rwa [hp,hn])
    (by simpa [hc,hn,hm] using hf.1)
    (by simpa [hc,hp] using hf.2)
  refine ⟨t,by simpa [hp,hn,hm] using ht,T,run,hT,hvalid,?_⟩
  rw [hiff,←R.allSelfZero_iff p hf]
  simp only [NatArrayParser.RawTensor.AllSelfZero,hp,hn,hm,hc]
  exact ⟨fun h x z => h x.val x.isLt z.val z.isLt,
    fun h x hx z hz => h ⟨x,hx⟩ ⟨z,hz⟩⟩

end GroupWL.MachinePrograms.AlternationCheck
