import GroupWL.MachinePrograms.PivotMatrix
import Mathlib.Data.ZMod.Basic

/-! Fixed-prime inversion is a finite program of comparisons and constants. -/
namespace GroupWL.MachinePrograms.PivotMatrix

def inverseTable (p : ℕ) : List ℕ := List.ofFn (fun x : Fin p => (-((x:ℕ):ZMod p)⁻¹).val)

def withInverse (p : ℕ) : Code := .seq
  (.atom (.read .value .row .pivot))
  (.seq (NatArrayLanguage.finiteTable .value .negInverse .flag (inverseTable p)) program)

open NatArrayLanguage

theorem inverseTable_length (p : ℕ) : (inverseTable p).length=p := by simp [inverseTable]

theorem inverseTable_small (p : ℕ) [NeZero p] (x : ℕ) (hx : x∈inverseTable p) : x<p := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact ZMod.val_lt _

theorem inverseTable_lookup (p x : ℕ) (hx : x<p) :
    ((inverseTable p)[x]?).getD 0=(-((x:ℕ):ZMod p)⁻¹).val := by
  simp [inverseTable,hx]

theorem withInverse_runs (p : ℕ) [NeZero p] (S : State) (M : ℕ)
    (bounded : S.Bounded M) (modulus : S.scalar .modulus=p)
    (width : S.scalar .width=(S.array .row).length)
    (pivot : S.scalar .pivot<(S.array .row).length)
    (small : p*p+p≤M)
    (size : S.scalar .width*(S.scalar .width-1)≤M)
    (values : ∀ x∈S.array .row,x<p) :
    ∃ t≤17*(S.scalar .width*(S.scalar .width-1))+3*p+11,∃ T,
      Runs (storageBound Reg Arr M) (withInverse p) S t T ∧ T.Bounded M ∧
      T.array .lift=List.ofFn (fun i : Fin (S.scalar .width*(S.scalar .width-1)) =>
        liftValue (S.array .row) (S.scalar .width-1) (S.scalar .pivot)
          (-((S.array .row)[S.scalar .pivot]?.getD 0:ZMod p)⁻¹).val p i) ∧
      T.array .lowerTranspose=List.ofFn (fun i : Fin (S.scalar .width*(S.scalar .width-1)) =>
        lowerValue (S.scalar .width-1) (S.scalar .pivot) i) := by
  have hp := NeZero.pos p
  have hpM : p≤M := by omega
  have h1 : 1≤M := by omega
  let a : Atom Reg Arr := .read .value .row .pivot
  have rread := atom_runs bounded a pivot trivial
  have hU := a.apply_bounded bounded trivial
  let U := a.apply S
  obtain ⟨ti,hti,V,rinv,hV,hv⟩ := finiteTable_runs Reg.value Reg.negInverse Reg.flag
    (by decide) (inverseTable p) U M hU h1 (by simpa [inverseTable_length])
    (fun x hx => (Nat.le_of_lt (inverseTable_small p x hx)).trans hpM)
  have input : U.scalar .value=(S.array .row)[S.scalar .pivot]?.getD 0 := by simp [U,a,Atom.apply]
  have input_lt : (S.array .row)[S.scalar .pivot]?.getD 0<p := MatrixArithmetic.read_lt values hp _
  rw [input,inverseTable_lookup p _ input_lt] at hv
  rw [inverseTable_length] at hti
  have arrays (a : Arr) : V.array a=S.array a := by
    exact (rinv.array_eq_of_not_mem a (by simp)).trans rfl
  have regs (r : Reg) (hne : r≠Reg.value ∧ r≠Reg.negInverse ∧ r≠Reg.flag) : V.scalar r=S.scalar r := by
    rcases hne with ⟨hi,ho,hf⟩
    have h := rinv.scalar_eq_of_not_mem r (finiteTable_not_scalarWrites _ _ _ _ ho hf _)
    simpa [U,a,Atom.apply,Store.setScalar,hi] using h
  have hwidth := regs .width (by decide)
  have hj := regs .pivot (by decide)
  have hmod := (regs .modulus (by decide)).trans modulus
  obtain ⟨t,ht,T,run,hT,hl,hr⟩ := program_runs V M hV
    (by rwa [hwidth,arrays]) (by rwa [hmod]) (by rwa [hmod])
    (by rwa [hwidth]) (by rw [hv,hmod]; exact Nat.le_of_lt (ZMod.val_lt _))
    (by rwa [arrays,hmod])
  simp only [hwidth,hj,hmod,hv,arrays] at ht hl hr
  exact ⟨1+(ti+t),by omega,T,.seq rread (.seq rinv run),hT,hl,hr⟩

end GroupWL.MachinePrograms.PivotMatrix
