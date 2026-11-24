import GroupWL.MachinePrograms.StructuredComposition
import GroupWL.MachinePrograms.CompilerAssembly
import GroupWL.ComputableMachineReduction
import GroupWL.EquivalenceMembership

/-! Compile a transducer on canonical circuit words into a one-tape reduction
on arbitrary bit strings. Only compiler outputs enter the circuit transducer. -/
namespace GroupWL.MachinePrograms.CircuitWriterReduction

open Complexity AddressedCircuit Statement Refinement Structured

inductive Task where | identification | equivalence

def outputWord (p : ℕ) [Fact p.Prime] (a : Task) (v : Version) (enc : DimensionEncoding)
    {G : Type} [FiniteCode G] {n : ℕ} (C : Circuit G (n+3)) : BitString :=
  match a with
  | .identification => ComputableCircuitReduction.identificationOutput p C v enc
  | .equivalence => ComputableCircuitReduction.equivalenceOutput p C v enc

/-- The circuit routine is only invoked on canonical inputs. -/
structure Writer (p : ℕ) [Fact p.Prime] (a : Task) (v : Version) (enc : DimensionEncoding) where
  Registers : Type
  [finite : Fintype Registers]
  [eq : DecidableEq Registers]
  program : Structured.Program Registers
  input : Registers
  output : Registers
  coefficient : ℕ
  degree : ℕ
  run : ∀ {G : Type} [FiniteCode G] [Fintype G] {n : ℕ} (C : Circuit G (n+3)),
    ∃ S t, t ≤ coefficient*((CircuitDescription.circuitWord C).length+1)^degree ∧
      Structured.Runs program (Function.update (fun _ => []) input
        (CircuitDescription.circuitWord C).reverse) t S ∧
      (S output).reverse = outputWord p a v enc C

attribute [instance] Writer.finite Writer.eq

theorem machineWord_eq (M : Machine) (c e : ℕ) (w : BitString) :
    CircuitDescription.machineWord M c e w =
      CircuitDescription.circuitWord (MachineReduction.circuit M c e w) := by
  have castWord {T : Type} [FiniteCode T] {k l : ℕ} (h : k=l) (C : Circuit T k) :
      CircuitDescription.circuitWord (MachineReduction.castCircuit h C) =
        CircuitDescription.circuitWord C := by subst l; rfl
  exact (castWord _ _).symm

private theorem composition_budget (n s t u C E A D P F : ℕ)
    (hs : s ≤ A*(n+1)^D) (ht : t ≤ C*(n+1)^E) (hu : u ≤ P*(s+1)^F) :
    t + (7*s+2+u) ≤ (C+7*A+2+P*(A+1)^F)*(n+1)^(E+D+D*F) := by
  have hN : 1 ≤ n+1 := by omega
  have hD : 1 ≤ (n+1)^D := one_le_pow₀ hN
  have expand : s+1 ≤ (A+1)*(n+1)^D := by rw [Nat.add_mul]; omega
  have last := hu.trans (Nat.mul_le_mul_left P (Nat.pow_le_pow_left expand F))
  rw [mul_pow,←pow_mul,←Nat.mul_assoc] at last
  let j := E+D+D*F
  have leE : (n+1)^E ≤ (n+1)^j := Nat.pow_le_pow_right hN (by dsimp [j]; omega)
  have leD : (n+1)^D ≤ (n+1)^j := Nat.pow_le_pow_right hN (by dsimp [j]; omega)
  have leF : (n+1)^(D*F) ≤ (n+1)^j := Nat.pow_le_pow_right hN (by dsimp [j]; omega)
  have t' := ht.trans (Nat.mul_le_mul_left C leE)
  have s' := hs.trans (Nat.mul_le_mul_left A leD)
  have u' := last.trans (Nat.mul_le_mul_left _ leF)
  have one : 1 ≤ (n+1)^j := one_le_pow₀ hN
  change _ ≤ _ * (n+1)^j
  simp only [Nat.add_mul, Nat.mul_assoc 7 A]
  omega

theorem Writer.machine {p : ℕ} [Fact p.Prime] {a : Task} {v : Version} {enc : DimensionEncoding}
    (W : Writer p a v enc) (M : Machine) (c e : ℕ) :
    ∃ (N : Machine) (C D : ℕ), ComputesBy N
      (fun w => outputWord p a v enc (MachineReduction.circuit M c e w))
      (fun n => C*(n+1)^D) := by
  let A := CircuitDescription.machineSizeConstant M*(c+4)^3
  let D := 3*(e+1)
  let C := compilerCoefficient M c e
  let f := fun w => outputWord p a v enc (MachineReduction.circuit M c e w)
  let prog := (compilerProgram M c e).composeWords 0 W.program W.input
  let B := C+7*A+2+W.coefficient*(A+1)^W.degree
  let d := D+D+D*W.degree
  apply Exists.intro (Stacks.compiled (compile prog true) (.inl 0) (.inr (.inl W.output)))
  refine ⟨_,_,computesBy_polynomial prog (.inl 0) (.inr (.inl W.output)) f B d ?_⟩
  intro w
  let circ := MachineReduction.circuit M c e w
  obtain ⟨t,ht,hfirst⟩ := compilerProgram_runs M c e w
  obtain ⟨S,u,hu,hsecond,hout⟩ := W.run circ
  have hw := machineWord_eq M c e w
  obtain ⟨T,hT,hval⟩ := composeWords_runs 0 0 W.input W.output hfirst
    (by simpa only [Function.update_self,List.reverse_reverse] using hw) hsecond hout
  refine ⟨T,_,?_,hT,hval⟩
  apply composition_budget _ _ _ _ C D A D W.coefficient W.degree _ ht hu
  rw [← hw]
  exact CircuitDescription.machineWord_polynomial M c e w

theorem identification_hard {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)] (hp : Odd p)
    (v : Version) (enc : DimensionEncoding) (W : Writer p .identification v enc) :
    HardWithOutputs (identificationLanguage p v enc) (hardIdentificationInputs p enc) := by
  rintro L ⟨M,c,e,hM⟩
  obtain ⟨N,C,D,h⟩ := W.machine M c e
  exact ⟨N,_,C,D,h,ComputableMachineReduction.identificationMap_correct p hp M L c e hM v enc,
    ComputableMachineReduction.identificationMap_hard p M c e v enc⟩

theorem equivalence_hard {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)] (hp : Odd p)
    (v : Version) (enc : DimensionEncoding) (W : Writer p .equivalence v enc) :
    HardWithOutputs (equivalenceLanguage p v enc) (nonisomorphicPairInputs p enc) := by
  rintro L ⟨M,c,e,hM⟩
  obtain ⟨N,C,D,h⟩ := W.machine (complement M) c e
  exact ⟨N,_,C,D,h,ComputableMachineReduction.equivalenceMap_correct p hp M L c e hM v enc,
    ComputableMachineReduction.equivalenceMap_nonisomorphic p M c e v enc⟩

end GroupWL.MachinePrograms.CircuitWriterReduction
