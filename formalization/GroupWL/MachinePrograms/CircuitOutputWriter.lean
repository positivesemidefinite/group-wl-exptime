import GroupWL.MachinePrograms.CircuitWriterReduction
import GroupWL.MachinePrograms.OutputSerialization
import GroupWL.MachinePrograms.KernelToTensor
import GroupWL.MachinePrograms.NatArrayComplexity
import GroupWL.MachinePrograms.PolynomialBudget

namespace GroupWL.MachinePrograms.CircuitWriterReduction
open Complexity Statement Refinement NatArrayLanguage NatArrayLowering
open OutputSerialization (Reg Arr)

variable {R A : Type} [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A]

private abbrev Big (R A : Type) := StackIndex (R ⊕ Reg) (A ⊕ Arr)

private def embedPort : OutputSerialization.K → Big R A
  | .inl (.inl r) => scalarSlot (.inr r)
  | .inl (.inr a) => arraySlot (.inr a)
  | .inr i => scratchSlot i

private def withOutput (s : Store R A) (t : Structured.Store OutputSerialization.K) :
    Structured.Store (Big R A)
  | .inl (.inl (.inl r)) => List.replicate (s.scalar r) true
  | .inl (.inr (.inl a)) => Structured.arrayWord (s.array a)
  | .inl (.inl (.inr r)) => t (scalarSlot r)
  | .inl (.inr (.inr a)) => t (arraySlot a)
  | .inr i => t (scratchSlot i)

omit [DecidableEq R] [DecidableEq A] [Fintype R] [Fintype A] in
private theorem withOutput_encode (s : Store R A) (t : OutputSerialization.State) :
    withOutput s (encodeStore t) = encodeStore (s.join t) := by
  funext k
  rcases k with ((_|_)|(_|_))|_ <;> rfl

omit [Fintype R] [Fintype A] in
private theorem runOnPorts (s : Store R A) {t u : Structured.Store OutputSerialization.K}
    {p : Structured.Program OutputSerialization.K} {n : ℕ} (h : Structured.Runs p t n u) :
    Structured.Runs (p.relabel embedPort) (withOutput s t) n (withOutput s u) := by
  apply h.relabel embedPort (withOutput s)
  · intro V k; rcases k with (r|a)|i <;> rfl
  · intro V k bs
    funext x
    rcases k with (r|a)|i <;> rcases x with ((r'|r')|(a'|a'))|i' <;>
      simp [withOutput,embedPort,scalarSlot,arraySlot,scratchSlot,Function.update_apply]

/-- Source registers may be shared, for instance when the two tensors have identical dimensions. -/
structure Fields (R A : Type) where
  scalar : Reg → R
  array : Arr → A

def Fields.read (f : Fields R A) (S : Store R A) : OutputSerialization.State :=
  ⟨fun r => S.scalar (f.scalar r),fun a => S.array (f.array a)⟩

noncomputable def collect (p : NatArrayLanguage.Program R A) (f : Fields R A) : NatArrayLanguage.Program (R ⊕ Reg) (A ⊕ Arr) :=
  .seq (p.map Sum.inl Sum.inl) (Ports.code (fun u => .scalar (f.scalar u)) (fun v => some (f.array v)))

def serializer (a : Task) (enc : DimensionEncoding) : Structured.Program OutputSerialization.K :=
  match a with
  | .identification => OutputSerialization.identification enc
  | .equivalence => OutputSerialization.equivalence enc

noncomputable def finish (p : NatArrayLanguage.Program R A) (input : A) (f : Fields R A)
    (a : Task) (enc : DimensionEncoding) : Structured.Program (Big R A) :=
  .seq (decisionProgram (collect p f) (.inl input)) ((serializer a enc).relabel embedPort)

structure Describes (prime : ℕ) [Fact prime.Prime] (S : OutputSerialization.State)
    (T U : TensorDescription prime) (k : ℕ) : Prop where
  ix : S.scalar .input₁ = T.inputDimension
  ox : S.scalar .output₁ = T.outputDimension
  cx : S.array .coefficients₁ = TensorSerialization.coefficientList (T.coefficient prime)
  iy : S.scalar .input₂ = U.inputDimension
  oy : S.scalar .output₂ = U.outputDimension
  cy : S.array .coefficients₂ = TensorSerialization.coefficientList (U.coefficient prime)
  dim : S.scalar .dimension = k

omit [DecidableEq R] [Fintype R] [Fintype A] in
private theorem input_bounded (i : A) (w : BitString) {m : ℕ} (h : w.length+1 ≤ m) :
    (inputStore (Reg:=R) i w).Bounded m := by
  refine ⟨by simp [inputStore],?_,?_⟩
  · intro a
    by_cases ha : a=i <;> (simp [inputStore,ha] <;> omega)
  · intro a x hx
    by_cases ha : a=i
    · subst a
      simp only [inputStore,Function.update_self,List.mem_map] at hx
      obtain ⟨b,_,rfl⟩ := hx
      cases b <;> (simp [bitNat] <;> omega)
    · simp [inputStore,ha] at hx

private theorem collect_runs (p : NatArrayLanguage.Program R A) (input : A) (f : Fields R A)
    (w : BitString) (m t : ℕ) (S : Store R A) (h : w.length+1≤m)
    (run : Runs (storageBound R A m) p (inputStore input w) t S) (hS : S.Bounded m) :
    Runs (storageBound (R⊕Reg) (A⊕Arr) m) (collect p f) (inputStore (.inl input) w)
      (t + (Fintype.card Reg + Fintype.card Arr)) (S.join (f.read S)) := by
  let I : Store (R⊕Reg) (A⊕Arr) := inputStore (.inl input) w
  have first : Runs (storageBound R A m) p I.left t S := by
    convert run using 1
    apply Store.ext
    · intro r; rfl
    · intro a
      by_cases ha : a=input <;> simp [I,Store.left,inputStore,ha]
  have hI : I.Bounded m := input_bounded _ _ h
  have hfirst := first.left_bounded hI
  obtain ⟨hcopy,_⟩ := Ports.code_runs (fun u => .scalar (f.scalar u)) (fun v => some (f.array v))
    S I.right m (hS.join hI.right) (by simp)
  exact hfirst.seq hcopy

private def targetWord (prime : ℕ) [Fact prime.Prime] (a : Task) (enc : DimensionEncoding)
    (T U : TensorDescription prime) (k : ℕ) :=
  match a with
  | .identification => identificationWord prime enc T k
  | .equivalence => equivalenceWord prime enc T U k

private theorem words_run (p : ℕ) [Fact p.Prime] (a : Task) (enc : DimensionEncoding)
    (T U : TensorDescription p) (k : ℕ) (s : OutputSerialization.State)
    (hs : Describes p s T U k) :
    ∃ t ≤ 3*((T.denseWord p).length+(U.denseWord p).length)+10+110*(k+1)^2, ∃ V,
      Structured.Runs (serializer a enc) (encodeStore s) t V ∧
      (V (scratchSlot 0)).reverse = targetWord p a enc T U k := by
  cases a with
  | identification =>
    obtain ⟨t,ht,V,run,hout⟩ := OutputSerialization.identification_runs p enc s T k hs.ix hs.ox hs.cx hs.dim
    exact ⟨t,by omega,V,run,hout⟩
  | equivalence => exact OutputSerialization.equivalence_runs p enc s T U k hs.ix hs.ox hs.cx hs.iy hs.oy hs.cy hs.dim

private def denseBound (p m : ℕ) := m+m+2+m*(m*(m*p))
private def endBudget (p n m t : ℕ) :=
  4*n+1+10000*(storageBound (R⊕Reg) (A⊕Arr) m+1)^4*(t+(Fintype.card Reg+Fintype.card Arr))+
    (3*(denseBound p m+denseBound p m)+10+110*(m+1)^2)

private theorem finish_runs (p : NatArrayLanguage.Program R A) (input : A) (f : Fields R A)
    (prime : ℕ) [Fact prime.Prime] (a : Task) (enc : DimensionEncoding)
    (w : BitString) (m t : ℕ) (S : Store R A) (h : w.length+1≤m)
    (run : Runs (storageBound R A m) p (inputStore input w) t S) (hS : S.Bounded m)
    (T U : TensorDescription prime) (k : ℕ) (hdata : Describes prime (f.read S) T U k) :
    ∃ V u, u ≤ endBudget (R:=R) (A:=A) prime w.length m t ∧
      Structured.Runs (finish p input f a enc)
        (Function.update (fun _ => []) (scratchSlot 15) w.reverse) u V ∧
      (V (scratchSlot 0)).reverse = targetWord prime a enc T U k := by
  obtain ⟨first,hfirst,h₁⟩ := decisionProgram_runs (collect_runs p input f w m t S h run hS)
  obtain ⟨last,hlast,V,h₂,value⟩ := words_run prime a enc T U k (f.read S) hdata
  have hser := runOnPorts S h₂
  rw [withOutput_encode] at hser
  have hd (D : TensorDescription prime) (hx : D.inputDimension≤m) (hz : D.outputDimension≤m) :
      (D.denseWord prime).length ≤ denseBound prime m := by
    apply (denseWord_length_le prime D).trans
    unfold denseBound
    gcongr
  have dt := hd T (hdata.ix ▸ hS.1 (f.scalar .input₁)) (hdata.ox ▸ hS.1 (f.scalar .output₁))
  have du := hd U (hdata.iy ▸ hS.1 (f.scalar .input₂)) (hdata.oy ▸ hS.1 (f.scalar .output₂))
  have dim : k≤m := hdata.dim ▸ hS.1 (f.scalar .dimension)
  refine ⟨_,_,Nat.add_le_add hfirst (hlast.trans ?_),h₁.seq hser,value⟩
  gcongr

/-- Turn a bounded array computation of both dense coefficient lists into
either word transducer, with both dimension encodings. -/
noncomputable def writerOfArrays (prime : ℕ) [Fact prime.Prime] (v : Version)
    (p : NatArrayLanguage.Program R A) (input : A) (f : Fields R A) (c d : ℕ)
    (h : ∀ {G : Type} [FiniteCode G] [Fintype G] {n : ℕ} (C : AddressedCircuit.Circuit G (n+3)),
      ∃ m t S, (CircuitDescription.circuitWord C).length+1≤m ∧
      m≤c*((CircuitDescription.circuitWord C).length+1)^d ∧
      t≤c*((CircuitDescription.circuitWord C).length+1)^d ∧
      Runs (storageBound R A m) p (inputStore input (CircuitDescription.circuitWord C)) t S ∧
      S.Bounded m ∧ Describes prime (f.read S) (ComputableCircuitReduction.baseDescription prime C)
        (ComputableCircuitReduction.mateDescription prime C) (CircuitGroupReduction.dimension v (n+3)))
    (a : Task) (enc : DimensionEncoding) : Writer prime a v enc := by
  classical
  let H (n : ℕ) := c*(n+1)^d
  have polyH : PolynomialBudget H := ⟨c,d,fun _ => le_rfl⟩
  have cost : PolynomialBudget (fun n => endBudget (R:=R) (A:=A) prime n (H n) (H n)) := by
    have hOne := PolynomialBudget.const 1
    have hSucc := polyH.add hOne
    have cap := (PolynomialBudget.const (Fintype.card (R⊕Reg)+3*Fintype.card (A⊕Arr))).mul (hSucc.pow 2)
    have time := polyH.add (PolynomialBudget.const (Fintype.card Reg+Fintype.card Arr))
    have lower := ((PolynomialBudget.const 10000).mul ((cap.add hOne).pow 4)).mul time
    have dense := (((polyH.add polyH).add (PolynomialBudget.const 2))).add
      (polyH.mul (polyH.mul (polyH.mul (PolynomialBudget.const prime))))
    have final := (((PolynomialBudget.const 3).mul (dense.add dense)).add (PolynomialBudget.const 10)).add
      ((PolynomialBudget.const 110).mul (hSucc.pow 2))
    exact (((((PolynomialBudget.const 4).mul PolynomialBudget.input).add hOne).add lower).add final)
  let K := Classical.choose cost
  let D := Classical.choose (Classical.choose_spec cost)
  have bound : ∀ n, endBudget (R:=R) (A:=A) prime n (H n) (H n) ≤ K*(n+1)^D :=
    Classical.choose_spec (Classical.choose_spec cost)
  exact {
    Registers := Big R A, program := finish p input f a enc,
    input := scratchSlot 15, output := scratchSlot 0,
    coefficient := K, degree := D,
    run := by
      intro G _ _ n C
      obtain ⟨m,t,S,hN,hm,ht,run,hS,hdata⟩ := h C
      obtain ⟨V,u,hu,run',out⟩ := finish_runs p input f prime a enc _ m t S hN run hS _ _ _ hdata
      refine ⟨V,u,hu.trans (le_trans ?_ (bound _)),run',?_⟩
      · unfold endBudget storageBound denseBound H
        gcongr
      · cases a <;> exact out }

end GroupWL.MachinePrograms.CircuitWriterReduction
