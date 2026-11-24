import GroupWL.MachinePrograms.FullGadgetWL
import GroupWL.EquivalenceMembership

/-! Raw-input Version III equivalence on the original dense tensor encoding. -/
namespace GroupWL.MachinePrograms.VersionThreeEquivalence
open NatArrayLanguage
open NatArrayLowering (bitNat)
set_option maxRecDepth 12000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev Reg := TensorPairTables.Reg ⊕ SimpleGadget.Reg
abbrev Arr := TensorPairTables.Arr ⊕ SimpleGadget.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
def input : Arr := .inl RawTableEquivalence.input
def result : Reg := .inr (.inr (GraphWLCore.wl .result))
def valid : Reg := .inl (TensorPairTables.parser (EquivalenceParsing.r 3))

/-- The existing tensor materializer has already clamped the arity. -/
def prepare : List (Atom Reg Arr) := [
  .copy (.inr (.inl (.inl (.inl 0)))) (.inl (TensorPairTables.wl (TableWL.wl .leftCount))),
  .copy (.inr (.inl (.inr (.inl 0)))) (.inl (TensorPairTables.wl (TableWL.wl .rightCount))),
  .copy (.inr (.inr (GraphWLCore.wl .arity))) (.inl (TensorPairTables.wl (TableWL.wl .arity))),
  .copyArray (.inr (.inl (.inl (.inl ())))) (.inl (TensorPairTables.array (TableWL.array .fanouts))),
  .copyArray (.inr (.inl (.inr (.inl ())))) (.inl (TensorPairTables.array (TableWL.array .targets)))]

def compareTables : Code := .seq (atoms prepare) (SimpleGadget.decide.map Sum.inr Sum.inr)

def program (p : ℕ) [Fact p.Prime] (encoding : Statement.DimensionEncoding) : Code :=
  .seq (((EquivalenceParsing.program p encoding).map Sum.inl Sum.inl).map Sum.inl Sum.inl)
    (.branch valid (.seq ((TensorPairTables.program p).map Sum.inl Sum.inl) compareTables)
      (.atom (.const result 0)))

private theorem compareTables_runs {G H : Type} [Group G] [Fintype G] [DecidableEq G]
    [Group H] [Fintype H] [DecidableEq H] {p N n m k : ℕ}
    (e : G ≃ Fin n) (e' : H ≃ Fin m) (S : State) (hp : 2 ≤ p)
    (hn : n ≤ p^N) (hm : m ≤ p^N) (hk : k ≤ N+10) (positive : 0 < k)
    (bounded : S.Bounded (WLExponentialBudgets.budget p (2*N+3)))
    (ready : TableWL.Input (k:=k) (GroupInitial.encodedMul e) (GroupInitial.encodedMul e')
      (WLExponentialBudgets.budget p (2*N+3)) S.left.right.right) :
    let B := WLExponentialBudgets.budget p (2*N+3)
    ∃ t ≤ 1500*(B+1)^7+5, ∃ T, Runs (storageBound Reg Arr B) compareTables S t T ∧
      T.Bounded B ∧ (T.scalar result ≠ 0 ↔ Refinement.GroupEquivalent .three k G H) := by
  let B := WLExponentialBudgets.budget p (2*N+3)
  obtain ⟨first, hA⟩ := atoms_runs bounded prepare (by simp [prepare, ValidAtoms, Atom.Valid, Atom.SmallResult])
  let A := applyAtoms prepare S
  obtain ⟨lr,rr,matrix,room⟩ := SimpleGadget.exponentialRoom hp
    (by have := (e 1).isLt; omega : 0<n) (by have := (e' 1).isLt; omega : 0<m) hn hm hk
  have leftOrder := ready.left_order
  have rightOrder := ready.right_order
  have arity := ready.arity
  have leftTable := ready.left_table
  have rightTable := ready.right_table
  obtain ⟨t,ht,T,run,hT,answer⟩ := SimpleGadget.pair_runs_III e e' A.right B positive hA.right
    (by simpa [A,prepare,applyAtoms,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,TensorPairTables.wl] using leftOrder)
    (by simpa [A,prepare,applyAtoms,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,TensorPairTables.wl] using rightOrder)
    (by simpa [A,prepare,applyAtoms,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,TensorPairTables.wl] using arity)
    (by simpa [A,prepare,applyAtoms,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,TensorPairTables.array] using leftTable)
    (by simpa [A,prepare,applyAtoms,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,TensorPairTables.array] using rightTable)
    lr rr matrix room
  exact ⟨5+t,by change 5+t ≤ 1500*(B+1)^7+5; omega,A.left.join T,.seq first (run.right_bounded hA),hA.left.join hT,answer⟩

private theorem budget_le (p N : ℕ) :
    WLExponentialBudgets.budget p N ≤ WLExponentialBudgets.budget p (2*N+3) := by
  apply pow_le_pow_right' (by decide)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)

theorem program_runs (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)]
    (encoding : Statement.DimensionEncoding) (w : List Bool) (S : State)
    (bounded : S.Bounded (WLExponentialBudgets.budget p (2*w.length+3)))
    (inputEq : S.array input = w.map bitNat) :
    let B := WLExponentialBudgets.budget p (2*w.length+3)
    ∃ t ≤ 5000*(B+1)^7, ∃ V, Runs (storageBound Reg Arr B) (program p encoding) S t V ∧
      V.Bounded B ∧ (V.scalar result ≠ 0 ↔ w ∈ Statement.equivalenceLanguage p .three encoding) := by
  let B := WLExponentialBudgets.budget p (2*w.length+3)
  have parserRoom : TensorParsingBudgets.magnitude p w.length ≤ B :=
    (WLExponentialBudgets.parser_room p w.length).1.trans (budget_le p w.length)
  have cap : w.length+10 ≤ B := (WLExponentialBudgets.parser_room p w.length).2.trans (budget_le p w.length)
  have baseRoom : TensorParsingBudgets.base p w.length ≤ B :=
    (show TensorParsingBudgets.base p w.length≤TensorParsingBudgets.magnitude p w.length from by
      simpa only [TensorParsingBudgets.magnitude,pow_one] using
        pow_le_pow_right' (TensorParsingBudgets.base_positive p w.length) (by decide : 1≤4)).trans parserRoom
  have fieldRoom := (TensorParsingBudgets.field_room p w.length).trans parserRoom
  obtain ⟨A,t,ht,parse,hA,_,_,spec⟩ := EquivalenceParsing.program_runs p encoding S.left.left w B bounded.left.left
    ((TensorParsingBudgets.length_cube_le_magnitude p w.length).trans parserRoom) (by omega)
    ((TensorParsingBudgets.field_power_room p w.length).trans parserRoom)
    ((TensorParsingBudgets.binary_room p w.length).trans parserRoom) inputEq
  let C := (A.join S.left.right).join S.right
  have parse' := (parse.left_bounded bounded.left).left_bounded bounded
  have hC : C.Bounded B := (hA.join bounded.left.right).join bounded.right
  have parseCost : t ≤ 1000*(B+1)^5 := by
    have scan := (TensorParsingBudgets.scanCost_le p w.length).trans
      (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left baseRoom 4))
    have powers : B^4≤(B+1)^5 := (Nat.pow_le_pow_left (by omega : B≤B+1) 4).trans (pow_le_pow_right' (by omega) (by omega))
    have linear : B+1≤(B+1)^5 := by simpa only [pow_one] using pow_le_pow_right' (by omega : 1≤B+1) (by decide : 1≤5)
    unfold EquivalenceParsing.parseCost at ht
    nlinarith
  cases parsed : Statement.readEquivalence p encoding w with
  | none =>
    have zero : C.scalar valid=0 := by simpa only [parsed] using spec
    have last := atom_runs hC (.const result 0) trivial (by simp [Atom.SmallResult])
    have hV := (Atom.const result 0 : Atom Reg Arr).apply_bounded hC (by simp [Atom.SmallResult])
    refine ⟨t+2,?_,(Atom.const result 0).apply C,.seq parse' (.branch_zero zero last),hV,?_⟩
    · have powers : (B+1)^5≤(B+1)^7 := pow_le_pow_right' (by omega) (by omega)
      have pos : 1≤(B+1)^7 := one_le_pow₀ (by omega)
      change t+2 ≤ 5000*(B+1)^7
      omega
    · simp [Atom.apply,Store.setScalar,Statement.equivalenceLanguage_iff_parsed,parsed]
  | some triple =>
    rcases triple with ⟨T,U,k⟩
    have data : C.scalar valid=1 ∧ C.left.scalar (TensorPairTables.parser (EquivalenceParsing.r 2))=k ∧
        EquivalenceParsing.EncodesFirst p C.left.left T ∧ IdentificationParsing.EncodesTensor p C.left.left.left U := by
      simpa only [parsed] using spec
    obtain ⟨dimT,dimU⟩ := RawTableEquivalence.parsed_dimensions p encoding w T U k parsed
    have capT : T.inputDimension+T.outputDimension+10 ≤ B := by omega
    have powerT := (TensorParsingBudgets.table_room p T.inputDimension T.outputDimension w.length dimT).trans parserRoom
    have powerU := (TensorParsingBudgets.table_room p U.inputDimension U.outputDimension w.length dimU).trans parserRoom
    obtain ⟨u,hu,D,tables,hD,ready⟩ := TensorPairTables.program_runs p C.left B T U k hC.left
      ⟨data.2.2.1,data.2.2.2,data.2.1⟩ fieldRoom
      capT (by omega) powerT powerU
    let E := D.join C.right
    have hE : E.Bounded B := hD.join hC.right
    have hprime := (Fact.out : p.Prime)
    have nbound : p^(T.inputDimension+T.outputDimension) ≤ p^w.length := pow_le_pow_right' hprime.one_le dimT
    have mbound : p^(U.inputDimension+U.outputDimension) ≤ p^w.length := pow_le_pow_right' hprime.one_le dimU
    have kbound : min k T.wlCap ≤ w.length+10 := by
      apply (Nat.min_le_right k T.wlCap).trans
      unfold Statement.TensorDescription.wlCap
      omega
    obtain ⟨bits,encoded,_⟩ := (Statement.readEquivalence_eq_some_iff p encoding w T U k).mp parsed
    have positive : 0 < k := by cases encoding with | binary => exact encoded.2.2 | unary => exact encoded.2
    have kpos : 0 < min k T.wlCap := by unfold Statement.TensorDescription.wlCap; omega
    obtain ⟨v,hv,V,wl,hV,correct⟩ := compareTables_runs (TensorGroupCode.groupEquiv p T)
      (TensorGroupCode.groupEquiv p U) E hprime.two_le nbound mbound kbound kpos hE ready
    have tableT := (TensorParsingBudgets.tableCost_le p T.inputDimension T.outputDimension w.length dimT).trans
      (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left baseRoom 5))
    have tableU := (TensorParsingBudgets.tableCost_le p U.inputDimension U.outputDimension w.length dimU).trans
      (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left baseRoom 5))
    refine ⟨t+(u+v+1),?_,V,.seq parse' (.branch_nonzero (by change C.scalar valid ≠ 0; omega)
      (.seq (tables.left_bounded hC) wl)),hV,?_⟩
    · change v ≤ 1500*(B+1)^7+5 at hv
      change t+(u+v+1) ≤ 5000*(B+1)^7
      have p5 : B^5 ≤ (B+1)^7 := (Nat.pow_le_pow_left (by omega : B≤B+1) 5).trans (pow_le_pow_right' (by omega) (by omega))
      have p5' : (B+1)^5 ≤ (B+1)^7 := pow_le_pow_right' (by omega) (by omega)
      have pos : 1 ≤ (B+1)^7 := one_le_pow₀ (by omega)
      omega
    · rw [correct,←Statement.equivalence_clamp T U .three k,Statement.equivalenceLanguage_iff_parsed]
      constructor
      · exact fun h => ⟨T,U,k,parsed,h⟩
      · rintro ⟨T',U',k',hparse,h⟩
        rw [parsed] at hparse
        cases hparse
        exact h

theorem versionIII_inEXPTIME (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)]
    (encoding : Statement.DimensionEncoding) :
    Complexity.InEXPTIME (Statement.equivalenceLanguage p .three encoding) := by
  let K := max 5000 (Fintype.card Reg+3*Fintype.card Arr)
  let c := (K+7*(WLExponentialBudgets.coefficient p+1))*256
  apply NatArrayLowering.inEXPTIME (program p encoding) input result _ c 4
  intro w
  let B := WLExponentialBudgets.budget p (2*w.length+3)
  have cap : w.length+10 ≤ B := (WLExponentialBudgets.parser_room p w.length).2.trans (budget_le p w.length)
  let S : State := NatArrayLowering.inputStore input w
  have hS : S.Bounded B := by
    refine ⟨fun _=>Nat.zero_le _,?_,?_⟩
    · intro a
      by_cases h : a=input
      · subst a; simpa [S,NatArrayLowering.inputStore] using (show w.length ≤ B by omega)
      · simp [S,NatArrayLowering.inputStore,h]
    · intro a x hx
      by_cases h : a=input
      · subst a
        simp only [S,NatArrayLowering.inputStore,Function.update_self] at hx
        obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
        cases b <;> simp [bitNat]
        omega
      · simp [S,NatArrayLowering.inputStore,h] at hx
  obtain ⟨t,ht,T,run,_,correct⟩ := program_runs p encoding w S hS (by simp [S,NatArrayLowering.inputStore])
  have poly := SimpleGadget.exponentialCost w.length p K 7
  have time : t ≤ 2^(c*(w.length+1)^4) :=
    ht.trans ((Nat.mul_le_mul_right _ (show 5000≤K from Nat.le_max_left _ _)).trans poly)
  have space : storageBound Reg Arr B ≤ 2^(c*(w.length+1)^4) := by
    have power : (B+1)^2 ≤ (B+1)^7 := pow_le_pow_right' (by omega) (by decide)
    exact (Nat.mul_le_mul (show Fintype.card Reg+3*Fintype.card Arr≤K from Nat.le_max_right _ _) power).trans poly
  exact ⟨storageBound Reg Arr B,t,T,space,time,run,correct⟩

end GroupWL.MachinePrograms.VersionThreeEquivalence

namespace GroupWL.Statement

theorem equivalence_three_inEXPTIME (p : ℕ) (hp : p.Prime) (hodd : p≠2) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ encoding, Complexity.InEXPTIME (equivalenceLanguage p .three encoding) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (2 : ZMod p) := ⟨two_ne_zero_of_prime_ne_two p hp hodd⟩
  exact MachinePrograms.VersionThreeEquivalence.versionIII_inEXPTIME p

end GroupWL.Statement
