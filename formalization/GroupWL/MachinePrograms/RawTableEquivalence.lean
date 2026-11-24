import GroupWL.MachinePrograms.TensorPairTables
import GroupWL.MachinePrograms.TensorParsingBudgets
import GroupWL.MachinePrograms.NatArrayComplexity

/-! Full raw-input execution for Versions I and II, including rejection and clamping. -/
namespace GroupWL.MachinePrograms.RawTableEquivalence
open NatArrayLanguage
open NatArrayLowering (bitNat)
open TensorPairTables
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def input : Arr := raw EquivalenceParsing.input
def result : Reg := wl (TableWL.wl .result)
def version (word : Bool) : Refinement.Version := if word then .two else .one

def accept (p : ℕ) [Fact p.Prime] (word : Bool) : Code := .seq (TensorPairTables.program p)
  ((TableWL.decide word).map Sum.inr Sum.inr |>.map Sum.inr Sum.inr)
def program (p : ℕ) [Fact p.Prime] (encoding : Statement.DimensionEncoding) (word : Bool) : Code :=
  .seq ((EquivalenceParsing.program p encoding).map Sum.inl Sum.inl)
    (.branch (parser (EquivalenceParsing.r 3)) (accept p word) (.atom (.const result 0)))

structure Room (p N B : ℕ) : Prop where
  parser : TensorParsingBudgets.magnitude p N≤B
  cap : N+10≤B
  tuples : ∀n m k,0<n → 0<m → n≤p^N → m≤p^N → k≤N+10 →
    InitialMatrixPrograms.Room n m k B ∧ (max n m)^4≤B ∧ IndexedWL.Room (n^k+m^k) k (max n m) B

theorem parsed_dimensions (p : ℕ) [Fact p.Prime] (encoding : Statement.DimensionEncoding)
    (w : List Bool) (T U : Statement.TensorDescription p) (k : ℕ)
    (parsed : Statement.readEquivalence p encoding w=some (T,U,k)) :
    T.inputDimension+T.outputDimension≤w.length ∧ U.inputDimension+U.outputDimension≤w.length := by
  obtain ⟨bits,_,heq⟩ := (Statement.readEquivalence_eq_some_iff p encoding w T U k).mp parsed
  have hT := Statement.dimensions_le_encoded_length p T (U.denseWord p++bits)
  have hU := Statement.dimensions_le_encoded_length p U bits
  rw [heq]
  simp only [List.length_append] at *
  omega

private theorem semantic (word : Bool) (k : ℕ) (G H : Type) [Group G] [Group H] [Fintype G] [Fintype H] :
    (if word then Refinement.EquivalentII k G H else Refinement.EquivalentI k G H) ↔
      Refinement.GroupEquivalent (version word) k G H := by cases word <;> rfl

theorem program_runs (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)]
    (encoding : Statement.DimensionEncoding) (word : Bool) (w : List Bool) (S : State) (B : ℕ)
    (bounded : S.Bounded B) (room : Room p w.length B) (inputEq : S.array input=w.map bitNat) :
    ∃t≤5000*(B+1)^7,∃V,Runs (storageBound Reg Arr B) (program p encoding word) S t V ∧
      V.Bounded B ∧ (V.scalar result≠0 ↔ w∈Statement.equivalenceLanguage p (version word) encoding) := by
  have parserRoom := room.parser
  have lengthRoom : w.length≤B := by have := room.cap;omega
  have baseRoom : TensorParsingBudgets.base p w.length≤B :=
    (show TensorParsingBudgets.base p w.length≤TensorParsingBudgets.magnitude p w.length from by
      simpa only [TensorParsingBudgets.magnitude,pow_one] using
        pow_le_pow_right' (TensorParsingBudgets.base_positive p w.length) (by decide : 1≤4)).trans parserRoom
  have fieldRoom : p^3+3*p≤B := (TensorParsingBudgets.field_room p w.length).trans parserRoom
  obtain ⟨A,t,ht,parse,hA,valid,inputA,spec⟩ := EquivalenceParsing.program_runs p encoding S.left w B bounded.left
    ((TensorParsingBudgets.length_cube_le_magnitude p w.length).trans parserRoom) (by omega)
    ((TensorParsingBudgets.field_power_room p w.length).trans parserRoom)
    ((TensorParsingBudgets.binary_room p w.length).trans parserRoom) inputEq
  let C := A.join S.right
  have parse' := parse.left_bounded bounded
  have hC : C.Bounded B := hA.join bounded.right
  have parseCost : t≤1000*(B+1)^5 := by
    have scan := (TensorParsingBudgets.scanCost_le p w.length).trans
      (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left baseRoom 4))
    have powers : B^4≤(B+1)^5 := (Nat.pow_le_pow_left (by omega : B≤B+1) 4).trans (pow_le_pow_right' (by omega) (by omega))
    have linear : B+1≤(B+1)^5 := by simpa only [pow_one] using pow_le_pow_right' (by omega : 1≤B+1) (by decide : 1≤5)
    unfold EquivalenceParsing.parseCost at ht
    nlinarith
  cases parsed : Statement.readEquivalence p encoding w with
  | none =>
    have zero : C.scalar (parser (EquivalenceParsing.r 3))=0 := by simpa only [parsed] using spec
    have last := atom_runs hC (.const result 0) trivial (by simp [Atom.SmallResult])
    have hV := (Atom.const result 0 : Atom Reg Arr).apply_bounded hC (by simp [Atom.SmallResult])
    refine ⟨t+2,?_,(Atom.const result 0).apply C,.seq parse' (.branch_zero zero last),hV,?_⟩
    · have powers : (B+1)^5≤(B+1)^7 := pow_le_pow_right' (by omega) (by omega)
      have pos : 1≤(B+1)^7 := one_le_pow₀ (by omega)
      nlinarith
    · simp [Atom.apply,Store.setScalar,Statement.equivalenceLanguage_iff_parsed,parsed]
  | some triple =>
    rcases triple with ⟨T,U,k⟩
    have data : C.scalar (parser (EquivalenceParsing.r 3))=1 ∧ C.scalar (parser (EquivalenceParsing.r 2))=k ∧
        EquivalenceParsing.EncodesFirst p C.left T ∧ IdentificationParsing.EncodesTensor p C.left.left U := by
      simpa only [parsed] using spec
    obtain ⟨dimT,dimU⟩ := parsed_dimensions p encoding w T U k parsed
    have capT : T.inputDimension+T.outputDimension+10≤B := by have := room.cap;omega
    have powerT := (TensorParsingBudgets.table_room p T.inputDimension T.outputDimension w.length dimT).trans parserRoom
    have powerU := (TensorParsingBudgets.table_room p U.inputDimension U.outputDimension w.length dimU).trans parserRoom
    obtain ⟨u,hu,D,tables,hD,ready⟩ := TensorPairTables.program_runs p C B T U k hC ⟨data.2.2.1,data.2.2.2,data.2.1⟩
      fieldRoom capT (dimU.trans lengthRoom) powerT powerU
    have hp : 0<p := (Fact.out : p.Prime).pos
    have npositive : 0<p^(T.inputDimension+T.outputDimension) := pow_pos hp _
    have mpositive : 0<p^(U.inputDimension+U.outputDimension) := pow_pos hp _
    have nbound : p^(T.inputDimension+T.outputDimension)≤p^w.length := pow_le_pow_right' (by omega) dimT
    have mbound : p^(U.inputDimension+U.outputDimension)≤p^w.length := pow_le_pow_right' (by omega) dimU
    have kbound : min k T.wlCap≤w.length+10 := by
      apply (Nat.min_le_right k T.wlCap).trans
      unfold Statement.TensorDescription.wlCap
      omega
    obtain ⟨matrixRoom,productRoom,tupleRoom⟩ := room.tuples _ _ _ npositive mpositive nbound mbound kbound
    obtain ⟨v,hv,E,wlrun,hE,correct⟩ := TableWL.decide_runs word
      (TensorGroupCode.groupEquiv p T) (TensorGroupCode.groupEquiv p U)
      (TensorGroupProgram.codedEquiv_one_val p T) (TensorGroupProgram.codedEquiv_one_val p U)
      D.right.right B ready matrixRoom productRoom tupleRoom
    let V := D.left.join (D.right.left.join E)
    have last := (wlrun.right_bounded hD.right).right_bounded hD
    have hV : V.Bounded B := hD.left.join (hD.right.left.join hE)
    have tableT := (TensorParsingBudgets.tableCost_le p T.inputDimension T.outputDimension w.length dimT).trans
      (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left baseRoom 5))
    have tableU := (TensorParsingBudgets.tableCost_le p U.inputDimension U.outputDimension w.length dimU).trans
      (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left baseRoom 5))
    refine ⟨t+(u+v+1),?_,V,.seq parse' (.branch_nonzero (by change C.scalar (parser (EquivalenceParsing.r 3))≠0;omega) (.seq tables last)),hV,?_⟩
    · have p5 : B^5≤(B+1)^7 := (Nat.pow_le_pow_left (by omega : B≤B+1) 5).trans (pow_le_pow_right' (by omega) (by omega))
      have p5' : (B+1)^5≤(B+1)^7 := pow_le_pow_right' (by omega) (by omega)
      have pos : 1≤(B+1)^7 := one_le_pow₀ (by omega)
      nlinarith
    · change E.scalar (TableWL.wl .result)≠0 ↔ _
      rw [correct,semantic,←Statement.equivalence_clamp T U (version word) k,Statement.equivalenceLanguage_iff_parsed]
      constructor
      · intro h;exact ⟨T,U,k,parsed,h⟩
      · rintro ⟨T',U',k',hparse,h⟩
        rw [parsed] at hparse
        cases hparse
        exact h

end GroupWL.MachinePrograms.RawTableEquivalence
