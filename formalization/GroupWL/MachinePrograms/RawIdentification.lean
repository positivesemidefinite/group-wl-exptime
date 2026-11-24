import GroupWL.MachinePrograms.RawIdentificationTables
import GroupWL.MachinePrograms.IdentificationTableBounds
import GroupWL.MachinePrograms.RawTableMembership

/-! Full raw-input identification algorithm, including parsing and clamping. -/
namespace GroupWL.MachinePrograms.RawIdentification
open NatArrayLanguage RawIdentificationTables
open NatArrayLowering (bitNat)
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false

def input : Arr := .inl ValidatedTensorProgram.input
def version (word : Bool) := IdentificationTest.version word

def program (p : ℕ) [Fact p.Prime] (encoding : Statement.DimensionEncoding) (word : Bool) : Code :=
  .seq ((IdentificationParsing.program p encoding).map Sum.inl Sum.inl)
    (.branch (parser 3) (RawIdentificationTables.program p word) (.atom (.const result 0)))

theorem program_runs (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)]
    (encoding : Statement.DimensionEncoding) (word : Bool) (w : List Bool) (S : State)
    (hb : S.Bounded (WLExponentialBudgets.budget p w.length)) (inputEq : S.array input=w.map bitNat) :
    ∃t≤20000*(WLExponentialBudgets.budget p w.length+1)^8,∃V,
      Runs (storageBound Reg Arr (WLExponentialBudgets.budget p w.length)) (program p encoding word) S t V ∧
      V.Bounded (WLExponentialBudgets.budget p w.length) ∧
      (V.scalar result≠0 ↔ w∈Statement.identificationLanguage p (version word) encoding) := by
  let B := WLExponentialBudgets.budget p w.length
  obtain ⟨parserRoom,capRoom⟩ := WLExponentialBudgets.parser_room p w.length
  have lengthRoom : w.length≤B := by dsimp [B];omega
  have one : 1≤B := by dsimp [B];omega
  have baseRoom : TensorParsingBudgets.base p w.length≤B :=
    (show TensorParsingBudgets.base p w.length≤TensorParsingBudgets.magnitude p w.length from by
      simpa only [TensorParsingBudgets.magnitude,pow_one] using
        pow_le_pow_right' (TensorParsingBudgets.base_positive p w.length) (by decide : 1≤4)).trans parserRoom
  have field : p^3+3*p≤B := (TensorParsingBudgets.field_room p w.length).trans parserRoom
  obtain ⟨A,t,ht,parse,hA,valid,inputA,spec⟩ := IdentificationParsing.program_runs p encoding S.left w B hb.left
    ((TensorParsingBudgets.length_cube_le_magnitude p w.length).trans parserRoom) (by omega)
    ((TensorParsingBudgets.field_power_room p w.length).trans parserRoom)
    ((TensorParsingBudgets.binary_room p w.length).trans parserRoom) inputEq
  let C := A.join S.right
  have hC : C.Bounded B := hA.join hb.right
  have parse' := parse.left_bounded hb
  have parseCost : t≤1000*(B+1)^5 := by
    have scan := (TensorParsingBudgets.scanCost_le p w.length).trans
      (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left baseRoom 4))
    have powers : B^4≤(B+1)^5 := (Nat.pow_le_pow_left (by omega : B≤B+1) 4).trans (pow_le_pow_right' (by omega) (by omega))
    have linear : B+1≤(B+1)^5 := by simpa only [pow_one] using pow_le_pow_right' (by omega : 1≤B+1) (by decide : 1≤5)
    unfold IdentificationParsing.parseCost at ht
    nlinarith
  have powers58 : (B+1)^5≤(B+1)^8 := pow_le_pow_right' (by omega) (by decide)
  have positive : 1≤(B+1)^8 := one_le_pow₀ (by omega)
  cases parsed : Statement.readIdentification p encoding w with
  | none =>
    have zero : C.scalar (parser 3)=0 := by simpa only [parsed] using spec
    have last := atom_runs hC (.const result 0) True.intro (Nat.zero_le B)
    have hV := (Atom.const result 0 : Atom Reg Arr).apply_bounded hC (Nat.zero_le B)
    refine ⟨t+2,by nlinarith,_,.seq parse' (.branch_zero zero last),hV,?_⟩
    simp [Atom.apply,Statement.identificationLanguage_iff_parsed,parsed]
  | some pair =>
    rcases pair with ⟨T,k⟩
    have data : C.scalar (parser 3)=1 ∧ C.scalar (parser 2)=k ∧ IdentificationParsing.EncodesTensor p C.left T := by
      simpa only [parsed] using spec
    obtain ⟨bits,hk,heq⟩ := (Statement.readIdentification_eq_some_iff p encoding w T k).mp parsed
    have hkpos : k≠0 := by
      cases encoding with
      | binary => exact Nat.ne_of_gt hk.2.2
      | unary => exact Nat.ne_of_gt hk.2
    have dim : T.inputDimension+T.outputDimension≤w.length := by
      have h := Statement.dimensions_le_encoded_length p T bits
      simpa [heq] using h
    have hp : 1≤p := (Fact.out : p.Prime).pos
    have npos : 0<p^(T.inputDimension+T.outputDimension) := pow_pos hp _
    have nbound : p^(T.inputDimension+T.outputDimension)≤p^w.length := pow_le_pow_right' hp dim
    have kb : min k T.wlCap≤w.length+10 := by
      apply (Nat.min_le_right k T.wlCap).trans
      unfold Statement.TensorDescription.wlCap
      omega
    obtain ⟨count,cube,power,fourth,vectors⟩ := WLExponentialBudgets.candidate_room p w.length
      (T.inputDimension+T.outputDimension) (min k T.wlCap) hp dim kb
    obtain ⟨ln,rn,kc,one',matrix,product,target,pair,arity,width,vectorRoom⟩ :=
      WLExponentialBudgets.room p w.length (p^(T.inputDimension+T.outputDimension))
        (p^(T.inputDimension+T.outputDimension)) (min k T.wlCap) nbound nbound kb
    have room4 : ((p^(T.inputDimension+T.outputDimension))*(p^(T.inputDimension+T.outputDimension)))*
        ((p^(T.inputDimension+T.outputDimension))*(p^(T.inputDimension+T.outputDimension)))≤B := by
      simpa [pow_succ,pow_two,Nat.mul_assoc] using fourth
    obtain ⟨u,hu,V,identify,hV,bit,out⟩ := RawIdentificationTables.program_runs p word C B T k hkpos hC data.2.2 data.2.1 field
      (by dsimp [B];omega) room4 power cube count
      ⟨npos,npos,ln,rn,kc,one',by simpa [pow_two] using matrix⟩
      ⟨by simpa [pow_two] using matrix,by simpa using target,by simpa using pair,arity,by simpa using width,one',vectorRoom⟩
    have tableCost := (TensorParsingBudgets.tableCost_le p T.inputDimension T.outputDimension w.length dim).trans
      (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left baseRoom 5))
    have clientCost := IdentificationTableClient.cost_le (p:=p) (D:=T.inputDimension+T.outputDimension) (B:=B)
      (by omega) (dim.trans lengthRoom) (by simpa using width) power count cube
    have basePower : B^5≤(B+1)^8 := (Nat.pow_le_pow_left (by omega : B≤B+1) 5).trans powers58
    refine ⟨t+(u+1),by nlinarith,V,.seq parse' (.branch_nonzero (by change C.scalar (parser 3)≠0;omega) identify),hV,?_⟩
    have nz : V.scalar result≠0 ↔ V.scalar result=1 := by omega
    rw [nz,out,Statement.identificationLanguage_iff_parsed]
    constructor
    · intro h; exact ⟨T,k,parsed,h⟩
    · rintro ⟨T',k',hparse,h⟩
      rw [parsed] at hparse
      cases hparse
      exact h

end GroupWL.MachinePrograms.RawIdentification
