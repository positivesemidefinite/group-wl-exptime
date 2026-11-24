import GroupWL.MachinePrograms.IdentificationThreeClient
import GroupWL.MachinePrograms.IdentificationMembership

/-! Identification in Version III using the dense-tensor parser, the compact
p-group candidate search and full multiplication-gadget refinement. -/
namespace GroupWL.MachinePrograms.IdentificationThree
open NatArrayLanguage
open NatArrayLowering (bitNat)
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev Reg := RawIdentificationTables.Reg ⊕ IdentificationThreeClient.Reg
abbrev Arr := RawIdentificationTables.Arr ⊕ IdentificationThreeClient.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
def input : Arr := .inl RawIdentification.input
def result : Reg := .inr IdentificationThreeClient.result
def transfer : List (Atom Reg Arr) := [
  .copy (.inr (IdentificationThreeClient.source .dimension)) (.inl (RawIdentificationTables.source .dimension)),
  .copy (.inr (IdentificationThreeClient.source .order)) (.inl (RawIdentificationTables.source .order)),
  .copy (.inr (IdentificationThreeClient.source .arity)) (.inl (RawIdentificationTables.source .arity)),
  .copyArray (.inr (IdentificationThreeClient.sourceArray .table)) (.inl (RawIdentificationTables.sourceArray .table))]
def identify (p : ℕ) [Fact p.Prime] : Code := .seq ((RawIdentificationTables.tables p).map Sum.inl Sum.inl)
  (.seq (atoms transfer) ((IdentificationThreeClient.identify p).map Sum.inr Sum.inr))
def program (p : ℕ) [Fact p.Prime] (enc : Statement.DimensionEncoding) : Code :=
  .seq (((IdentificationParsing.program p enc).map Sum.inl Sum.inl |>.map Sum.inl Sum.inl))
    (.branch (.inl (RawIdentificationTables.parser 3)) (identify p) (.atom (.const result 0)))
private def budget (p N : ℕ) := WLExponentialBudgets.budget p (2*N+3)
private theorem budget_le (p N : ℕ) : WLExponentialBudgets.budget p N≤budget p N := by
  unfold budget WLExponentialBudgets.budget WLExponentialBudgets.exponent
  exact pow_le_pow_right' (by decide) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4))

theorem identify_runs (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)] (N : ℕ)
    (S : State) (T : Statement.TensorDescription p) (k : ℕ) (hkpos : k≠0)
    (dim : T.inputDimension+T.outputDimension≤N) (hb : S.Bounded (budget p N))
    (enc : IdentificationParsing.EncodesTensor p S.left.left T)
    (hk : S.left.scalar (RawIdentificationTables.parser 2)=k) :
    ∃t≤6000*(budget p N+1)^8,∃U,Runs (storageBound Reg Arr (budget p N)) (identify p) S t U ∧
      U.Bounded (budget p N) ∧ U.scalar result≤1 ∧
      (U.scalar result=1 ↔ Refinement.Identifies .three k T.Carrier) := by
  let B := budget p N
  let D := T.inputDimension+T.outputDimension
  have hp : 2≤p := (Fact.out : p.Prime).two_le
  have hp1 : 1≤p := by omega
  have hD : D≤N := dim
  have positive : min k T.wlCap≠0 := by unfold Statement.TensorDescription.wlCap;omega
  have kb : min k T.wlCap≤N+10 := (Nat.min_le_right k T.wlCap).trans (by unfold Statement.TensorDescription.wlCap;omega)
  have npos : 0<p^D := pow_pos hp1 _
  have nbound : p^D≤p^N := pow_le_pow_right' hp1 hD
  have alloc := budget_le p N
  have parseRoom := (WLExponentialBudgets.parser_room p N).1.trans alloc
  have capRoom := (WLExponentialBudgets.parser_room p N).2.trans alloc
  have field := (TensorParsingBudgets.field_room p N).trans parseRoom
  have baseRoom : TensorParsingBudgets.base p N≤B :=
    (show TensorParsingBudgets.base p N≤TensorParsingBudgets.magnitude p N from by
      simpa only [TensorParsingBudgets.magnitude,pow_one] using
        pow_le_pow_right' (TensorParsingBudgets.base_positive p N) (by decide : 1≤4)).trans parseRoom
  obtain ⟨count,cube,power,fourth,_⟩ := WLExponentialBudgets.candidate_room p (2*N+3) D (min k T.wlCap)
    hp1 (by omega) (by omega)
  change (p^D)^4≤B at fourth
  have room4 : ((p^D)*(p^D))*((p^D)*(p^D))≤B := by simpa [pow_succ,pow_two,Nat.mul_assoc] using fourth
  have power2 : (p^D)^2≤B := by simpa only [pow_two] using (Nat.le_mul_self _).trans room4
  obtain ⟨t,ht,U,tables,hU,dimension,order,arity,table⟩ := RawIdentificationTables.tables_runs p S.left B T k hb.left enc hk field
    (by dsimp only [B]; omega) power2
  let C := U.join S.right
  have hC : C.Bounded B := hU.join hb.right
  obtain ⟨move,hW⟩ := atoms_runs hC transfer (by simp [transfer,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let W := applyAtoms transfer C
  have data : W.right.scalar (IdentificationThreeClient.source .dimension)=D ∧
      W.right.scalar (IdentificationThreeClient.source .order)=p^D ∧
      W.right.scalar (IdentificationThreeClient.source .arity)=min k T.wlCap ∧
      W.right.array (IdentificationThreeClient.sourceArray .table)=GroupInitial.tableWord (TensorGroupProgram.codedMul p T) := by
    simp [W,C,transfer,applyAtoms,Atom.apply,Store.right,Store.setScalar,Store.setArray,
      IdentificationThreeClient.source,IdentificationThreeClient.sourceArray]
    exact ⟨dimension,order,arity,table⟩
  obtain ⟨ls,_,graphMatrix,graphRoom⟩ := SimpleGadget.exponentialRoom hp npos npos nbound nbound kb
  obtain ⟨u,hu,Y,check,hY,bit,out⟩ := IdentificationThreeClient.identify_runs
    (TensorGroupCode.groupEquiv p T) (TensorGroupProgram.codedEquiv_one_val p T) positive W.right hW.right
    data.1 data.2.1 data.2.2.1 data.2.2.2 room4 power (by omega) cube count ls graphMatrix (by simpa using graphRoom)
  have nB : p^D≤B := (Nat.le_mul_self _).trans (by simpa only [pow_two] using power2)
  have clientCost := IdentificationThreeClient.cost_le (p:=p) (D:=D) (B:=B)
    (by omega) (by dsimp only [B];omega) nB power count cube
  have tabCost := (TensorParsingBudgets.tableCost_le p T.inputDimension T.outputDimension N dim).trans
    (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left baseRoom 5))
  have pow58 : B^5≤(B+1)^8 := (Nat.pow_le_pow_left (by omega : B≤B+1) 5).trans
    (pow_le_pow_right' (by omega) (by decide))
  have one : 1≤(B+1)^8 := one_le_pow₀ (by omega)
  refine ⟨t+(4+u),?_,W.left.join Y,.seq (tables.left_bounded hb) (.seq move (check.right_bounded hW)),
    hW.left.join hY,bit,out.trans (Statement.identification_clamp T .three k).symm⟩
  change t+(4+u)≤6000*(B+1)^8
  change u≤IdentificationThreeClient.cost p D B at hu
  nlinarith

theorem program_runs (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)]
    (encoding : Statement.DimensionEncoding) (w : List Bool) (S : State)
    (hb : S.Bounded (budget p w.length)) (inputEq : S.array input=w.map bitNat) :
    ∃t≤20000*(budget p w.length+1)^8,∃V,
      Runs (storageBound Reg Arr (budget p w.length)) (program p encoding) S t V ∧
      V.Bounded (budget p w.length) ∧
      (V.scalar result≠0 ↔ w∈Statement.identificationLanguage p .three encoding) := by
  let B := budget p w.length
  have alloc := budget_le p w.length
  have parserRoom := (WLExponentialBudgets.parser_room p w.length).1.trans alloc
  have capRoom := (WLExponentialBudgets.parser_room p w.length).2.trans alloc
  have field := (TensorParsingBudgets.field_room p w.length).trans parserRoom
  have lengthRoom : w.length≤B := by dsimp only [B]; omega
  have one : 1≤B := by dsimp only [B]; omega
  have baseRoom : TensorParsingBudgets.base p w.length≤B :=
    (show TensorParsingBudgets.base p w.length≤TensorParsingBudgets.magnitude p w.length from by
      simpa only [TensorParsingBudgets.magnitude,pow_one] using
        pow_le_pow_right' (TensorParsingBudgets.base_positive p w.length) (by decide : 1≤4)).trans parserRoom
  obtain ⟨A,t,ht,parse,hA,_,_,spec⟩ := IdentificationParsing.program_runs p encoding S.left.left w B hb.left.left
    ((TensorParsingBudgets.length_cube_le_magnitude p w.length).trans parserRoom) (by omega)
    ((TensorParsingBudgets.field_power_room p w.length).trans parserRoom)
    ((TensorParsingBudgets.binary_room p w.length).trans parserRoom) inputEq
  let C := (A.join S.left.right).join S.right
  have hC : C.Bounded B := (hA.join hb.left.right).join hb.right
  have parse' := (parse.left_bounded hb.left).left_bounded hb
  have parseCost : t≤1000*(B+1)^5 := by
    have scan := (TensorParsingBudgets.scanCost_le p w.length).trans
      (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left baseRoom 4))
    have powers : B^4≤(B+1)^5 := (Nat.pow_le_pow_left (by omega : B≤B+1) 4).trans (pow_le_pow_right' (by omega) (by omega))
    have linear : B+1≤(B+1)^5 := by simpa only [pow_one] using pow_le_pow_right' (by omega : 1≤B+1) (by decide : 1≤5)
    unfold IdentificationParsing.parseCost at ht
    nlinarith
  have power58 : (B+1)^5≤(B+1)^8 := pow_le_pow_right' (by omega) (by decide)
  have positive : 1≤(B+1)^8 := one_le_pow₀ (by omega)
  cases parsed : Statement.readIdentification p encoding w with
  | none =>
    have zero : C.left.scalar (RawIdentificationTables.parser 3)=0 := by simpa only [parsed] using spec
    have last := atom_runs hC (.const result 0) True.intro (Nat.zero_le B)
    have hV := (Atom.const result 0 : Atom Reg Arr).apply_bounded hC (Nat.zero_le B)
    refine ⟨t+2,by change t+2≤20000*(B+1)^8; nlinarith,_,.seq parse' (.branch_zero zero last),hV,?_⟩
    simp [Atom.apply,Statement.identificationLanguage_iff_parsed,parsed]
  | some pair =>
    rcases pair with ⟨T,k⟩
    have data : C.left.scalar (RawIdentificationTables.parser 3)=1 ∧ C.left.scalar (RawIdentificationTables.parser 2)=k ∧
        IdentificationParsing.EncodesTensor p C.left.left T := by simpa only [parsed] using spec
    obtain ⟨bits,hk,heq⟩ := (Statement.readIdentification_eq_some_iff p encoding w T k).mp parsed
    have hkpos : k≠0 := by
      cases encoding with
      | binary => exact Nat.ne_of_gt hk.2.2
      | unary => exact Nat.ne_of_gt hk.2
    have dim : T.inputDimension+T.outputDimension≤w.length := by
      simpa [heq] using Statement.dimensions_le_encoded_length p T bits
    obtain ⟨u,hu,V,run,hV,bit,out⟩ := identify_runs p w.length C T k hkpos dim hC data.2.2 data.2.1
    change u≤6000*(B+1)^8 at hu
    refine ⟨t+(u+1),by change t+(u+1)≤20000*(B+1)^8; nlinarith,V,.seq parse' (.branch_nonzero
      (by change C.left.scalar (RawIdentificationTables.parser 3)≠0; omega) run),hV,?_⟩
    have nz : V.scalar result≠0 ↔ V.scalar result=1 := by omega
    rw [nz,out,Statement.identificationLanguage_iff_parsed]
    constructor
    · intro h; exact ⟨T,k,parsed,h⟩
    · rintro ⟨T',k',hparse,h⟩
      rw [parsed] at hparse
      cases hparse
      exact h

theorem inEXPTIME (p : ℕ) [Fact p.Prime] [NeZero (2:ZMod p)]
    (encoding : Statement.DimensionEncoding) :
    Complexity.InEXPTIME (Statement.identificationLanguage p .three encoding) := by
  let K := max 20000 (Fintype.card Reg+3*Fintype.card Arr)
  let c := (K+8*(WLExponentialBudgets.coefficient p+1))*256
  apply NatArrayLowering.inEXPTIME (program p encoding) input result _ c 4
  intro w
  let B := budget p w.length
  have cap := (WLExponentialBudgets.parser_room p w.length).2.trans (budget_le p w.length)
  have hlen : w.length≤B := by dsimp [B];omega
  have one : 1≤B := by dsimp [B];omega
  let S : State := NatArrayLowering.inputStore input w
  have hS : S.Bounded B := by
    refine ⟨fun _=>Nat.zero_le _,?_,?_⟩
    · intro a
      by_cases h : a=input
      · subst a; simpa [S,NatArrayLowering.inputStore] using hlen
      · simp [S,NatArrayLowering.inputStore,h]
    · intro a x hx
      by_cases h : a=input
      · subst a; simp only [S,NatArrayLowering.inputStore,Function.update_self] at hx
        obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
        cases b <;> simp [NatArrayLowering.bitNat,one]
      · simp [S,NatArrayLowering.inputStore,h] at hx
  obtain ⟨t,ht,T,run,hT,correct⟩ := program_runs p encoding w S hS (by simp [S,NatArrayLowering.inputStore])
  have poly := SimpleGadget.exponentialCost w.length p K 8
  have time : t≤2^(c*(w.length+1)^4) :=
    ht.trans ((Nat.mul_le_mul_right _ (show 20000≤K from Nat.le_max_left _ _)).trans poly)
  have space : storageBound Reg Arr B≤2^(c*(w.length+1)^4) := by
    have power : (B+1)^2≤(B+1)^8 := pow_le_pow_right' (by omega) (by decide)
    exact (Nat.mul_le_mul (show Fintype.card Reg+3*Fintype.card Arr≤K from Nat.le_max_right _ _) power).trans poly
  exact ⟨storageBound Reg Arr B,t,T,space,time,run,correct⟩
end GroupWL.MachinePrograms.IdentificationThree

