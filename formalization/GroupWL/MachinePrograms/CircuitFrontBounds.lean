import GroupWL.ReductionResourceBounds
import GroupWL.MachinePrograms.CircuitRecordPipeline
import GroupWL.MachinePrograms.PolynomialBudget

namespace GroupWL.MachinePrograms.CircuitRecordPipeline.Frontend
open AddressedCircuit CircuitDescription NatArrayLanguage CircuitMetadataValues
open CircuitMetadataExpressions (Field)
open ReductionResourceBounds

noncomputable def expressionDegree : ℕ :=
  Finset.univ.sup (fun f : Field => 2*((CircuitMetadataExpressions.entry f).expression
    CircuitMetadataExpressions.sizeRegister).cost)
noncomputable def frontExponent := 20+5*expressionDegree

private theorem numerical {x r N a b L : ℕ} (hx : 1024≤x) (hn : N≤x) (hr : r≤x)
    (ha : a≤x) (hb : b≤x) (hl : L≤x) :
    6≤x^4 ∧ 3*N+5≤x^4 ∧ a≤x^4 ∧ b≤x^4 ∧ b*2≤x^4 ∧ b*r*2≤x^4 ∧
    b*r≤x^4 ∧ 146*(r+1)^2≤x^20 ∧ 40*(a+b+L+r+1)^3≤x^20 ∧ x^4+2≤x^5 := by
  have root : 1≤x := by omega
  have sq : x*x=x^2 := by ring
  have hx2 := Nat.le_self_pow (n:=2) (by decide) x
  have grow (i j : ℕ) (hij : i≤j) := Nat.pow_le_pow_right root hij
  have hbr := Nat.mul_le_mul hb hr
  have hsum : a+b+L+r+1 ≤ x^2 := by nlinarith [Nat.mul_le_mul_right x (show 5≤x by omega)]
  have hsucc : r+1≤x^2 := by omega
  have par := mulPow (constPow (show 146≤x by omega)) (natPower 2 hsucc)
  have cap := mulPow (constPow (show 40≤x by omega)) (natPower 3 hsum)
  have dbl := mulPow (hbr.trans_eq sq) (constPow (show 2≤x by omega))
  have h4 : 3*N+5≤x^2 := by nlinarith [Nat.mul_le_mul_right x (show 8≤x by omega)]
  have five : x^4+2≤x^5 := by
    have two : 2≤x^4 := (show 2≤x by omega).trans (Nat.le_self_pow (by decide) x)
    have prod := Nat.mul_le_mul_left (x^4) (show 2≤x by omega)
    change x^4+2≤x^4*x
    omega
  exact ⟨(show 6≤x by omega).trans (Nat.le_self_pow (by decide) x),h4.trans (grow 2 4 (by decide)),
    ha.trans (Nat.le_self_pow (by decide) x), hb.trans (Nat.le_self_pow (by decide) x),
    (mulPow (constPow hb) (constPow (show 2≤x by omega))).trans (grow _ 4 (by decide)),
    dbl.trans (grow _ 4 (by decide)), hbr.trans (sq.le.trans (grow 2 4 (by decide))),
    par.trans (grow _ 20 (by decide)), cap.trans (grow _ 20 (by decide)),five⟩

variable {T : Type} [FiniteCode T] {n : ℕ} (C : Circuit T (n+3))
theorem front_room (p d : ℕ) (hd : frontExponent≤d) :
    let X := scale C p
    let B := X^4
    let M := X^d
    B ≤ M ∧ 6≤B ∧ 3*(circuitWord C).length+5≤B ∧ (∀f,fieldSize (ofCircuit C) f≤B) ∧
      (∀ f,(B+2)^(2*((CircuitMetadataExpressions.entry f).expression CircuitMetadataExpressions.sizeRegister).cost)≤M) ∧
      146*(n+3+1)^2≤M ∧ LayoutRecordPrograms.budget (ofCircuit C).table (CircuitGroupReduction.wireLength n)≤M := by
  let x := scale C p
  have scale := (scale_lower C p).1
  have header := ReductionResourceBounds.header C
  obtain ⟨_,real,comp,_,wire,_⟩ := schema C p
  letI : Fintype T := FiniteCode.fintype T
  have a : (ofCircuit C).realTypes≤x := by
    have h := (CircuitOutputSize.real_card_le C).trans real
    rwa [FiniteCode.card_eq_size, CircuitComparisonCodes.size_realType] at h
  have b : (ofCircuit C).comparisons≤x := by
    have h := (CircuitOutputSize.comparison_card_le C).trans comp
    rwa [FiniteCode.card_eq_size, CircuitComparisonCodes.size_comparison] at h
  have hx : 1024≤x := by dsimp [x]; omega
  have hr : n+3≤x := by dsimp [x]; omega
  have hn : (circuitWord C).length≤x := by dsimp [x]; omega
  have hl : CircuitGroupReduction.wireLength n≤x := by dsimp [x]; omega
  obtain ⟨six,parse,types,comparisons,forms,domain,perm,param,capacity,plus⟩ :=
    numerical hx hn hr a b hl
  have d20 : 20≤d := by unfold frontExponent at hd; omega
  have toM := Nat.pow_le_pow_right (show 1≤x by omega) d20
  refine ⟨Nat.pow_le_pow_right (by omega) (by omega),six,parse,?_,?_,param.trans toM,capacity.trans toM⟩
  · intro f
    cases f <;> first | exact types | exact comparisons | exact forms | exact domain | exact perm
  · intro f
    let e := 2*((CircuitMetadataExpressions.entry f).expression CircuitMetadataExpressions.sizeRegister).cost
    have he : e≤expressionDegree := Finset.le_sup (f:=(fun f : Field =>
       2*((CircuitMetadataExpressions.entry f).expression CircuitMetadataExpressions.sizeRegister).cost)) (Finset.mem_univ f)
    have lift := Nat.pow_le_pow_left plus e
    rw [← pow_mul] at lift
    exact lift.trans (Nat.pow_le_pow_right (by omega) (by unfold frontExponent at hd; omega))

private theorem linAdd {a b x y m : ℕ} (hx : a≤x*m) (hy : b≤y*m) : a+b≤(x+y)*m := by
  rw [Nat.add_mul]; exact Nat.add_le_add hx hy
private theorem linCoeff (k : ℕ) {a b m : ℕ} (h : a≤b*m) : k*a≤(k*b)*m := by
  rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h
private theorem linRight (k : ℕ) {a b m : ℕ} (h : a≤b*m) : a*k≤(b*k)*m := by
  calc
    _ ≤ (b*m)*k := Nat.mul_le_mul_right _ h
    _ = _ := by ring
private theorem linConst (a M : ℕ) : a ≤ a*(M+1) := Nat.le_mul_of_pos_right _ (by omega)

private theorem table_scale (B M : ℕ) (hB : B≤M) (fs : List Field) :
    tableTime B fs ≤ tableTime 1 fs*(M+1) := by
  induction fs with
  | nil => simp [tableTime]
  | cons f fs ih =>
    simp only [tableTime]
    exact linAdd ih (linAdd (linConst _ M) (linAdd (linRight _ (by simpa using hB.trans (Nat.le_succ M))) (linConst _ M)))

theorem time_scale (N size B M : ℕ) (input : (N+1)^2≤M) (types : size≤M) (cells : B≤M) :
    time N size B M ≤ time 0 1 1 1*(M+1) := by
  have hN : (N+1)^2≤(0+1)^2*(M+1) := by simpa using input.trans (Nat.le_succ M)
  have hT : size≤1*(M+1) := by omega
  have hM : M≤1*(M+1) := by omega
  have tab := table_scale B M cells Metadata.fields
  have loop : 20*size+9 ≤ (20*1+9)*(M+1) := linAdd (linCoeff 20 hT) (linConst _ M)
  have pair : Packed.pairTime size ≤ Packed.pairTime 1*(M+1) :=
    linAdd loop (linAdd (linConst _ M) loop)
  have count : Packed.countTime size ≤ Packed.countTime 1*(M+1) :=
    linAdd pair (linAdd (linConst _ M) (linAdd (linCoeff 6 (linCoeff 2 hT)) (linConst _ M)))
  have pack : Packed.time size ≤ Packed.time 1*(M+1) :=
    linAdd count (linAdd (linConst _ M) (linAdd (linCoeff 8 (linCoeff 2 hT)) (linConst _ M)))
  have stage : Decode.stageTime size ≤ Decode.stageTime 1*(M+1) := linAdd (linConst _ M) pack
  have decode : Decode.time N size ≤ Decode.time 0 1*(M+1) :=
    linAdd (linAdd (linCoeff 110 hN) stage) stage
  have counts : Metadata.countsTime N size ≤ Metadata.countsTime 0 1*(M+1) :=
    linAdd decode (linConst _ M)
  have metadataTime : Metadata.time N size B ≤ Metadata.time 0 1 1*(M+1) :=
    linAdd counts (linAdd (linConst _ M) tab)
  exact linAdd (linAdd metadataTime (linConst _ M)) (linAdd (linConst _ M)
    (linAdd (linConst 2 M) (linAdd (linCoeff 2000 hM) (linConst _ M))))

theorem time_bounded (p d : ℕ) (hd : frontExponent≤d) :
    time (circuitWord C).length (FiniteCode.size T) ((scale C p)^4) ((scale C p)^d) ≤
      time 0 1 1 1*((scale C p)^d+1) := by
  have low := (scale_lower C p).1
  have header := ReductionResourceBounds.header C
  let X := scale C p
  have x1 : 1≤X := by dsimp [X]; omega
  have hn : (circuitWord C).length+1≤X := by dsimp [X]; omega
  have de : 4≤d := by unfold frontExponent at hd; omega
  exact time_scale _ _ _ _ ((Nat.pow_le_pow_left hn 2).trans (Nat.pow_le_pow_right x1 (by omega)))
    ((show FiniteCode.size T ≤ X by dsimp [X]; omega).trans (Nat.le_self_pow (by omega) X))
    (Nat.pow_le_pow_right x1 de)

end GroupWL.MachinePrograms.CircuitRecordPipeline.Frontend
