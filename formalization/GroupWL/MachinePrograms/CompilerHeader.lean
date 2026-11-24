import GroupWL.MachinePrograms.CompilerOutput
import GroupWL.MachinePrograms.UnaryArithmetic

/-! Executable canonical tableau headers. Every variable numeral is produced
by unary stack operations, including the quadratic schema count. -/
namespace GroupWL.MachinePrograms.Structured

open CircuitDescription Complexity MachineCellular

variable {K : Type*} [DecidableEq K]

theorem fixedScale_writes (S : Store K) (source output temp : K)
    (hso : source ≠ output) (hst : source ≠ temp) (hot : output ≠ temp)
    (n c : ℕ) (hn : S source = unary n) (ht : S temp = []) :
    Writes output (fixedScale source output temp c) S (unary (c*n)) (c*(7*n+2)) := by
  exact ⟨_,le_rfl,by simpa using fixedScale_runs source output temp hso hst hot n c S hn ht⟩

def emitLinearWord (reg : Fin 4 ↪ K) (a b c : ℕ) : Program K :=
  .seq (fixedScale (reg 0) (reg 2) (reg 3) a)
    (.seq (fixedScale (reg 1) (reg 2) (reg 3) b)
      (emitFixed (reg 2) (unary c++[false])))

theorem emitLinearWord_runs (S : Store K) (reg : Fin 4 ↪ K) (a b c m n : ℕ)
    (hm : S (reg 0) = unary m) (hn : S (reg 1) = unary n) (ht : S (reg 3) = []) :
    Writes (reg 2) (emitLinearWord reg a b c) S (natWord (a*m+b*n+c))
      (a*(7*m+2)+(b*(7*n+2)+(c+1))) := by
  have eqreg (i j : Fin 4) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  have first := fixedScale_writes S (reg 0) (reg 2) (reg 3)
    (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
    m a hm ht
  let A := Function.update S (reg 2) ((unary (a*m)).reverse++S (reg 2))
  have second := fixedScale_writes A (reg 1) (reg 2) (reg 3)
    (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
    n b (by simp [A,eqreg,hn]) (by simp [A,eqreg,ht])
  let B := Function.update A (reg 2) ((unary (b*n)).reverse++A (reg 2))
  have third := emitFixed_writes B (reg 2) (unary c++[false])
  have run := first.seq (second.seq third)
  have hw : unary (a*m)++(unary (b*n)++(unary c++[false])) = natWord (a*m+b*n+c) := by
    change unary (a*m)++(unary (b*n)++(unary c++[false])) = unary (a*m+b*n+c)++[false]
    simp only [← List.append_assoc,← unary_add,Nat.add_assoc]
  rw [hw] at run
  simpa only [emitLinearWord,List.length_append,unary_length,List.length_singleton] using run

def emitSquareScale (reg : Fin 5 ↪ K) (c : ℕ) : Program K :=
  .seq (multiply (reg 0) (reg 0) (reg 2) (reg 3) (reg 4))
    (.seq (fixedScale (reg 2) (reg 1) (reg 4) c) (clear (reg 2)))

theorem emitSquareScale_runs (S : Store K) (reg : Fin 5 ↪ K) (n c : ℕ)
    (hn : S (reg 0) = unary n) (hs : S (reg 2) = [])
    (hc : S (reg 3) = []) (ht : S (reg 4) = []) :
    Writes (reg 1) (emitSquareScale reg c) S (unary (c*n^2))
      ((7*n*n+11*n+3)+(c*(7*n^2+2)+(2*n^2+1))) := by
  have eqreg (i j : Fin 5) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let A := Function.update S (reg 2) (unary (n^2))
  have first : Runs (multiply (reg 0) (reg 0) (reg 2) (reg 3) (reg 4)) S (7*n*n+11*n+3) A := by
    simpa [A,hs,pow_two] using multiply_runs S (reg 0) (reg 0) (reg 2) (reg 3) (reg 4)
      (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
      (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
      (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) n n hn hn hc ht
  let B := Function.update A (reg 1) (unary (c*n^2)++A (reg 1))
  have second : Runs (fixedScale (reg 2) (reg 1) (reg 4) c) A (c*(7*n^2+2)) B := by
    exact fixedScale_runs (reg 2) (reg 1) (reg 4)
      (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
      (n^2) c A (by simp [A]) (by simp [A,eqreg,ht])
  have third := clear_runs B (reg 2)
  have hb : B (reg 2) = unary (n^2) := by simp [B,A,eqreg]
  rw [hb,unary_length] at third
  have hfinal : Function.update B (reg 2) [] =
      Function.update S (reg 1) ((unary (c*n^2)).reverse++S (reg 1)) := by
    funext k
    by_cases hk : k = reg 2
    · subst k; simp [eqreg,hs]
    · by_cases hk' : k = reg 1
      · subst k; simp [B,A,eqreg]
      · simp [B,A,Function.update_of_ne hk,Function.update_of_ne hk']
  rw [hfinal] at third
  exact ⟨_,le_rfl,Runs.seq first (Runs.seq second third)⟩

def edgeCoefficient (M : Machine) : ℕ := ((3+M.workSymbols)*(3+M.states))^3

def emitEdgeWord (reg : Fin 5 ↪ K) (M : Machine) : Program K :=
  .seq (emitSquareScale reg (2*edgeCoefficient M))
    (.seq (fixedScale (reg 0) (reg 1) (reg 4) (3*edgeCoefficient M))
      (emitFixed (reg 1) (unary (2*edgeCoefficient M)++[false])))

def edgeSteps (M : Machine) (d : ℕ) : ℕ :=
  (7*d*d+11*d+3)+((2*edgeCoefficient M)*(7*d^2+2)+(2*d^2+1))+
    ((3*edgeCoefficient M)*(7*d+2)+(2*edgeCoefficient M+1))

theorem emitEdgeWord_runs (S : Store K) (reg : Fin 5 ↪ K) (M : Machine) (d : ℕ)
    (hd : S (reg 0) = unary d) (hs : S (reg 2) = [])
    (hc : S (reg 3) = []) (ht : S (reg 4) = []) :
    Writes (reg 1) (emitEdgeWord reg M) S (natWord (edgeCoefficient M*(2*d^2+3*d+2)))
      (edgeSteps M d) := by
  have eqreg (i j : Fin 5) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  have first := emitSquareScale_runs S reg d (2*edgeCoefficient M) hd hs hc ht
  let A := Function.update S (reg 1) ((unary (2*edgeCoefficient M*d^2)).reverse++S (reg 1))
  have second := fixedScale_writes A (reg 0) (reg 1) (reg 4)
    (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
    d (3*edgeCoefficient M) (by simp [A,eqreg,hd]) (by simp [A,eqreg,ht])
  let B := Function.update A (reg 1) ((unary (3*edgeCoefficient M*d)).reverse++A (reg 1))
  have third := emitFixed_writes B (reg 1) (unary (2*edgeCoefficient M)++[false])
  have run := first.seq (second.seq third)
  have hnum : 2*edgeCoefficient M*d^2+(3*edgeCoefficient M*d+2*edgeCoefficient M) =
      edgeCoefficient M*(2*d^2+3*d+2) := by ring
  have hw : unary (2*edgeCoefficient M*d^2)++
      (unary (3*edgeCoefficient M*d)++(unary (2*edgeCoefficient M)++[false])) =
      natWord (edgeCoefficient M*(2*d^2+3*d+2)) := by
    change _ = unary (edgeCoefficient M*(2*d^2+3*d+2))++[false]
    simp only [← List.append_assoc,← unary_add,hnum]
  rw [hw] at run
  simpa only [emitEdgeWord,edgeSteps,List.length_append,unary_length,List.length_singleton] using run

def headerLinearRegisters : Fin 4 ↪ Fin 6 := ⟨![0,1,2,5],by decide⟩
def headerEdgeRegisters : Fin 5 ↪ Fin 6 := ⟨![1,2,3,4,5],by decide⟩

def headerPrefix (M : Machine) : List Bool := natWord (FiniteCode.size (CellularTableau.Gate (Cell M)))

def headerSuffix (M : Machine) : List Bool :=
  natWord (3+M.workSymbols)++kindWord (MachineCircuit.compile M [] 0)

def headerWord (M : Machine) (n d : ℕ) : List Bool :=
  headerPrefix M++natWord (2*d)++natWord (edgeCoefficient M*(2*d^2+3*d+2))++
    natWord (n+d+2)++headerSuffix M

/-- Preserved unary input length, unary address width, output, and three
initially empty scratch registers. -/
def emitHeader (reg : Fin 6 ↪ K) (M : Machine) : Program K :=
  .seq (emitFixed (reg 2) (headerPrefix M))
    (.seq (emitLinearWord (headerLinearRegisters.trans reg) 0 2 0)
      (.seq (emitEdgeWord (headerEdgeRegisters.trans reg) M)
        (.seq (emitLinearWord (headerLinearRegisters.trans reg) 1 1 2)
          (emitFixed (reg 2) (headerSuffix M)))))

def headerSteps (M : Machine) (n d : ℕ) : ℕ :=
  (headerPrefix M).length+((2*(7*d+2)+1)+
    (edgeSteps M d+((7*n+2)+((7*d+2)+3)+(headerSuffix M).length)))

theorem emitHeader_runs (S : Store K) (reg : Fin 6 ↪ K) (M : Machine) (n d : ℕ)
    (hn : S (reg 0) = unary n) (hd : S (reg 1) = unary d)
    (hs : S (reg 3) = []) (hc : S (reg 4) = []) (ht : S (reg 5) = []) :
    Writes (reg 2) (emitHeader reg M) S (headerWord M n d) (headerSteps M n d) := by
  have eqreg (i j : Fin 6) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let A := Function.update S (reg 2) ((headerPrefix M).reverse++S (reg 2))
  have first := emitFixed_writes S (reg 2) (headerPrefix M)
  have second : Writes (reg 2) (emitLinearWord (headerLinearRegisters.trans reg) 0 2 0) A
      (natWord (2*d)) (2*(7*d+2)+1) := by
    simpa [headerLinearRegisters] using emitLinearWord_runs A (headerLinearRegisters.trans reg) 0 2 0 n d
      (by simp [headerLinearRegisters,A,eqreg,hn]) (by simp [headerLinearRegisters,A,eqreg,hd])
      (by simp [headerLinearRegisters,A,eqreg,ht])
  let B := Function.update A (reg 2) ((natWord (2*d)).reverse++A (reg 2))
  have third : Writes (reg 2) (emitEdgeWord (headerEdgeRegisters.trans reg) M) B
      (natWord (edgeCoefficient M*(2*d^2+3*d+2))) (edgeSteps M d) := by
    exact emitEdgeWord_runs B (headerEdgeRegisters.trans reg) M d
      (by simp [headerEdgeRegisters,B,A,eqreg,hd]) (by simp [headerEdgeRegisters,B,A,eqreg,hs])
      (by simp [headerEdgeRegisters,B,A,eqreg,hc]) (by simp [headerEdgeRegisters,B,A,eqreg,ht])
  let C := Function.update B (reg 2)
    ((natWord (edgeCoefficient M*(2*d^2+3*d+2))).reverse++B (reg 2))
  have fourth : Writes (reg 2) (emitLinearWord (headerLinearRegisters.trans reg) 1 1 2) C
      (natWord (n+d+2)) ((7*n+2)+((7*d+2)+3)) := by
    simpa [headerLinearRegisters] using emitLinearWord_runs C (headerLinearRegisters.trans reg) 1 1 2 n d
      (by simp [headerLinearRegisters,C,B,A,eqreg,hn]) (by simp [headerLinearRegisters,C,B,A,eqreg,hd])
      (by simp [headerLinearRegisters,C,B,A,eqreg,ht])
  let D := Function.update C (reg 2) ((natWord (n+d+2)).reverse++C (reg 2))
  have fifth := emitFixed_writes D (reg 2) (headerSuffix M)
  have run := first.seq (second.seq (third.seq (fourth.seq fifth)))
  simpa [emitHeader,headerWord,headerSteps,List.append_assoc,Nat.add_assoc] using run

def headerConstant (M : Machine) : ℕ :=
  (headerPrefix M).length+(headerSuffix M).length+100*edgeCoefficient M+100

theorem headerSteps_le (M : Machine) (n d : ℕ) :
    headerSteps M n d ≤ headerConstant M*(n+d+1)^2 := by
  let x := n+d+1
  have hx : 1 ≤ x^2 := by
    have hx0 : 1 ≤ x := by dsimp [x]; omega
    exact hx0.trans (Nat.le_self_pow (by decide : 2 ≠ 0) _)
  have hn : n ≤ x^2 := (by dsimp [x]; omega : n ≤ x).trans (Nat.le_self_pow (by decide : 2 ≠ 0) _)
  have hd : d ≤ x^2 := (by dsimp [x]; omega : d ≤ x).trans (Nat.le_self_pow (by decide : 2 ≠ 0) _)
  have hd2 : d^2 ≤ x^2 := Nat.pow_le_pow_left (by dsimp [x]; omega) 2
  have hconst := Nat.mul_le_mul_left ((headerPrefix M).length+(headerSuffix M).length) hx
  have hc := Nat.mul_le_mul_left (edgeCoefficient M) hx
  have hcd := Nat.mul_le_mul_left (edgeCoefficient M) hd
  have hcd2 := Nat.mul_le_mul_left (edgeCoefficient M) hd2
  change headerSteps M n d ≤ headerConstant M*x^2
  unfold headerSteps edgeSteps headerConstant
  nlinarith

theorem headerWord_canonical (M : Machine) (w : List Bool) (d : ℕ) :
    headerWord M w.length d =
      natWord (FiniteCode.size (CellularTableau.Gate (Cell M)))++natWord (d+d)++
        natWord (MachineCircuit.compile M w d).edges++natWord (MachineCircuit.compile M w d).seedCount++
        natWord (MachineCircuit.compile M w d).testCount++kindWord (MachineCircuit.compile M w d) := by
  simp only [headerWord,headerPrefix,headerSuffix,MachineCircuit.edge_count,
    MachineCircuit.seed_count,MachineCircuit.test_count,edgeCoefficient]
  have hk : kindWord (MachineCircuit.compile M [] 0) = kindWord (MachineCircuit.compile M w d) := rfl
  rw [hk]
  simp [two_mul,List.append_assoc]

end GroupWL.MachinePrograms.Structured
