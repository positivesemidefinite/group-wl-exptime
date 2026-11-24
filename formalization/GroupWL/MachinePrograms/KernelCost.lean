import GroupWL.MachinePrograms.KernelComplete

/-! Polynomial bounds for the complete concrete Gaussian kernel algorithm. -/
namespace GroupWL.MachinePrograms.KernelProgram
open NatArrayLanguage

theorem stepCost_le (n p q : ℕ) (hn : n≤q) (hp : p≤q) (hq : 1≤q) :
    stepCost n p+1≤200*q^3 := by
  have hn3 := Nat.pow_le_pow_left hn 3
  have hn2 := Nat.pow_le_pow_left hn 2
  have hq23 : q^2≤q^3 := by
    have := Nat.mul_le_mul_left (q*q) hq
    nlinarith
  have hq3 := Nat.le_self_pow (by decide : 3≠0) q
  unfold stepCost updateCost
  nlinarith

theorem programCost_le (m n p : ℕ) : programCost m n p≤220*(m+n+p+1)^4 := by
  let q := m+n+p+1
  have hq : 1≤q := by dsimp [q]; omega
  have hm : m≤q := by dsimp [q]; omega
  have hn : n≤q := by dsimp [q]; omega
  have hp : p≤q := by dsimp [q]; omega
  have hs := stepCost_le n p q hn hp hq
  have hms := Nat.mul_le_mul hm hs
  have hq4 := Nat.le_self_pow (by decide : 4≠0) q
  change programCost m n p≤220*q^4
  unfold programCost
  nlinarith

theorem storageBound_le (M : ℕ) : storageBound Reg Arr M≤150*(M+1)^2 := by
  have hcard : Fintype.card Reg+3*Fintype.card Arr≤150 := by decide
  exact Nat.mul_le_mul_right _ hcard

theorem program_runs_polynomial (p : ℕ) [NeZero p] (n m M : ℕ) (A : List ℕ) (S : State)
    (bounded : S.Bounded M) (ambient : S.scalar (wr .ambient)=n)
    (rows : S.scalar (wr .rows)=m) (modulus : S.scalar (wr .modulus)=p)
    (input : S.array (wa .input)=A) (positive : 1<p) (small : p*p+p≤M) (square : n*n≤M)
    (inputLength : A.length=m*n) (inputValues : ∀x∈A,x<p) :
    ∃ t≤220*(m+n+p+1)^4,∃ T,Runs (150*(M+1)^2) (program p) S t T ∧
      T.Bounded M ∧ Represents p n 0 A (executeRows A p n m (initial n)) T := by
  obtain ⟨t,ht,T,run,hT,hrep⟩ := program_runs p n m M A S bounded ambient rows modulus input
    positive small square inputLength inputValues
  exact ⟨t,ht.trans (programCost_le m n p),T,run.mono (storageBound_le M),hT,hrep⟩

end GroupWL.MachinePrograms.KernelProgram
