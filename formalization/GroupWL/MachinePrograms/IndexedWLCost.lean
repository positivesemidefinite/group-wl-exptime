import GroupWL.MachinePrograms.IndexedWLSetup

/-! Uniform source-resource estimates for the fully proved indexed client. -/
namespace GroupWL.MachinePrograms.IndexedWL
open NatArrayLanguage GroupWL.IndexedRefinement

theorem decisionCost_le_common_bound {n k b m left right : ℕ} (room : Room n k b m)
    (hl : left≤m) (hr : right≤m) : decisionCost n k b left right≤200*(m+1)^7 := by
  let M := m+1
  have hM : 1≤M := by dsimp [M]; omega
  have hn : n≤M := ((Nat.le_mul_self n).trans room.matrix).trans (by dsimp [M]; omega)
  have hk : k≤M := room.arity.trans (by dsimp [M]; omega)
  have hb : b≤M := room.width.trans (by dsimp [M]; omega)
  have hv : n^k≤M := room.vectors.trans (by dsimp [M]; omega)
  have hl' : left≤M := hl.trans (by dsimp [M]; omega)
  have hr' : right≤M := hr.trans (by dsimp [M]; omega)
  have hcost : decisionCost n k b left right ≤
      4*M+(M*M)*(M*(M*(M*(2*M*(10*M+10)+6*M+24)+10)+6)+4+3)+12+
        M*(7*(M+M)+17)+4 := by
    unfold decisionCost refinementCost roundCost
    gcongr
  have hp (j : ℕ) (hj : j≤7) : M^j≤M^7 := Nat.pow_le_pow_right (by omega) hj
  have h0 := hp 0 (by omega)
  have h1 := hp 1 (by omega)
  have h2 := hp 2 (by omega)
  have h3 := hp 3 (by omega)
  have h4 := hp 4 (by omega)
  have h5 := hp 5 (by omega)
  have h6 := hp 6 (by omega)
  change decisionCost n k b left right≤200*M^7
  nlinarith

theorem storageBound_le_common_bound (m : ℕ) : storageBound Reg Arr m≤100*(m+1)^2 := by
  have hcard : Fintype.card Reg+3*Fintype.card Arr≤100 := by decide
  exact Nat.mul_le_mul_right _ hcard

/-- Source time and space are polynomial in a common magnitude bound that
already includes the finite tuple/vector universes. -/
theorem decide_runs_polynomial {n k b m : ℕ} (D : Data n k b)
    (initialEq : Fin n → Fin n → Bool) (S : Store Reg Arr) (room : Room n k b m)
    (input : Input D (CompressedRefinement.table D.edges initialEq 0) m S)
    (left right : List (Fin n))
    (hleft : S.array .leftSelection=left.map Fin.val)
    (hright : S.array .rightSelection=right.map Fin.val)
    (hlenL : left.length≤m) (hlenR : right.length≤m) :
    ∃t≤200*(m+1)^7,∃T,Runs (100*(m+1)^2) decide S t T ∧ T.Bounded m ∧
      T.scalar .result=boolNat (IndexedRefinement.run D
        (matrixWord (CompressedRefinement.table D.edges initialEq 0))
        (left.map Fin.val) (right.map Fin.val)) := by
  obtain ⟨t,ht,T,run,hT,heq⟩ := decide_runs D initialEq S room input left right hleft hright hlenL hlenR
  exact ⟨t,ht.trans (decisionCost_le_common_bound room hlenL hlenR),T,
    run.mono (storageBound_le_common_bound m),hT,heq⟩

end GroupWL.MachinePrograms.IndexedWL

