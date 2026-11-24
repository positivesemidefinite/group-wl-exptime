import GroupWL.LayoutMetadataCharge
import GroupWL.FiniteCodeCompaction

/-! Stable filtering of numeric candidates gives the canonical typed source records. -/
namespace GroupWL.LayoutMetadata
open SourceLayout MachinePrograms
variable {T E : Type} [FiniteCode T] [FiniteCode E] {r : ℕ}
  (p : ℕ) [Fact p.Prime] (C : ComparisonData (ZMod p) T E r) (L : ℕ)

theorem domain_binary : ∀x∈(ComparisonMetadata.ofComparison p C).domain,x≤1 := by
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨i,rfl⟩
  change (if _ then 1 else 0)≤1
  split_ifs <;> omega

theorem nodeLabels_binary : ∀x∈nodeLabels (ComparisonMetadata.ofComparison p C) L,x≤1 := by
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨i,rfl⟩
  dsimp only [nodeLabel]
  split_ifs
  · omega
  · exact RectangleFlags.read_small (domain_binary p C) _

theorem linkLabels_binary : ∀x∈linkLabels (ComparisonMetadata.ofComparison p C) L,x≤1 := by
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨i,rfl⟩
  exact RectangleFlags.read_small (domain_binary p C) _

theorem horizontalFlags_binary : ∀x∈horizontalFlags (ComparisonMetadata.ofComparison p C) L,x≤1 := by
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨i,rfl⟩
  exact RectangleFlags.entry_small (nodeLabels_binary p C L) _ _

theorem squareFlags_binary : ∀x∈squareFlags (ComparisonMetadata.ofComparison p C) L,x≤1 := by
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨i,rfl⟩
  exact RectangleFlags.entry_small (linkLabels_binary p C L) _ _

def horizontalTypedKey (h : C.Horizontal L) : ℕ :=
  horizontalKey (ComparisonMetadata.ofComparison p C) (FiniteCode.equiv h.1).val h.2.1.val
    (FiniteCode.equiv h.2.2.1.val).val (FiniteCode.equiv h.2.2.2.val).val

theorem squareKey_lt (s : C.Square L) :
    squareKey p C L s<(squareFlags (ComparisonMetadata.ofComparison p C) L).length := by
  simp only [squareFlags,List.length_ofFn,ComparisonMetadata.ofComparison,linkCount_eq]
  have ha : (FiniteCode.equiv s.2.2.1.val).val<2 := (FiniteCode.equiv s.2.2.1.val).isLt
  have hb : (FiniteCode.equiv s.2.2.2.val).val<2 := (FiniteCode.equiv s.2.2.2.val).isLt
  simpa [squareKey,horizontalKey,Nat.add_assoc] using
    key_lt (FiniteCode.equiv s.1).isLt s.2.1.isLt (show 2*(FiniteCode.equiv s.2.2.1.val).val+(FiniteCode.equiv s.2.2.2.val).val<4 by omega)

theorem horizontalTypedKey_lt (h : C.Horizontal L) :
    horizontalTypedKey p C L h<(horizontalFlags (ComparisonMetadata.ofComparison p C) L).length := by
  simp only [horizontalFlags,List.length_ofFn,ComparisonMetadata.ofComparison,nodeCount_eq]
  have ha : (FiniteCode.equiv h.2.2.1.val).val<2 := (FiniteCode.equiv h.2.2.1.val).isLt
  have hb : (FiniteCode.equiv h.2.2.2.val).val<2 := (FiniteCode.equiv h.2.2.2.val).isLt
  simpa [horizontalTypedKey,horizontalKey,Nat.add_assoc] using
    key_lt (FiniteCode.equiv h.1).isLt h.2.1.isLt (show 2*(FiniteCode.equiv h.2.2.1.val).val+(FiniteCode.equiv h.2.2.2.val).val<4 by omega)

theorem squareKey_chosen (s : C.Square L) :
    (squareFlags (ComparisonMetadata.ofComparison p C) L)[squareKey p C L s]?.getD 0=1 := by
  change (squareFlags _ _)[4*((FiniteCode.equiv s.1).val*r+s.2.1.val)+2*(FiniteCode.equiv s.2.2.1.val).val+(FiniteCode.equiv s.2.2.2.val).val]?.getD 0=1
  rw [squareFlags_read]
  simp only [FiniteCode.boolFlag,if_pos s.2.2.1.property,if_pos s.2.2.2.property,Nat.one_mul]

theorem horizontalTypedKey_chosen (h : C.Horizontal L) :
    (horizontalFlags (ComparisonMetadata.ofComparison p C) L)[horizontalTypedKey p C L h]?.getD 0=1 := by
  change (horizontalFlags _ _)[4*((FiniteCode.equiv h.1).val*r+h.2.1.val)+2*(FiniteCode.equiv h.2.2.1.val).val+(FiniteCode.equiv h.2.2.2.val).val]?.getD 0=1
  rw [horizontalFlags_read]
  simp only [FiniteCode.boolFlag,if_pos h.2.2.1.property,if_pos h.2.2.2.property,Nat.one_mul]

theorem square_compaction (values : List ℕ) (f : C.Square L → ℕ)
    (read : ∀s,values[squareKey p C L s]?.getD 0=f s) :
    SelectArray.selectedPrefix (squareFlags (ComparisonMetadata.ofComparison p C) L) values
      (squareFlags (ComparisonMetadata.ofComparison p C) L).length=
      List.ofFn (fun i : Fin (FiniteCode.size (C.Square L)) => f (FiniteCode.equiv.symm i)) :=
  FiniteCode.selectedPrefix_eq_ofFn _ _ _ (squareKey p C L) f
    (squareFlags_binary p C L) (squareCount_correct p C L)
    (squareKey_lt p C L) (squareKey_chosen p C L) (squareRank_correct p C L) read

theorem horizontal_compaction (values : List ℕ) (f : C.Horizontal L → ℕ)
    (read : ∀h,values[horizontalTypedKey p C L h]?.getD 0=f h) :
    SelectArray.selectedPrefix (horizontalFlags (ComparisonMetadata.ofComparison p C) L) values
      (horizontalFlags (ComparisonMetadata.ofComparison p C) L).length=
      List.ofFn (fun i : Fin (FiniteCode.size (C.Horizontal L)) => f (FiniteCode.equiv.symm i)) :=
  FiniteCode.selectedPrefix_eq_ofFn _ _ _ (horizontalTypedKey p C L) f
    (horizontalFlags_binary p C L) (horizontalCount_correct p C L)
    (horizontalTypedKey_lt p C L) (horizontalTypedKey_chosen p C L) (horizontalRank_correct p C L) read

end GroupWL.LayoutMetadata
