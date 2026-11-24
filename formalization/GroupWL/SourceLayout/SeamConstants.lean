import GroupWL.SourceLayout.Images

namespace GroupWL.SourceLayout.ComparisonData

open scoped BigOperators

variable {F T E : Type*} [Field F] {r L : ℕ}
  (C : ComparisonData F T E r)

theorem sum_rowMarker (hr : 0 < r) : (∑ i : Fin r, (rowMarker i : F)) = 1 := by
  let last : Fin r := ⟨r - 1, by omega⟩
  have hlast (i : Fin r) : i.val + 1 = r ↔ i = last := by
    constructor
    · intro hi
      apply Fin.ext
      dsimp [last]
      omega
    · intro hi
      subst i
      dsimp [last]
      omega
  simp [rowMarker, hlast]

theorem linkDelta_sourceShift (hr : 0 < r) (b : E → F)
    (l : Link E L) (a : C.DomainAddress l.comparison) :
    C.linkDelta (C.sourceShift b) l a = linkConstant b l := by
  change (∑ i : Fin r, (rowMarker i : F) * linkConstant b l) = _
  rw [← Finset.sum_mul, sum_rowMarker (F := F) hr, one_mul]

theorem comparisonDelta_sourceShift (hr : 0 < r) (b : E → F)
    (e : E) (a : C.DomainAddress e) :
    C.comparisonDelta (L := L) (C.sourceShift b) e a = b e := by
  simp [comparisonDelta, C.linkDelta_sourceShift hr, linkConstant]

theorem constantScalarImages_iff_sourceShift (hr : 0 < r) (b : E → F) (Q : C.ImageSets) :
    C.ConstantScalarImages b Q ↔ C.ScalarImages (L := L) (C.sourceShift b) Q := by
  constructor
  · intro h
    refine ⟨h.nonempty, ?_⟩
    intro e a
    simpa only [C.comparisonDelta_sourceShift hr] using h.comparison e a
  · intro h
    refine ⟨h.nonempty, ?_⟩
    intro e a
    simpa only [C.comparisonDelta_sourceShift hr] using h.comparison e a

end GroupWL.SourceLayout.ComparisonData
