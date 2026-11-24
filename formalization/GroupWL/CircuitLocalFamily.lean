import GroupWL.CircuitRejection
import GroupWL.SourceLayout.ExactFamily

namespace GroupWL.CircuitRejection

open AddressedCircuit CircuitComparisons

variable {T : Type*} [Fintype T] {n L : ℕ}
variable (C : Circuit T (n + 3)) (F : Type*) [Field F]

/-- The explicit rejecting circuit shift has an exact local family through
`r+1` blocks in the actual site-and-square affine system. -/
noncomputable def rejecting_exact_family (hreject : ¬ C.Accepts)
    (hL : n + 4 < L + 2) :
    ((comparisons C F).affineSystem (L := L)).ExactLocalFamily
      ((comparisons C F).sourceShift (rejectingConstant C F)) (n + 4) :=
  (comparisons C F).exactLocalFamily_of_constantScalarImages
    (rejectingConstant C F) (rejectingImages C F)
    (rejecting_constant_images C F hreject) hL

/-- The manuscript's wire has `4K+1` links and `4K` internal scalar types,
where `K=r+1`. In the layout's indexing this is `L=4n+15`. -/
noncomputable def canonical_rejecting_exact_family (hreject : ¬ C.Accepts) :
    ((comparisons C F).affineSystem (L := 4 * n + 15)).ExactLocalFamily
      ((comparisons C F).sourceShift (rejectingConstant C F)) (n + 4) :=
  rejecting_exact_family C F hreject (by omega)

end GroupWL.CircuitRejection
