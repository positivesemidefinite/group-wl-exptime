import GroupWL.ConstructiveTensor
import GroupWL.ComputableSource
import GroupWL.SourceFiniteCodes

/-! The concrete source-to-dense-tensor function uses numeric index codes and
materialized finite Gaussian elimination throughout. -/
namespace GroupWL.ConstructiveSourceTensor

open SourceLayout ConstructiveCoordinates IncidenceTensor

variable {F T E : Type} [Field F] [DecidableEq F] [FiniteCode T] [FiniteCode E]
  {r : ℕ} (C : ComparisonData F T E r) (L : ℕ)

local instance : Fintype T := FiniteCode.fintype T
local instance : Fintype E := FiniteCode.fintype E
local instance : Fintype (C.Block L) := FiniteCode.fintype _
local instance : Fintype (C.Readout L) := FiniteCode.fintype _
local instance : DecidableEq (C.Block L) := (FiniteCode.equiv (α := C.Block L)).decidableEq
local instance : DecidableEq (C.Readout L) := (FiniteCode.equiv (α := C.Readout L)).decidableEq

def system : AffineSystem F (C.Block L) (C.Readout L) (C.readoutSpace L) :=
  ComputableSource.affineSystem C

def radicalCoordinates (j : C.Readout L) : Coordinates F (ReadoutRadical (system C L) j) :=
  readoutRadical (system C L) j (ComputableSource.readoutCoordinates C j)

section Prime
variable (p : ℕ) [Fact p.Prime]
variable (D : ComparisonData (ZMod p) T E r) (q : ℕ)

def description (hq : 0 < q)
    (ε : AlternatingBilinearMap (ZMod p) (PaddedInput (system D L) q)
      (PaddedOutput (system D L) q)) : Statement.TensorDescription p :=
  ConstructiveTensor.description q p (system D L) (radicalCoordinates D L) hq ε

def zeroDescription (hq : 0 < q) : Statement.TensorDescription p :=
  description L p D q hq AlternatingBilinearMap.zero

def chargedDescription (hq : 2 ≤ q) (β : D.Block L → ZMod p) : Statement.TensorDescription p :=
  description L p D q (by omega) (epsilonCharge (system D L) q hq β)

end Prime
end GroupWL.ConstructiveSourceTensor
