import GroupWL.NamedChargeReduction
import GroupWL.ResidualAssembly
import GroupWL.GameRefinement
import GroupWL.SourceLayout.Owners

/-! Exact affine families give actual equivalent, nonisomorphic group pairs
without any remaining tensor residual or game hypotheses. -/
namespace GroupWL.IncidenceForward
open IncidenceTensor IncidenceCoordinates IncidenceGroup FrameResponses
open PebbleGame Refinement

variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)]
  {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module (ZMod p) (V j)]
  (A : AffineSystem (ZMod p) I J V) (q : ℕ) (hq : 2 ≤ q)

theorem winning_empty (β : I → ZMod p) (K m : ℕ) (hm : m < (q-1)*(K+1))
    (owner : J → I) (howner : ∀ j, j ∈ A.scope (owner j))
    (H : A.ExactLocalFamily β K) :
    Winning (empty : Position m (ZeroGroup A q hq) (ChargedGroup A q hq β)) := by
  have hw := ResidualAssembly.winning_of_exactAffineFamily A q
    (NeZero.ne (2 : ZMod p)) hq β K m hm owner howner H
  change Winning (empty : Position m
    (TensorGroup (evaluationTwist (Y A q hq)
      (twistCoordinates A q (inputCoordinates A q) (outputCoordinates A q)
        AlternatingBilinearMap.zero))) (ChargedGroup A q hq β))
  rw [NamedChargeReduction.zero_coordinates A q]
  exact hw

theorem equivalentII (β : I → ZMod p) (K k : ℕ) (hm : k+1 < (q-1)*(K+1))
    (owner : J → I) (howner : ∀ j, j ∈ A.scope (owner j))
    (H : A.ExactLocalFamily β K)
    [Fintype (ZeroGroup A q hq)] [Fintype (ChargedGroup A q hq β)] :
    EquivalentII k (ZeroGroup A q hq) (ChargedGroup A q hq β) :=
  GameRefinement.equivalentII_of_winning_empty k
    (winning_empty A q hq β K (k+1) hm owner howner H)

theorem not_identifiedII [Nonempty I] (hq3 : 3 ≤ q)
    (β : I → ZMod p) (hβ : β ∉ LinearMap.range A.linearMap)
    (K k : ℕ) (hm : k+1 < (q-1)*(K+1))
    (owner : J → I) (howner : ∀ j, j ∈ A.scope (owner j))
    (H : A.ExactLocalFamily β K) [Fintype (ZeroGroup A q hq)] :
    ¬ IdentifiesII k (ZeroGroup A q hq) := by
  classical
  letI := Fintype.ofFinite (ChargedGroup A q hq β)
  intro hi
  have he := equivalentII A q hq β K k hm owner howner H
  have hiso := hi ⟨ChargedGroup A q hq β, inferInstance, inferInstance⟩ he
  exact hβ ((NamedChargeReduction.zero_charge_iso A q hq hq3 β).mp hiso)

end GroupWL.IncidenceForward
