import GroupWL.CircuitComparisons
import GroupWL.SourceLayout.SeamConstants

/-! The explicit rejecting charge has no global solution, on every circuit.
The contradiction comes from the two broadcast identity buffers. -/

namespace GroupWL.CircuitComparisons

open AddressedCircuit SourceLayout SourceLayout.ComparisonData

variable {T F : Type*} {r L : ℕ} [Field F] (C : Circuit T r)

abbrev Values := ∀ t : RealType C, Address r → (Fin (dimension C t) → F)

def zeroAddress : Address r := fun _ => false

def broadcastCopyAddress (b k : Bool) :
    (comparisons C F).DomainAddress (.copy (.broadcastIdentity b) k) :=
  fun _ => ⟨false, Finset.mem_univ _⟩

def broadcastSumAddress (b : Bool) :
    (comparisons C F).DomainAddress (.sum (.broadcastIdentity b)) :=
  fun _ => ⟨false, Finset.mem_univ _⟩

theorem no_rejecting_comparison_values (h : Values (F := F) C)
    (heq : ∀ e (a : (comparisons C F).DomainAddress e),
      (comparisons C F).sourceForm e
          (h ((comparisons C F).source e) ((comparisons C F).sourceAddress a)) -
        (comparisons C F).targetForm e
          (h ((comparisons C F).target e) ((comparisons C F).targetAddress a)) =
        rejectingConstant C F e) : False := by
  have hself (b : Bool) : h (.inl .broadcast) zeroAddress (0 : Fin 1) =
      rejectingConstant C F (.sum (.broadcastIdentity b)) := by
    have h₀ := heq (.copy (.broadcastIdentity b) false) (broadcastCopyAddress C b false)
    have h₁ := heq (.copy (.broadcastIdentity b) true) (broadcastCopyAddress C b true)
    have hs := heq (.sum (.broadcastIdentity b)) (broadcastSumAddress C b)
    change h (.inl .broadcast) zeroAddress (0 : Fin 1) -
      h (.inr (.broadcastIdentity b)) zeroAddress (0 : Fin 2) = 0 at h₀
    change h (.inl .broadcast) zeroAddress (0 : Fin 1) -
      h (.inr (.broadcastIdentity b)) zeroAddress (1 : Fin 2) = 0 at h₁
    change h (.inr (.broadcastIdentity b)) zeroAddress (0 : Fin 2) +
      h (.inr (.broadcastIdentity b)) zeroAddress (1 : Fin 2) -
        h (.inl .broadcast) zeroAddress (0 : Fin 1) = _ at hs
    linear_combination h₀ + h₁ + hs
  have h0 : h (.inl .broadcast) zeroAddress (0 : Fin 1) = 0 := hself false
  have h1 : h (.inl .broadcast) zeroAddress (0 : Fin 1) = 1 := hself true
  exact zero_ne_one (h0.symm.trans h1)

theorem rejecting_shift_not_solvable [Fintype T] (hr : 0 < r) :
    (comparisons C F).sourceShift (L := L) (rejectingConstant C F) ∉
      LinearMap.range (comparisons C F).affineSystem.linearMap := by
  rintro ⟨z, hz⟩
  apply no_rejecting_comparison_values C
    (fun t a => (comparisons C F).realRing z t a)
  intro e a
  have h := (comparisons C F).comparison_equation_of_solution z _ hz e a
  simpa only [comparisonDelta_sourceShift _ hr] using h

end GroupWL.CircuitComparisons
