import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Prod

namespace GroupWL

variable {F A X B : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup X] [Module F X]
  [AddCommGroup B] [Module F B]

/-- A split exact sequence, with the splitting constructed by linear algebra. -/
theorem exists_exact_sequence_equiv (q : A →ₗ[F] X) (i : B →ₗ[F] A)
    (hq : Function.Surjective q) (hi : Function.Injective i)
    (hexact : LinearMap.range i = LinearMap.ker q) :
    ∃ E : (X × B) ≃ₗ[F] A,
      (∀ x b, q (E (x, b)) = x) ∧ (∀ b, E (0, b) = i b) := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqs : ∀ x, q (s x) = x := fun x => LinearMap.congr_fun hs x
  have hqi : ∀ b, q (i b) = 0 := by
    intro b
    have : i b ∈ LinearMap.ker q := hexact ▸ (LinearMap.mem_range_self i b)
    exact this
  let e : (X × B) →ₗ[F] A := s.coprod i
  have heq : ∀ x b, q (e (x, b)) = x := by intro x b; simp [e, hqs, hqi]
  have hinj : Function.Injective e := by
    intro u v huv
    have hx : u.1 = v.1 := by simpa only [heq] using congrArg q huv
    have hb : u.2 = v.2 := by
      apply hi
      change s u.1 + i u.2 = s v.1 + i v.2 at huv
      rw [hx] at huv
      exact add_left_cancel huv
    exact Prod.ext hx hb
  have hsurj : Function.Surjective e := by
    intro a
    have hmem : a - s (q a) ∈ LinearMap.ker q := by simp [LinearMap.mem_ker, hqs]
    rw [← hexact] at hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨(q a, b), ?_⟩
    change s (q a) + i b = a
    rw [hb]
    abel
  refine ⟨LinearEquiv.ofBijective e ⟨hinj, hsurj⟩, heq, ?_⟩
  intro b
  change s 0 + i b = i b
  simp

end GroupWL
