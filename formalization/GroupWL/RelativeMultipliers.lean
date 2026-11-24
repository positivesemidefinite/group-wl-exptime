import GroupWL.GlobalMultipliers

/-! # Relative multipliers on good vertices

The domain below can be any retained query subspace. The input map need not
be surjective, and no nondegeneracy of its restricted coordinate pairing is
assumed. Rank two of the scalar projections is the only local hypothesis.
-/
namespace GroupWL.IncidenceTensor

set_option linter.unusedSectionVars false

universe u v
variable {F I J : Type u} [Field F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {V : J → Type u} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]
variable (A : AffineSystem F I J V) {q : ℕ}
variable {T : Type v} [AddCommGroup T] [Module F T]

def vertexProjection (g : T →ₗ[F] OldInput A q) (v : I ⊕ J) :
    T →ₗ[F] (Fin q → RingAt A v) := (LinearMap.proj v).comp g

def scalarVertexProjection (g : T →ₗ[F] OldInput A q) (v : I ⊕ J) :
    T →ₗ[F] (Fin q → F) := LocalMultiplier.scalarMap (vertexProjection A g v)

def GoodVertex (g : T →ₗ[F] OldInput A q) (v : I ⊕ J) : Prop :=
  1 < Module.finrank F (scalarVertexProjection A g v).range

theorem relative_internal_diagonal_relation
    (P g : T →ₗ[F] OldInput A q)
    (hdiag : ∀ x, omega A q (P x) (g x) = 0)
    (x : T) (v : I ⊕ J) (a b : Fin q) :
    P x v a * g x v b = P x v b * g x v a := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have h := congrArg (fun z : OldOutput A q => z.1 v ⟨(a, b), hab⟩) (hdiag x)
    change P x v a * g x v b - g x v a * P x v b = 0 at h
    rw [mul_comm (g x v a)] at h
    exact sub_eq_zero.mp h
  · subst b; rfl
  · have h := congrArg (fun z : OldOutput A q => z.1 v ⟨(b, a), hab⟩) (hdiag x)
    change P x v b * g x v a - g x v b * P x v a = 0 at h
    rw [mul_comm (g x v b)] at h
    exact (sub_eq_zero.mp h).symm

theorem relative_vertex_multiplier
    (P g : T →ₗ[F] OldInput A q)
    (hdiag : ∀ x, omega A q (P x) (g x) = 0)
    (v : I ⊕ J) (hv : GoodVertex A g v) :
    ∃! r : RingAt A v, ∀ x k, P x v k = r * g x v k := by
  exact LocalMultiplier.squareZero_existsUnique_multiplier_of_rank
    (vertexProjection A P v) (vertexProjection A g v)
    (fun x i j => relative_internal_diagonal_relation A P g hdiag x v i j) hv

/-- A good vertex supplies a coordinate whose scalar functional is nonzero. -/
theorem goodVertex_nonzero_scalar (g : T →ₗ[F] OldInput A q)
    (v : I ⊕ J) (hv : GoodVertex A g v) :
    ∃ a : Fin q, ∃ x : T, (g x v a).fst ≠ 0 := by
  by_contra h
  have hz : scalarVertexProjection A g v = 0 := by
    ext x a
    exact not_ne_iff.mp (fun hx => h ⟨a, x, hx⟩)
  unfold GoodVertex at hv
  rw [hz] at hv
  rw [LinearMap.range_zero] at hv
  simp at hv

/-- A good vertex has a nonzero scalar wedge in one of the actual stored
triangular output coordinates. -/
theorem goodVertex_exists_scalar_minor (g : T →ₗ[F] OldInput A q)
    (v : I ⊕ J) (hv : GoodVertex A g v) :
    ∃ x y : T, ∃ ab : Pair q,
      (g x v ab.1.1).fst * (g y v ab.1.2).fst -
        (g y v ab.1.1).fst * (g x v ab.1.2).fst ≠ 0 := by
  obtain ⟨x, y, hxy⟩ := LocalMultiplier.independent_images_of_one_lt_finrank
    (scalarVertexProjection A g v) hv
  obtain ⟨a, b, hab⟩ := LocalMultiplier.exists_minor_ne_zero hxy
  change (g x v a).fst * (g y v b).fst - (g x v b).fst * (g y v a).fst ≠ 0 at hab
  rcases lt_trichotomy a b with hlt | heq | hgt
  · refine ⟨x, y, ⟨(a, b), hlt⟩, ?_⟩
    change (g x v a).fst * (g y v b).fst - (g y v a).fst * (g x v b).fst ≠ 0
    rw [mul_comm (g y v a).fst]
    exact hab
  · subst b; exact False.elim (hab (sub_self _))
  · refine ⟨x, y, ⟨(b, a), hgt⟩, ?_⟩
    intro hz
    apply hab
    linear_combination -hz

theorem multiplier_unique_of_good
    (P g : T →ₗ[F] OldInput A q) (v : I ⊕ J) (hv : GoodVertex A g v)
    (r s : RingAt A v)
    (hr : ∀ x k, P x v k = r * g x v k)
    (hs : ∀ x k, P x v k = s * g x v k) : r = s := by
  obtain ⟨a, x, hx⟩ := goodVertex_nonzero_scalar A g v hv
  apply ((LocalMultiplier.squareZero_isUnit_iff _).mpr hx).mul_right_cancel
  exact (hr x a).symm.trans (hs x a)

/-- The same multiplier is read after restricting to a smaller query space
whenever the vertex remains good there. -/
theorem multiplier_restriction_eq
    {T' : Type*} [AddCommGroup T'] [Module F T']
    (P g : T →ₗ[F] OldInput A q) (ι : T' →ₗ[F] T)
    (v : I ⊕ J) (hv : GoodVertex A (g.comp ι) v)
    (r s : RingAt A v)
    (hr : ∀ x k, P x v k = r * g x v k)
    (hs : ∀ x k, P (ι x) v k = s * g (ι x) v k) : r = s :=
  multiplier_unique_of_good A (P.comp ι) (g.comp ι) v hv r s
    (fun x k => hr (ι x) k) hs

theorem relative_incidence_compatibility
    (P g : T →ₗ[F] OldInput A q)
    (hdiag : ∀ x, omega A q (P x) (g x) = 0)
    (e : Incidence A)
    (hi : GoodVertex A g (.inl e.1.1)) (hj : GoodVertex A g (.inr e.1.2))
    (ri : RingAt A (.inl e.1.1)) (rj : RingAt A (.inr e.1.2))
    (hri : ∀ x k, P x (.inl e.1.1) k = ri * g x (.inl e.1.1) k)
    (hrj : ∀ x k, P x (.inr e.1.2) k = rj * g x (.inr e.1.2) k) :
    ri = endpointMap A e rj := by
  obtain ⟨a, xa, hxa⟩ := goodVertex_nonzero_scalar A g (.inl e.1.1) hi
  obtain ⟨b, xb, hxb⟩ := goodVertex_nonzero_scalar A g (.inr e.1.2) hj
  let x : T →ₗ[F] EdgeRing (F := F) :=
    (LinearMap.proj a).comp (vertexProjection A g (.inl e.1.1))
  let y : T →ₗ[F] EdgeRing (F := F) :=
    (endpointMap A e).toLinearMap.comp
      ((LinearMap.proj b).comp (vertexProjection A g (.inr e.1.2)))
  apply LocalMultiplier.incidence_compatibility_of_nonzero_scalars
    (LocalMultiplier.scalarProjection (F := F) (N := F))
    (fun z hz => (LocalMultiplier.squareZero_isUnit_iff z).mpr hz)
    x.toAddMonoidHom y.toAddMonoidHom
  · exact ⟨xa, hxa⟩
  · refine ⟨xb, ?_⟩
    simpa [y, vertexProjection, endpointMap, LocalMultiplier.scalarProjection] using hxb
  · intro u
    have h := congrArg (fun z : OldOutput A q => z.2 e (a, b)) (hdiag u)
    change P u (.inl e.1.1) a * endpointMap A e (g u (.inr e.1.2) b) -
      g u (.inl e.1.1) a * endpointMap A e (P u (.inr e.1.2) b) = 0 at h
    rw [hri, hrj, map_mul] at h
    change (ri * g u (.inl e.1.1) a) * endpointMap A e (g u (.inr e.1.2) b) =
      (endpointMap A e rj * endpointMap A e (g u (.inr e.1.2) b)) *
        g u (.inl e.1.1) a
    linear_combination h

/-- Compatible multipliers on one complete good star obey the original
readout relation, even when other vertices have no multiplier. -/
theorem relative_good_star_relation
    (g : T →ₗ[F] OldInput A q) (r : ∀ v, RingAt A v)
    (hr : ∀ e : Incidence A, GoodVertex A g (.inl e.1.1) →
      GoodVertex A g (.inr e.1.2) →
      r (.inl e.1.1) = endpointMap A e (r (.inr e.1.2)))
    (j : J) (hj : GoodVertex A g (.inr j))
    (hstar : ∀ i, j ∈ A.scope i → GoodVertex A g (.inl i)) :
    ∑ i, (r (.inl i)).snd • A.coefficient i j = 0 := by
  classical
  have hk := (r (.inr j)).snd.property
  change (∑ i : Neighbors A j,
    (r (.inr j)).snd.val i • A.coefficient i.val j) = 0 at hk
  have hi (i : Neighbors A j) : (r (.inr j)).snd.val i = (r (.inl i.val)).snd := by
    have he := congrArg TrivSqZeroExt.snd
      (hr ⟨(i.val, j), i.property⟩ (hstar i.val i.property) hj)
    simpa [endpointMap, readoutProjection] using he.symm
  simp only [hi] at hk
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun i => j ∈ A.scope i)
    (fun i => (r (.inl i)).snd • A.coefficient i j)
  have hz : (∑ i : {i // j ∉ A.scope i},
      (r (.inl i.val)).snd • A.coefficient i.val j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [A.coefficient_outside i.val j i.property, smul_zero]
  rw [hk, hz, add_zero] at hsum
  exact hsum.symm

theorem relative_multiplier_classification
    (P g : T →ₗ[F] OldInput A q)
    (hdiag : ∀ x, omega A q (P x) (g x) = 0) :
    ∃ r : ∀ v, RingAt A v,
      (∀ v, GoodVertex A g v → ∀ x k, P x v k = r v * g x v k) ∧
      (∀ e : Incidence A, GoodVertex A g (.inl e.1.1) →
        GoodVertex A g (.inr e.1.2) →
        r (.inl e.1.1) = endpointMap A e (r (.inr e.1.2))) ∧
      (∀ j, GoodVertex A g (.inr j) →
        (∀ i, j ∈ A.scope i → GoodVertex A g (.inl i)) →
        ∑ i, (r (.inl i)).snd • A.coefficient i j = 0) := by
  classical
  have hex (v : I ⊕ J) : ∃ r : RingAt A v,
      GoodVertex A g v → ∀ x k, P x v k = r * g x v k := by
    by_cases hv : GoodVertex A g v
    · obtain ⟨r, hr, _⟩ := relative_vertex_multiplier A P g hdiag v hv
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => (hv h).elim⟩
  choose r hr using hex
  have he (e : Incidence A) (hi : GoodVertex A g (.inl e.1.1))
      (hj : GoodVertex A g (.inr e.1.2)) :=
    relative_incidence_compatibility A P g hdiag e hi hj _ _ (hr _ hi) (hr _ hj)
  exact ⟨r, hr, he, relative_good_star_relation A g r he⟩

end GroupWL.IncidenceTensor
