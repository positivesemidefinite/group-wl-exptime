import GroupWL.IsomorphismTransport

/-! Isomorphism invariance also for the ordinary neighbor-refinement
convention at Version-III dimension one. -/
namespace GroupWL.Refinement

universe u v

theorem neighborColor_equiv {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (e : A ≃ B) (adjA : A → A → Prop) (adjB : B → B → Prop)
    (hadj : ∀ a b, adjA a b ↔ adjB (e a) (e b)) (r : ℕ) (a : A) :
    neighborColor adjA r a = neighborColor adjB r (e a) := by
  classical
  induction r generalizing a with
  | zero => rfl
  | succ r ih =>
      change (neighborColor adjA r a,
        (Finset.univ.filter (adjA a)).val.map (neighborColor adjA r)) =
        (neighborColor adjB r (e a),
        (Finset.univ.filter (adjB (e a))).val.map (neighborColor adjB r))
      apply Prod.ext (ih a)
      have hm : (Finset.univ.filter (adjA a)).map e.toEmbedding =
          Finset.univ.filter (adjB (e a)) := by
        ext b
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.toEmbedding_apply]
        constructor
        · rintro ⟨c,hc,rfl⟩
          exact (hadj a c).mp hc
        · intro hb
          refine ⟨e.symm b,?_,e.apply_symm_apply b⟩
          exact (hadj a (e.symm b)).mpr (by simpa using hb)
      rw [← hm, Finset.map_val, Multiset.map_map]
      exact Multiset.map_congr rfl (fun b _ => ih b)

variable {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]

def gadgetMulEquiv (e : G ≃* H) : GadgetVertex G ≃ GadgetVertex H :=
  GadgetInterpretation.gadgetEquiv e.toEquiv (fun _ => e.toEquiv)

theorem gadgetMulEquiv_adj (e : G ≃* H) (a b : GadgetVertex G) :
    gadgetAdj a b ↔ gadgetAdj (gadgetMulEquiv e a) (gadgetMulEquiv e b) := by
  rcases a with a | ⟨a,b',i⟩ <;> rcases b with b | ⟨c,d,j⟩
  · rfl
  · change ((j=0 ∧ a=c) ∨ (j=1 ∧ a=d) ∨ (j=3 ∧ a=c*d)) ↔
      ((j=0 ∧ e a=e c) ∨ (j=1 ∧ e a=e d) ∨ (j=3 ∧ e a=e c*e d))
    simp only [← map_mul, e.injective.eq_iff]
  · change ((i=0 ∧ b=a) ∨ (i=1 ∧ b=b') ∨ (i=3 ∧ b=a*b')) ↔
      ((i=0 ∧ e b=e a) ∨ (i=1 ∧ e b=e b') ∨ (i=3 ∧ e b=e a*e b'))
    simp only [← map_mul, e.injective.eq_iff]
  · change (a=c ∧ b'=d ∧ (i.val+1=j.val ∨ j.val+1=i.val)) ↔
      (e a=e c ∧ e b'=e d ∧ (i.val+1=j.val ∨ j.val+1=i.val))
    simp only [e.injective.eq_iff]

theorem neighborGroupHistogram_equiv (e : G ≃* H) (r : ℕ) :
    neighborGroupHistogram (G := G) r = neighborGroupHistogram (G := H) r := by
  change Finset.univ.val.map (fun a : G => neighborColor gadgetAdj r (Sum.inl a)) = _
  have hc (a : G) : neighborColor gadgetAdj r (Sum.inl a) =
      neighborColor gadgetAdj r (Sum.inl (e a)) :=
    neighborColor_equiv (gadgetMulEquiv e) gadgetAdj gadgetAdj (gadgetMulEquiv_adj e) r _
  calc
    _ = Finset.univ.val.map (fun a : G => neighborColor gadgetAdj r (Sum.inl (e a))) :=
      Multiset.map_congr rfl (fun a _ => hc a)
    _ = (Finset.univ.val.map e.toEquiv).map
        (fun a : H => neighborColor gadgetAdj r (Sum.inl a)) := by rw [Multiset.map_map]; rfl
    _ = _ := by rw [Multiset.map_univ_val_equiv]; rfl

theorem equivalentIII_one_of_isomorphic (e : G ≃* H) : EquivalentIII 1 G H := by
  simp only [EquivalentIII, if_pos rfl]
  exact neighborGroupHistogram_equiv e

/-- No low-dimensional exception is needed for invariance under isomorphism. -/
theorem groupEquivalent_of_isomorphic (e : G ≃* H) (version : Version) (k : ℕ) :
    GroupEquivalent version k G H := by
  by_cases hk : k=1
  · subst k
    cases version with
    | one => exact equivalentI_of_isomorphic e 1
    | two => exact equivalentII_of_isomorphic e 1
    | three => exact equivalentIII_one_of_isomorphic e
  · exact TensorVersionCaps.groupEquivalent_of_isomorphic e version hk

theorem groupEquivalent_transport_left_all (e : G ≃* H)
    {K : Type*} [Group K] [Fintype K] (version : Version) (k : ℕ) :
    GroupEquivalent version k G K ↔ GroupEquivalent version k H K := by
  have he := groupEquivalent_of_isomorphic e version k
  exact ⟨fun h => he.symm.trans h,fun h => he.trans h⟩

theorem identifies_transport_all (e : G ≃* H) (version : Version) (k : ℕ) :
    Identifies version k G ↔ Identifies version k H := by
  constructor
  · intro hi J hj
    obtain ⟨f⟩ := hi J ((groupEquivalent_transport_left_all e version k).mpr hj)
    exact ⟨e.symm.trans f⟩
  · intro hi J hj
    obtain ⟨f⟩ := hi J ((groupEquivalent_transport_left_all e version k).mp hj)
    exact ⟨e.trans f⟩

end GroupWL.Refinement
