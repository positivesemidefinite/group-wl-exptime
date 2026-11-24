import GroupWL.MachinePrograms.GroupSaturationComplete

/-! Numeric saturation computes the genuine paired subgroup after any
explicit finite enumeration preserving the multiplication table. -/
namespace GroupWL.MachinePrograms.GroupSaturation

open NatArrayLanguage FiniteSetArrays Refinement

variable {n : ℕ} {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H]

theorem image_step (op : Fin n → Fin n → Fin n) (C : Finset (Fin n))
    (e : Fin n → G×H) (he : ∀ x y,e (op x y)=e x*e y) :
    (C ∪ C.biUnion (fun a => C.image (op a))).image e =
      PositiveWordTypes.step (C.image e) := by
  ext z
  simp only [PositiveWordTypes.step,Finset.mem_union,Finset.mem_image,Finset.mem_biUnion]
  constructor
  · rintro ⟨x,hx,hz⟩
    rcases hx with hx|⟨a,ha,b,hb,hx⟩
    · exact Or.inl ⟨x,hx,hz⟩
    · subst x
      exact Or.inr ⟨e a,⟨a,ha,rfl⟩,e b,⟨b,hb,rfl⟩,(he a b).symm.trans hz⟩
  · rintro (⟨x,hx,hz⟩|⟨a,⟨x,hx,ha⟩,b,⟨y,hy,hb⟩,hz⟩)
    · exact ⟨x,Or.inl hx,hz⟩
    · subst a; subst b
      exact ⟨op x y,Or.inr ⟨x,hx,y,hy,rfl⟩,(he x y).trans hz⟩

theorem image_closureSet {k : ℕ} (op : Fin n → Fin n → Fin n) (C : Finset (Fin n))
    (e : Fin n → G×H) (he : ∀ x y,e (op x y)=e x*e y)
    (a : Fin k → G) (b : Fin k → H)
    (hC : C.image e=insert 1 (Finset.univ.image (fun i => (a i,b i)))) (r : ℕ) :
    (closureSet op C r).image e=PositiveWordTypes.explore a b r := by
  induction r with
  | zero => exact hC
  | succ r ih =>
    rw [closureSet,image_step op _ e he,ih]
    rfl

variable [Fintype G] [Fintype H]

theorem mask_closure_mem {k : ℕ} (op : Fin n → Fin n → Fin n) (C : Finset (Fin n))
    (e : Fin n ≃ G×H) (he : ∀ x y,e (op x y)=e x*e y)
    (a : Fin k → G) (b : Fin k → H)
    (hC : C.image e=insert 1 (Finset.univ.image (fun i => (a i,b i)))) (j : Fin n) :
    j∈closureSet op C n ↔ e j∈FiniteWordTypes.explore a b (Fintype.card (G×H)) := by
  have hn : n=Fintype.card (G×H) := by simpa using Fintype.card_congr e
  have himage := image_closureSet op C e he a b hC n
  have hfinal : PositiveWordTypes.explore a b n=FiniteWordTypes.explore a b (Fintype.card (G×H)) := by
    rw [hn,PositiveWordTypes.explore_eq]
  rw [←himage.trans hfinal]
  constructor
  · intro hj; exact Finset.mem_image.mpr ⟨j,hj,rfl⟩
  · intro hj
    obtain ⟨x,hx,hxj⟩ := Finset.mem_image.mp hj
    exact e.injective hxj ▸ hx

theorem saturate_paired_runs {k : ℕ} (S : State) (M : ℕ)
    (C : Finset (Fin n)) (op : Fin n → Fin n → Fin n)
    (e : Fin n ≃ G×H) (he : ∀ x y,e (op x y)=e x*e y)
    (a : Fin k → G) (b : Fin k → H)
    (hC : C.image e=insert 1 (Finset.univ.image (fun i => (a i,b i))))
    (hb : S.Bounded M) (hn : S.scalar .order=n) (hcurrent : S.array .current=word C)
    (hlen : (S.array .table).length=n*n)
    (hread : ∀ i : Fin (n*n),(S.array .table)[i.val]?.getD 0=
      (op (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).val)
    (hroom : n*n≤M) :
    ∃ t≤10*n^3+8*n+5,∃ T,Runs (storageBound Reg Arr M) saturate S t T ∧
      T.Bounded M ∧ (T.array .current).length=n ∧
      ∀ j : Fin n,(T.array .current)[j.val]?.getD 0=1 ↔
        e j∈FiniteWordTypes.explore a b (Fintype.card (G×H)) := by
  have hpos : 0<n := by have := (e.symm 1).isLt; omega
  obtain ⟨t,ht,T,run,hT,ho⟩ := saturate_runs S n M C op hb hn hcurrent hlen hread hpos hroom
  refine ⟨t,ht,T,run,hT,by simp [ho],?_⟩
  intro j
  rw [ho,read_word]
  simpa using mask_closure_mem op C e he a b hC j

end GroupWL.MachinePrograms.GroupSaturation
