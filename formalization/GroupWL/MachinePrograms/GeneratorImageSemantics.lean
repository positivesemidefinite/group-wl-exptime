import GroupWL.MachinePrograms.GeneratorImageExpansion
import GroupWL.FiniteImageSearch

/-! The operational row scan recovers every genuine homomorphism from its
values on a generating tuple. -/
namespace GroupWL.MachinePrograms.GeneratorImages

open NatArrayLanguage Refinement
variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
  [DecidableEq G] [DecidableEq H] {rows cols k : ℕ}

theorem rowImage_hom (eG : Fin rows ≃ G) (eH : Fin cols ≃ H)
    (a : Fin k → G) (ha : Generates a) (f : G →* H) (xs : List ℕ)
    (hmask : ∀ x : Fin rows,∀ y : Fin cols,
      xs[x.val*cols+y.val]?.getD 0≠0 ↔
        (eG x,eH y)∈FiniteWordTypes.explore a (f ∘ a) (Fintype.card (G×H)))
    (identity : ℕ) (x : Fin rows) :
    rowImage xs cols identity x.val=(eH.symm (f (eG x))).val := by
  let y := eH.symm (f (eG x))
  have hmem : xs[x.val*cols+y.val]?.getD 0≠0 := by
    apply (hmask x y).mpr
    obtain ⟨w,hw⟩ := ha (eG x)
    have h := FiniteWordTypes.eval_mem_explore a (f ∘ a) w
    simpa only [GroupWord.eval_hom,hw,y,Equiv.apply_symm_apply] using h
  have hunique : ∀ i<cols,xs[x.val*cols+i]?.getD 0≠0 → i=y.val := by
    intro i hi hm
    obtain ⟨w,hw⟩ := FiniteWordTypes.explore_sound a (f ∘ a) _
      (eG x,eH ⟨i,hi⟩) ((hmask x ⟨i,hi⟩).mp hm)
    have hx := congrArg Prod.fst hw
    have hy := congrArg Prod.snd hw
    change w.eval a=eG x at hx
    change w.eval (f ∘ a)=eH ⟨i,hi⟩ at hy
    rw [GroupWord.eval_hom,hx] at hy
    have he : (⟨i,hi⟩ : Fin cols)=y := by
      apply eH.injective
      simpa [y] using hy.symm
    exact congrArg Fin.val he
  unfold rowImage
  rw [FirstNonzero.hit_eq_some_of_unique xs (x.val*cols) cols y.val y.isLt hmem hunique]
  rfl

theorem expand_hom_runs (eG : Fin rows ≃ G) (eH : Fin cols ≃ H)
    (a : Fin k → G) (ha : Generates a) (f : G →* H)
    (S : State) (M : ℕ) (hb : S.Bounded M)
    (hrows : S.scalar (.inr .rows)=rows) (hc : S.scalar (.inr .cols)=cols)
    (he : S.scalar (.inr .identity)=(eH.symm 1).val)
    (hlen : (S.array (.inl .input)).length=rows*cols) (hroom : rows*cols≤M)
    (hmask : ∀ x : Fin rows,∀ y : Fin cols,
      (S.array (.inl .input))[x.val*cols+y.val]?.getD 0≠0 ↔
        (eG x,eH y)∈FiniteWordTypes.explore a (f ∘ a) (Fintype.card (G×H))) :
    ∃ t≤rows*(9*cols+13)+5,∃ T,Runs (storageBound Reg Arr M) expand S t T ∧
      T.Bounded M ∧ T.array (.inr .images)=
        List.ofFn (fun x : Fin rows => (eH.symm (f (eG x))).val) := by
  have hM : 1≤M := by
    have hr := (eG.symm 1).isLt
    have hc := (eH.symm 1).isLt
    nlinarith
  obtain ⟨t,ht,T,run,hT,ho⟩ := expand_runs S M rows cols (eH.symm 1).val hb hrows hc he
    (eH.symm 1).isLt hlen hroom hM
  refine ⟨t,ht,T,run,hT,ho.trans ?_⟩
  congr 1
  funext x
  exact rowImage_hom eG eH a ha f _ hmask _ x

end GroupWL.MachinePrograms.GeneratorImages
