import GroupWL.MachinePrograms.GroupMapValidation

namespace GroupWL.MachinePrograms.GroupMapPrograms
open NatArrayLanguage GroupTablePrograms

variable {n m : ℕ}

theorem pairValid_iff (source target images : List ℕ)
    (op : Fin n → Fin n → Fin n) (op' : Fin m → Fin m → Fin m) (f : Fin n → Fin m)
    (hsource : ∀ x y : Fin n,operation n source x.val y.val=(op x y).val)
    (htarget : ∀ x y : Fin m,operation m target x.val y.val=(op' x y).val)
    (himages : ∀ x : Fin n,read images x.val=(f x).val) :
    (∀ x y : Fin n,pairValid n m source target images x.val y.val) ↔
      (∀ x y,f (op x y)=op' (f x) (f y)) ∧ Function.Injective f := by
  simp only [pairValid,hsource,himages,htarget]
  constructor
  · intro h
    exact ⟨fun x y => Fin.ext (h x y).1,fun x y he => Fin.ext ((h x y).2 (congrArg Fin.val he))⟩
  · rintro ⟨hm,hi⟩ x y
    exact ⟨congrArg Fin.val (hm x y),fun he => congrArg Fin.val (hi (Fin.ext he))⟩

theorem validate_correct (S : State) (M : ℕ)
    (op : Fin n → Fin n → Fin n) (op' : Fin m → Fin m → Fin m) (f : Fin n → Fin m)
    (hb : S.Bounded M) (hn : S.scalar .sourceOrder=n) (hm : S.scalar .targetOrder=m)
    (hnpos : 0<n) (hmpos : 0<m)
    (hsource : (S.array .source).length=n*n) (htarget : (S.array .target).length=m*m)
    (himages : (S.array .images).length=n)
    (hsourceVals : ∀ v∈S.array .source,v<n) (himageVals : ∀ v∈S.array .images,v<m)
    (hsourceRead : ∀ x y : Fin n,operation n (S.array .source) x.val y.val=(op x y).val)
    (htargetRead : ∀ x y : Fin m,operation m (S.array .target) x.val y.val=(op' x y).val)
    (himageRead : ∀ x : Fin n,read (S.array .images) x.val=(f x).val)
    (hroom : n*n≤M) (hroom' : m*m≤M) :
    ∃ t≤19*(n*n)+6,∃ T,Runs (storageBound Reg Arr M) validate S t T ∧ T.Bounded M ∧
      (T.scalar .result=1 ↔ (∀ x y,f (op x y)=op' (f x) (f y)) ∧ Function.Injective f) := by
  obtain ⟨t,ht,T,run,hT,ho⟩ := validate_runs S n m M hb hn hm hnpos hmpos
    hsource htarget himages hsourceVals himageVals hroom hroom'
  refine ⟨t,ht,T,run,hT,?_⟩
  rw [ho]
  have hc := (prefixValid_complete hnpos (S.array .source) (S.array .target) (S.array .images)).trans
    (pairValid_iff _ _ _ op op' f hsourceRead htargetRead himageRead)
  simpa using hc

variable {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]

def numericOperation (e : Fin n ≃ G) (x y : Fin n) : Fin n := e.symm (e x*e y)

theorem numeric_valid_iff (eG : Fin n ≃ G) (eH : Fin m ≃ H) (f : Fin n → Fin m) :
    ((∀ x y,f (numericOperation eG x y)=numericOperation eH (f x) (f y)) ∧ Function.Injective f) ↔
      (∀ x y,(eH ∘ f ∘ eG.symm) (x*y)=(eH ∘ f ∘ eG.symm) x*(eH ∘ f ∘ eG.symm) y) ∧
        Function.Injective (eH ∘ f ∘ eG.symm) := by
  constructor
  · rintro ⟨hm,hi⟩
    refine ⟨?_,eH.injective.comp (hi.comp eG.symm.injective)⟩
    intro x y
    simpa [numericOperation] using congrArg eH (hm (eG.symm x) (eG.symm y))
  · rintro ⟨hm,hi⟩
    refine ⟨?_,?_⟩
    · intro x y
      apply eH.injective
      simpa [numericOperation] using hm (eG x) (eG y)
    · intro x y he
      apply eG.injective
      apply hi
      simpa using congrArg eH he

theorem numeric_valid_isomorphic (eG : Fin n ≃ G) (eH : Fin m ≃ H) (f : Fin n → Fin m)
    (hnm : n=m)
    (h : (∀ x y,f (numericOperation eG x y)=numericOperation eH (f x) (f y)) ∧ Function.Injective f) :
    Nonempty (G ≃* H) := by
  obtain ⟨hm,hi⟩ := (numeric_valid_iff eG eH f).mp h
  have hc : Fintype.card G=Fintype.card H := by
    have hg := Fintype.card_congr eG
    have hh := Fintype.card_congr eH
    simp only [Fintype.card_fin] at hg hh
    omega
  have hb := (Fintype.bijective_iff_injective_and_card (eH ∘ f ∘ eG.symm)).mpr ⟨hi,hc⟩
  exact ⟨{ toEquiv := Equiv.ofBijective _ hb, map_mul' := hm }⟩

end GroupWL.MachinePrograms.GroupMapPrograms
