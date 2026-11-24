import GroupWL.GadgetInterpretation

/-! # Recovering sorts and marked coordinates from the uncolored graph -/
namespace GroupWL.GadgetDecoding

open Refinement InitialIWords GadgetInterpretation
universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable [Fintype G] [Fintype H] {d : ℕ}
noncomputable local instance : DecidableEq G := Classical.decEq G

abbrev SameGraph (a : Fin d → GadgetVertex G) (b : Fin d → GadgetVertex H) : Prop :=
  Stable (graphInitial gadgetAdj d) (graphInitial gadgetAdj d) a b

theorem SameGraph.eq_iff {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (i j : Fin d) : a i = a j ↔ b i = b j := by
  classical
  exact decide_eq_decide.mp (congrFun (congrFun (congrArg Prod.fst (h 0)) i) j)

theorem SameGraph.adj_iff {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (i j : Fin d) : gadgetAdj (a i) (a j) ↔ gadgetAdj (b i) (b j) := by
  classical
  exact decide_eq_decide.mp (congrFun (congrFun (congrArg Prod.snd (h 0)) i) j)

noncomputable def neighbors (v : GadgetVertex G) : Finset (GadgetVertex G) := by
  classical
  exact Finset.univ.filter (gadgetAdj v)

@[simp] theorem mem_neighbors (x y : GadgetVertex G) : x ∈ neighbors y ↔ gadgetAdj y x := by
  classical
  simp [neighbors]

/-- A replacement bijection restricts to an actual bijection of neighborhoods. -/
theorem SameGraph.neighborhoods {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (i j : Fin d) (hij : i ≠ j) :
    ∃ f : GadgetVertex G ≃ GadgetVertex H,
      (∀ x,gadgetAdj (a i) x ↔ gadgetAdj (b i) (f x)) ∧
      ∀ x,SameGraph (Function.update a j x) (Function.update b j (f x)) := by
  obtain ⟨f,hf⟩ := h.matching
  refine ⟨f,fun x => ?_,fun x => hf x j⟩
  have hh := SameGraph.adj_iff (hf x j) i j
  simpa only [Function.update_self,Function.update_of_ne hij] using hh

theorem SameGraph.degree_eq {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (i j : Fin d) (hij : i ≠ j) :
    (neighbors (a i)).card = (neighbors (b i)).card := by
  classical
  obtain ⟨f,hf,_⟩ := h.neighborhoods i j hij
  have he : (neighbors (a i)).map f.toEmbedding = neighbors (b i) := by
    ext y
    simp only [Finset.mem_map,mem_neighbors,Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (hf x).mp hx
    · intro hy
      exact ⟨f.symm y,(hf (f.symm y)).mpr (by simpa using hy),f.apply_symm_apply y⟩
  rw [← he,Finset.card_map]

omit [Fintype G] in
@[simp] theorem adj_group_group (g h : G) : ¬ gadgetAdj (.inl g) (.inl h) := by
  exact not_false

omit [Fintype G] in
@[simp] theorem adj_group_internal (x g h : G) (j : Fin 4) :
    gadgetAdj (.inl x) (.inr (g,h,j)) ↔
      (j=0 ∧ x=g) ∨ (j=1 ∧ x=h) ∨ (j=3 ∧ x=g*h) := Iff.rfl
omit [Fintype G] in
@[simp] theorem adj_internal_group (x g h : G) (j : Fin 4) :
    gadgetAdj (.inr (g,h,j)) (.inl x) ↔
      (j=0 ∧ x=g) ∨ (j=1 ∧ x=h) ∨ (j=3 ∧ x=g*h) := Iff.rfl
omit [Fintype G] in
@[simp] theorem adj_internal_internal (g h g' h' : G) (i j : Fin 4) :
    gadgetAdj (.inr (g,h,i)) (.inr (g',h',j)) ↔
      g=g' ∧ h=h' ∧ (i.val+1=j.val ∨ j.val+1=i.val) := Iff.rfl

theorem neighbors_zero (g h : G) :
    neighbors (.inr (g,h,(0:Fin 4))) = {Sum.inl g,Sum.inr (g,h,1)} := by
  classical
  ext v
  cases v with
  | inl x => simp [eq_comm]
  | inr v =>
      rcases v with ⟨x,y,j⟩
      fin_cases j <;> simp [eq_comm,and_left_comm,and_assoc]

theorem neighbors_one (g h : G) :
    neighbors (.inr (g,h,(1:Fin 4))) = {Sum.inl h,Sum.inr (g,h,0),Sum.inr (g,h,2)} := by
  classical
  ext v
  cases v with
  | inl x => simp [eq_comm]
  | inr v =>
      rcases v with ⟨x,y,j⟩
      fin_cases j <;> simp [eq_comm,and_left_comm,and_assoc]

theorem neighbors_two (g h : G) :
    neighbors (.inr (g,h,(2:Fin 4))) = {Sum.inr (g,h,1),Sum.inr (g,h,3)} := by
  classical
  ext v
  cases v with
  | inl x => simp
  | inr v =>
      rcases v with ⟨x,y,j⟩
      fin_cases j <;> simp [eq_comm,and_left_comm,and_assoc]

theorem neighbors_three (g h : G) :
    neighbors (.inr (g,h,(3:Fin 4))) = {Sum.inl (g*h),Sum.inr (g,h,2)} := by
  classical
  ext v
  cases v with
  | inl x => simp [eq_comm]
  | inr v =>
      rcases v with ⟨x,y,j⟩
      fin_cases j <;> simp [eq_comm,and_left_comm,and_assoc]

theorem degree_internal (g h : G) (j : Fin 4) :
    (neighbors (.inr (g,h,j))).card = if j=1 then 3 else 2 := by
  classical
  fin_cases j <;> simp [neighbors_zero,neighbors_one,neighbors_two,neighbors_three]

theorem degree_group_gt [Nontrivial G] (g : G) : 3 < (neighbors (.inl g)).card := by
  classical
  obtain ⟨t,ht⟩ := exists_ne (1:G)
  let s : Finset (GadgetVertex G) :=
    {Sum.inr (g,1,0),Sum.inr (g,t,0),Sum.inr (1,g,1),Sum.inr (1,g,3)}
  have hs : s ⊆ neighbors (.inl g) := by
    intro v hv
    simp only [s,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl|rfl|rfl <;> simp
  have hc : s.card = 4 := by simp [s,ht,ht.symm]
  have := Finset.card_le_card hs
  omega

/-- The group sort is recovered from the uncolored graph by degree. -/
def IsGroup : GadgetVertex G → Prop
  | .inl _ => True
  | .inr _ => False

theorem isGroup_iff_degree [Nontrivial G] (x : GadgetVertex G) :
    IsGroup x ↔ 3 < (neighbors x).card := by
  cases x with
  | inl g => exact iff_of_true trivial (degree_group_gt g)
  | inr v =>
      rcases v with ⟨g,h,j⟩
      simp only [IsGroup,degree_internal]
      split_ifs <;> norm_num

theorem SameGraph.isGroup_iff [Nontrivial G] [Nontrivial H]
    {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (i j : Fin d) (hij : i ≠ j) :
    IsGroup (a i) ↔ IsGroup (b i) := by
  rw [isGroup_iff_degree,isGroup_iff_degree,h.degree_eq i j hij]

/-- The internal path position, with four denoting the group sort. -/
def vertexSort : GadgetVertex G → Fin 5
  | .inl _ => 4
  | .inr (_,_,j) => j.castSucc

def HasGroupNeighbor (x : GadgetVertex G) : Prop :=
  ∃ y,gadgetAdj x y ∧ IsGroup y

def HasDegreeThreeNeighbor (x : GadgetVertex G) : Prop :=
  ∃ y,gadgetAdj x y ∧ (neighbors y).card = 3

theorem hasGroupNeighbor_internal (g h : G) (j : Fin 4) :
    HasGroupNeighbor (.inr (g,h,j)) ↔ j ≠ 2 := by
  unfold HasGroupNeighbor
  simp only [Sum.exists,IsGroup,and_true,and_false,exists_false,or_false,
    adj_internal_group]
  fin_cases j <;> simp

theorem degree_three_iff [Nontrivial G] (v : GadgetVertex G) :
    (neighbors v).card = 3 ↔ ∃ g h,v = .inr (g,h,(1:Fin 4)) := by
  cases v with
  | inl g =>
      have hg := degree_group_gt g
      constructor
      · intro hh
        omega
      · rintro ⟨g',h',he⟩
        cases he
  | inr v =>
      rcases v with ⟨g,h,j⟩
      simp only [degree_internal,Sum.inr.injEq,Prod.mk.injEq]
      fin_cases j <;> simp

theorem hasDegreeThreeNeighbor_internal [Nontrivial G] (g h : G) (j : Fin 4) :
    HasDegreeThreeNeighbor (.inr (g,h,j)) ↔ j=0 ∨ j=2 := by
  simp only [HasDegreeThreeNeighbor,degree_three_iff]
  constructor
  · rintro ⟨y,hxy,g',h',rfl⟩
    simp only [adj_internal_internal] at hxy
    fin_cases j <;> simp_all
  · intro hj
    refine ⟨.inr (g,h,1),?_,g,h,rfl⟩
    rcases hj with rfl|rfl <;> simp

theorem SameGraph.hasGroupNeighbor_iff [Nontrivial G] [Nontrivial H]
    {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (i j : Fin d) (hij : i ≠ j) :
    HasGroupNeighbor (a i) ↔ HasGroupNeighbor (b i) := by
  obtain ⟨f,hf,hh⟩ := h.neighborhoods i j hij
  have hs (x : GadgetVertex G) : IsGroup x ↔ IsGroup (f x) := by
    have hs := (hh x).isGroup_iff j i hij.symm
    simpa only [Function.update_self] using hs
  constructor
  · rintro ⟨x,hx,hg⟩
    exact ⟨f x,(hf x).mp hx,(hs x).mp hg⟩
  · rintro ⟨y,hy,hg⟩
    obtain ⟨x,rfl⟩ := f.surjective y
    exact ⟨x,(hf x).mpr hy,(hs x).mpr hg⟩

theorem SameGraph.hasDegreeThreeNeighbor_iff
    {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (i j : Fin d) (hij : i ≠ j) :
    HasDegreeThreeNeighbor (a i) ↔ HasDegreeThreeNeighbor (b i) := by
  obtain ⟨f,hf,hh⟩ := h.neighborhoods i j hij
  have hs (x : GadgetVertex G) : (neighbors x).card = (neighbors (f x)).card := by
    have hs := (hh x).degree_eq j i hij.symm
    simpa only [Function.update_self] using hs
  constructor
  · rintro ⟨x,hx,hg⟩
    exact ⟨f x,(hf x).mp hx,(hs x) ▸ hg⟩
  · rintro ⟨y,hy,hg⟩
    obtain ⟨x,rfl⟩ := f.surjective y
    exact ⟨x,(hf x).mpr hy,(hs x).symm ▸ hg⟩

/-- Even though the gadget graph is uncolored, stable colors recover all five
vertex sorts using degrees and two successive neighborhood tests. -/
theorem SameGraph.sort_eq [Nontrivial G] [Nontrivial H]
    {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (i j : Fin d) (hij : i ≠ j) :
    vertexSort (a i) = vertexSort (b i) := by
  have hg := h.isGroup_iff i j hij
  have hd := h.degree_eq i j hij
  have hn := h.hasGroupNeighbor_iff i j hij
  have ht := h.hasDegreeThreeNeighbor_iff i j hij
  cases ha : a i with
  | inl x =>
      cases hb : b i with
      | inl y => rfl
      | inr y => simp [ha,hb,IsGroup] at hg
  | inr x =>
      cases hb : b i with
      | inl y => simp [ha,hb,IsGroup] at hg
      | inr y =>
          rcases x with ⟨x₀,x₁,l⟩
          rcases y with ⟨y₀,y₁,m⟩
          rw [ha,hb] at hd hn ht
          simp only [degree_internal] at hd
          simp only [hasGroupNeighbor_internal] at hn
          simp only [hasDegreeThreeNeighbor_internal] at ht
          fin_cases l <;> fin_cases m <;> simp_all [vertexSort]

end GroupWL.GadgetDecoding
