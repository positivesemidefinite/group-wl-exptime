import GroupWL.GadgetDecoding

/-! # Three-variable relations in the multiplication graph -/
namespace GroupWL.GadgetRelations

open Refinement InitialIWords GadgetDecoding
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Relation algebra syntax; composition uses one reusable intermediate name. -/
inductive Rel where
  | eq
  | adj
  | test : Fin 5 → Rel
  | comp : Rel → Rel → Rel
  | inter : Rel → Rel → Rel
  | union : Rel → Rel → Rel
  | converse : Rel → Rel

def Rel.Realize : Rel → GadgetVertex G → GadgetVertex G → Prop
  | .eq,x,y => x=y
  | .adj,x,y => gadgetAdj x y
  | .test t,x,y => vertexSort x=t ∧ x=y
  | .comp R S,x,y => ∃ z,R.Realize x z ∧ S.Realize z y
  | .inter R S,x,y => R.Realize x y ∧ S.Realize x y
  | .union R S,x,y => R.Realize x y ∨ S.Realize x y
  | .converse R,x,y => R.Realize y x

theorem exists_third {d : ℕ} (hd : 3 ≤ d) (i j : Fin d) :
    ∃ l : Fin d,l ≠ i ∧ l ≠ j := by
  have mk (n : ℕ) (hn : n < d) (hi : i.val ≠ n) (hj : j.val ≠ n) :
      ∃ l : Fin d,l ≠ i ∧ l ≠ j :=
    ⟨⟨n,hn⟩,fun h => hi (congrArg Fin.val h).symm,
      fun h => hj (congrArg Fin.val h).symm⟩
  by_cases h0 : i.val ≠ 0 ∧ j.val ≠ 0
  · exact mk 0 (by omega) h0.1 h0.2
  by_cases h1 : i.val ≠ 1 ∧ j.val ≠ 1
  · exact mk 1 (by omega) h1.1 h1.2
  exact mk 2 (by omega) (by omega) (by omega)

/-- Every relation-algebra expression is preserved by actual stable graph
colors in at least three dimensions. -/
theorem Rel.realize_iff [Fintype G] [Fintype H] [Nontrivial G] [Nontrivial H]
    {d : ℕ} (hd : 3 ≤ d) (R : Rel)
    {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (i j : Fin d) : R.Realize (a i) (a j) ↔ R.Realize (b i) (b j) := by
  induction R generalizing a b i j with
  | eq => exact h.eq_iff i j
  | adj => exact h.adj_iff i j
  | test t =>
      obtain ⟨l,hli,_⟩ := exists_third hd i j
      exact and_congr (by rw [h.sort_eq i l hli.symm]) (h.eq_iff i j)
  | comp R S ihR ihS =>
      obtain ⟨l,hli,hlj⟩ := exists_third hd i j
      obtain ⟨f,hf⟩ := h.matching
      have hR (x) : R.Realize (a i) x ↔ R.Realize (b i) (f x) := by
        simpa only [Function.update_self,Function.update_of_ne hli.symm] using
          ihR (hf x l) i l
      have hS (x) : S.Realize x (a j) ↔ S.Realize (f x) (b j) := by
        simpa only [Function.update_self,Function.update_of_ne hlj.symm] using
          ihS (hf x l) l j
      constructor
      · rintro ⟨x,hx,hy⟩
        exact ⟨f x,(hR x).mp hx,(hS x).mp hy⟩
      · rintro ⟨y,hx,hy⟩
        obtain ⟨x,rfl⟩ := f.surjective y
        exact ⟨x,(hR x).mpr hx,(hS x).mpr hy⟩
  | inter R S ihR ihS => exact and_congr (ihR h i j) (ihS h i j)
  | union R S ihR ihS => exact or_congr (ihR h i j) (ihS h i j)
  | converse R ih => exact ih h j i

/-- Follow an edge, then check the reached vertex's recovered sort. -/
def edgeTo (t : Fin 5) : Rel := .comp .adj (.test t)

theorem edgeTo_realize (t : Fin 5) (x y : GadgetVertex G) :
    (edgeTo t).Realize x y ↔ gadgetAdj x y ∧ vertexSort y=t := by
  simp [edgeTo,Rel.Realize,and_assoc,exists_eq_right]

/-- Paths from the central gadget vertex to its first input, second input,
and product, respectively. -/
def endpointPath : Fin 3 → Rel
  | ⟨0,_⟩ => .comp (edgeTo 0) (edgeTo 4)
  | ⟨1,_⟩ => edgeTo 4
  | ⟨2,_⟩ => .comp (edgeTo 2) (.comp (edgeTo 3) (edgeTo 4))

def endpoint (r : Fin 3) : Rel :=
  .union (.test 4) (.comp (.test 1) (endpointPath r))

/-- Coordinates read directly on group vertices and implicitly on gadget vertices. -/
def coord (r : Fin 3) : GadgetVertex G → G
  | .inl g => g
  | .inr (g,h,_) => if r=0 then g else if r=1 then h else g*h

def Usable (x : GadgetVertex G) : Prop := vertexSort x=4 ∨ vertexSort x=1

theorem edgeTo_internal (t : Fin 5) (g h : G) (j : Fin 4) (y : GadgetVertex G) :
    (edgeTo t).Realize (.inr (g,h,j)) y ↔ gadgetAdj (.inr (g,h,j)) y ∧ vertexSort y=t :=
  edgeTo_realize _ _ _

private theorem edgeTo_group (g h : G) (j : Fin 4) (y : GadgetVertex G) :
    (edgeTo 4).Realize (.inr (g,h,j)) y ↔
      (j=0 ∧ y=.inl g) ∨ (j=1 ∧ y=.inl h) ∨ (j=3 ∧ y=.inl (g*h)) := by
  cases y with
  | inl x => simp [edgeTo_realize,vertexSort,eq_comm,and_or_left]
  | inr v =>
      rcases v with ⟨x,y,l⟩
      fin_cases l <;> simp [edgeTo_realize,vertexSort]

private theorem edgeTo_tag (g h : G) (j l : Fin 4) (y : GadgetVertex G) :
    (edgeTo l.castSucc).Realize (.inr (g,h,j)) y ↔
      (j.val+1=l.val ∨ l.val+1=j.val) ∧ y=.inr (g,h,l) := by
  cases y with
  | inl x =>
      fin_cases l <;> simp [edgeTo_realize,vertexSort]
  | inr v =>
      rcases v with ⟨x,y,m⟩
      simp only [edgeTo_realize,adj_internal_internal,vertexSort,Fin.castSucc_inj,
        Sum.inr.injEq,Prod.mk.injEq]
      constructor
      · rintro ⟨⟨rfl,rfl,hjl⟩,rfl⟩
        exact ⟨hjl,rfl,rfl,rfl⟩
      · rintro ⟨hjl,rfl,rfl,rfl⟩
        exact ⟨⟨rfl,rfl,hjl⟩,rfl⟩

theorem endpointPath_realize (r : Fin 3) (g h : G) (y : GadgetVertex G) :
    (endpointPath r).Realize (.inr (g,h,(1:Fin 4))) y ↔
      y=.inl (coord r (.inr (g,h,(1:Fin 4)))) := by
  have e0 (z : GadgetVertex G) : (edgeTo 0).Realize (.inr (g,h,(1:Fin 4))) z ↔
      z=.inr (g,h,(0:Fin 4)) := by
    simpa using edgeTo_tag g h 1 0 z
  have e2 (z : GadgetVertex G) : (edgeTo 2).Realize (.inr (g,h,(1:Fin 4))) z ↔
      z=.inr (g,h,(2:Fin 4)) := by
    simpa using edgeTo_tag g h 1 2 z
  have e3 (z : GadgetVertex G) : (edgeTo 3).Realize (.inr (g,h,(2:Fin 4))) z ↔
      z=.inr (g,h,(3:Fin 4)) := by
    simpa using edgeTo_tag g h 2 3 z
  fin_cases r
  · change (∃ z,(edgeTo 0).Realize (.inr (g,h,(1:Fin 4))) z ∧
      (edgeTo 4).Realize z y) ↔ _
    simp only [e0,exists_eq_left,edgeTo_group]
    simp [coord]
  · change (edgeTo 4).Realize (.inr (g,h,(1:Fin 4))) y ↔ _
    simp only [edgeTo_group]
    simp [coord]
  · change (∃ z,(edgeTo 2).Realize (.inr (g,h,(1:Fin 4))) z ∧
      ∃ w,(edgeTo 3).Realize z w ∧ (edgeTo 4).Realize w y) ↔ _
    simp only [e2,exists_eq_left,e3,edgeTo_group]
    simp [coord]

theorem endpoint_realize (r : Fin 3) (x y : GadgetVertex G) :
    (endpoint r).Realize x y ↔ Usable x ∧ y=.inl (coord r x) := by
  cases x with
  | inl g => simp [endpoint,Rel.Realize,Usable,vertexSort,coord,eq_comm]
  | inr v =>
      rcases v with ⟨g,h,j⟩
      fin_cases j <;> simp [endpoint,Rel.Realize,Usable,vertexSort,endpointPath_realize]

def sameCoord (r s : Fin 3) : Rel := .comp (endpoint r) (.converse (endpoint s))

theorem sameCoord_realize (r s : Fin 3) (x y : GadgetVertex G) :
    (sameCoord r s).Realize x y ↔ Usable x ∧ Usable y ∧ coord r x=coord s y := by
  simp only [sameCoord,Rel.Realize,endpoint_realize]
  constructor
  · rintro ⟨z,⟨hx,hzx⟩,hy,hzy⟩
    exact ⟨hx,hy,Sum.inl.inj (hzx.symm.trans hzy)⟩
  · rintro ⟨hx,hy,he⟩
    exact ⟨.inl (coord r x),⟨hx,rfl⟩,hy,congrArg Sum.inl he⟩

/-- Stable colors preserve equalities between all marked implicit coordinates. -/
theorem coord_eq_iff [Fintype G] [Fintype H] [Nontrivial G] [Nontrivial H]
    {d : ℕ} (hd : 3 ≤ d) {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (i j : Fin d) (r s : Fin 3)
    (hai : Usable (a i)) (haj : Usable (a j))
    (hbi : Usable (b i)) (hbj : Usable (b j)) :
    coord r (a i)=coord s (a j) ↔ coord r (b i)=coord s (b j) := by
  have he := (sameCoord r s).realize_iff hd h i j
  simpa only [sameCoord_realize,hai,haj,hbi,hbj,true_and] using he

end GroupWL.GadgetRelations
