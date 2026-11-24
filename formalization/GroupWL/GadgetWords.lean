import GroupWL.GadgetRelations

/-! # Group-word tests on packed multiplication-graph vertices -/
namespace GroupWL.GadgetWords

open Refinement InitialIWords GadgetDecoding GadgetRelations
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] {d k : ℕ}

theorem sort_one_iff (v : GadgetVertex G) :
    vertexSort v=1 ↔ ∃ g h,v=.inr (g,h,(1:Fin 4)) := by
  cases v with
  | inl g => simp [vertexSort]
  | inr v =>
      rcases v with ⟨g,h,j⟩
      fin_cases j <;> simp [vertexSort]

@[simp] theorem usable_group (g : G) : Usable (.inl g) := Or.inl rfl
@[simp] theorem usable_pair (g h : G) : Usable (.inr (g,h,(1:Fin 4))) := Or.inr rfl
@[simp] theorem coord_group (r : Fin 3) (g : G) : coord r (.inl g) = g := rfl
@[simp] theorem coord_pair_zero (g h : G) : coord 0 (.inr (g,h,(1:Fin 4))) = g := rfl
@[simp] theorem coord_pair_one (g h : G) : coord 1 (.inr (g,h,(1:Fin 4))) = h := rfl
@[simp] theorem coord_pair_two (g h : G) : coord 2 (.inr (g,h,(1:Fin 4))) = g*h := rfl

/-- The unique idempotent is recognized using a gadget with equal inputs and product. -/
def idempotentTest : Rel := .inter (.test 1) (.inter (sameCoord 0 1) (sameCoord 0 2))

def oneTest (r : Fin 3) : Rel :=
  .comp (sameCoord r 0) (.comp idempotentTest (.converse (sameCoord r 0)))

theorem oneTest_realize (r : Fin 3) (x : GadgetVertex G) :
    (oneTest r).Realize x x ↔ Usable x ∧ coord r x=1 := by
  constructor
  · rintro ⟨y,hxy,z,⟨⟨hys,hyz⟩,hy1,hy2⟩,hxz⟩
    subst z
    obtain ⟨g,h,rfl⟩ := (sort_one_iff y).mp hys
    obtain ⟨hx,_,hxr⟩ := (sameCoord_realize r 0 _ _).mp hxy
    have hgh : g=h := ((sameCoord_realize 0 1 _ _).mp hy1).2.2
    have hmul : g=g*h := ((sameCoord_realize 0 2 _ _).mp hy2).2.2
    have hh : h=1 := by
      apply mul_left_cancel (a := g)
      simpa using hmul.symm
    exact ⟨hx,hxr.trans (hgh.trans hh)⟩
  · rintro ⟨hx,hx1⟩
    let y : GadgetVertex G := .inr (1,1,1)
    have hxy : (sameCoord r 0).Realize x y := by
      apply (sameCoord_realize _ _ _ _).mpr
      exact ⟨hx,usable_pair _ _,hx1⟩
    refine ⟨y,hxy,y,?_,hxy⟩
    refine ⟨⟨rfl,rfl⟩,?_,?_⟩ <;>
      apply (sameCoord_realize _ _ _ _).mpr <;> simp [y]

inductive Formula (d : ℕ) where
  | atom : Rel → Fin d → Fin d → Formula d
  | and : Formula d → Formula d → Formula d
  | ex : Fin d → Formula d → Formula d

def Formula.Realize (a : Fin d → GadgetVertex G) : Formula d → Prop
  | .atom R i j => R.Realize (a i) (a j)
  | .and φ ψ => φ.Realize a ∧ ψ.Realize a
  | .ex i φ => ∃ x,φ.Realize (Function.update a i x)

theorem Formula.realize_iff [Fintype G] [Fintype H] [Nontrivial G] [Nontrivial H]
    (hd : 3 ≤ d) (φ : Formula d) {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) : φ.Realize a ↔ φ.Realize b := by
  induction φ generalizing a b with
  | atom R i j => exact R.realize_iff hd h i j
  | and φ ψ ihφ ihψ => exact and_congr (ihφ h) (ihψ h)
  | ex i φ ih =>
      obtain ⟨f,hf⟩ := h.matching
      constructor
      · rintro ⟨x,hx⟩
        exact ⟨f x,(ih (hf x i)).mp hx⟩
      · rintro ⟨y,hy⟩
        obtain ⟨x,rfl⟩ := f.surjective y
        exact ⟨x,(ih (hf x i)).mpr hy⟩

/-- A coordinate name consists of a graph slot and one of its implicit group coordinates. -/
abbrev Coordinate (d : ℕ) := Fin d × Fin 3

def read (a : Fin d → GadgetVertex G) (c : Coordinate d) : G := coord c.2 (a c.1)

def eqCoords (c e : Coordinate d) : Formula d := .atom (sameCoord c.2 e.2) c.1 e.1

theorem eqCoords_realize (a : Fin d → GadgetVertex G) (c e : Coordinate d) :
    (eqCoords c e).Realize a ↔ Usable (a c.1) ∧ Usable (a e.1) ∧ read a c=read a e :=
  sameCoord_realize _ _ _ _

/-- One new gadget contains the leading letter, the remainder value and their product. -/
def evaluationFormula (input : Fin k → Coordinate d) :
    List (Letter k) → Coordinate d → Fin d → Formula d
  | [],out,_ => .atom (oneTest out.2) out.1 out.1
  | (i,negative)::L,out,helper =>
      .ex helper (.and (.atom (.test 1) helper helper)
        (.and (eqCoords (input i) (helper,0))
          (.and (eqCoords out (helper,if negative then 1 else 2))
            (evaluationFormula input L (helper,if negative then 2 else 1) out.1))))

private theorem read_update (a : Fin d → GadgetVertex G) (c : Coordinate d)
    (j : Fin d) (x : GadgetVertex G) (hc : c.1 ≠ j) :
    read (Function.update a j x) c = read a c := by
  simp only [read,Function.update_of_ne hc]

private theorem input_update (input : Fin k → Coordinate d) (a : Fin d → GadgetVertex G)
    (j : Fin d) (x : GadgetVertex G) (hj : ∀ i,(input i).1 ≠ j) :
    (fun i => read (Function.update a j x) (input i)) = fun i => read a (input i) := by
  funext i
  exact read_update _ _ _ _ (hj i)

/-- Exact semantics of the packed-coordinate evaluator. -/
theorem evaluationFormula_correct (input : Fin k → Coordinate d) (L : List (Letter k))
    (out : Coordinate d) (helper : Fin d) (hneq : out.1 ≠ helper)
    (hout : ∀ i,(input i).1 ≠ out.1) (hhelper : ∀ i,(input i).1 ≠ helper)
    (a : Fin d → GadgetVertex G) (hinput : ∀ i,Usable (a (input i).1))
    (husable : Usable (a out.1)) :
    (evaluationFormula input L out helper).Realize a ↔
      read a out = listEval (fun i => read a (input i)) L := by
  induction L generalizing out helper a with
  | nil => simpa [evaluationFormula,Formula.Realize,oneTest_realize,read,husable]
  | cons l L ih =>
      rcases l with ⟨i,negative⟩
      cases negative <;>
        simp only [evaluationFormula,Formula.Realize,Bool.false_eq_true,if_false,if_true,
          Rel.Realize,Function.update_self,and_true]
      · constructor
        · rintro ⟨y,hys,hgen,houty,htail⟩
          obtain ⟨g,t,rfl⟩ := (sort_one_iff y).mp hys
          have hu (j : Fin k) : Usable (Function.update a helper (.inr (g,t,1)) (input j).1) := by
            simpa only [Function.update_of_ne (hhelper j)] using hinput j
          have htail' := (ih (helper,1) out.1 hneq.symm hhelper hout _ hu
            (by simp)).mp htail
          rw [input_update input a helper _ hhelper] at htail'
          simp only [read,Function.update_self,coord_pair_one] at htail'
          have hg := ((eqCoords_realize _ _ _).mp hgen).2.2
          have ho := ((eqCoords_realize _ _ _).mp houty).2.2
          rw [read_update _ _ _ _ (hhelper i)] at hg
          rw [read_update _ _ _ _ hneq] at ho
          simp only [read,Function.update_self,coord_pair_zero] at hg
          simp only [read,Function.update_self,coord_pair_two] at ho
          simpa [listEval_cons,letterEval,← hg,htail'] using ho
        · intro hv
          let t := listEval (fun i => read a (input i)) L
          let g := read a (input i)
          refine ⟨.inr (g,t,1),rfl,?_,?_,?_⟩
          · apply (eqCoords_realize _ _ _).mpr
            simp [read,Function.update_of_ne (hhelper i),hinput i,g]
          · apply (eqCoords_realize _ _ _).mpr
            simp only [Function.update_of_ne hneq,Function.update_self,usable_pair,husable,
              true_and,read,coord_pair_two]
            simpa [g,t,read,listEval_cons,letterEval] using hv
          · apply (ih (helper,1) out.1 hneq.symm hhelper hout _
              (fun j => by simpa only [Function.update_of_ne (hhelper j)] using hinput j)
              (by simp)).mpr
            rw [input_update input a helper _ hhelper]
            simp [read,t]
      · constructor
        · rintro ⟨y,hys,hgen,houty,htail⟩
          obtain ⟨g,t,rfl⟩ := (sort_one_iff y).mp hys
          have hu (j : Fin k) : Usable (Function.update a helper (.inr (g,t,1)) (input j).1) := by
            simpa only [Function.update_of_ne (hhelper j)] using hinput j
          have htail' := (ih (helper,2) out.1 hneq.symm hhelper hout _ hu
            (by simp)).mp htail
          rw [input_update input a helper _ hhelper] at htail'
          simp only [read,Function.update_self,coord_pair_two] at htail'
          have hg := ((eqCoords_realize _ _ _).mp hgen).2.2
          have ho := ((eqCoords_realize _ _ _).mp houty).2.2
          rw [read_update _ _ _ _ (hhelper i)] at hg
          rw [read_update _ _ _ _ hneq] at ho
          simp only [read,Function.update_self,coord_pair_zero] at hg
          simp only [read,Function.update_self,coord_pair_one] at ho
          rw [← hg,← ho] at htail'
          simpa [listEval_cons,letterEval] using (eq_inv_mul_iff_mul_eq.mpr htail')
        · intro hv
          let g := read a (input i)
          let t := read a out
          refine ⟨.inr (g,t,1),rfl,?_,?_,?_⟩
          · apply (eqCoords_realize _ _ _).mpr
            simp [read,Function.update_of_ne (hhelper i),hinput i,g]
          · apply (eqCoords_realize _ _ _).mpr
            simp [read,Function.update_of_ne hneq,husable,t]
          · apply (ih (helper,2) out.1 hneq.symm hhelper hout _
              (fun j => by simpa only [Function.update_of_ne (hhelper j)] using hinput j)
              (by simp)).mpr
            rw [input_update input a helper _ hhelper]
            simp only [read,Function.update_self,coord_pair_two]
            change g*t = _
            exact eq_inv_mul_iff_mul_eq.mp (by simpa [g,t,listEval_cons,letterEval] using hv)

/-- A closed test for any word relation on implicit coordinates. -/
def wordFormula (input : Fin k → Coordinate d) (out helper : Fin d) (w : GroupWord k) : Formula d :=
  .ex out (.and (.atom (.test 4) out out)
    (.and (.atom (oneTest 0) out out) (evaluationFormula input (linearize w) (out,0) helper)))

theorem wordFormula_correct (input : Fin k → Coordinate d) (out helper : Fin d)
    (hneq : out ≠ helper) (hout : ∀ i,(input i).1 ≠ out)
    (hhelper : ∀ i,(input i).1 ≠ helper) (w : GroupWord k)
    (a : Fin d → GadgetVertex G) (hinput : ∀ i,Usable (a (input i).1)) :
    (wordFormula input out helper w).Realize a ↔
      w.eval (fun i => read a (input i))=1 := by
  constructor
  · rintro ⟨x,hxs,hx1,hword⟩
    have hx1' : (oneTest 0).Realize x x := by
      simpa only [Formula.Realize,Function.update_self] using hx1
    have hu : Usable x := ((oneTest_realize 0 x).mp hx1').1
    have hx : coord 0 x=1 := ((oneTest_realize 0 x).mp hx1').2
    have hh := (evaluationFormula_correct input (linearize w) (out,0) helper hneq hout hhelper _
      (fun i => by simpa only [Function.update_of_ne (hout i)] using hinput i)
      (by simpa using hu)).mp hword
    rw [input_update input a out x hout,linearize_eval] at hh
    simpa only [read,Function.update_self,hx] using hh.symm
  · intro hw
    refine ⟨.inl 1,by simp [Formula.Realize,Rel.Realize,vertexSort],?_,?_⟩
    · simpa only [Formula.Realize,Function.update_self] using
        (oneTest_realize 0 (Sum.inl (1:G))).mpr ⟨usable_group _,rfl⟩
    · apply (evaluationFormula_correct input (linearize w) (out,0) helper hneq hout hhelper _
        (fun i => by simpa only [Function.update_of_ne (hout i)] using hinput i)
        (by simp)).mpr
      rw [input_update input a out _ hout,linearize_eval,hw]
      simp [read]

/-- Stable graph colors test the full generated-subgroup type of any marked
implicit coordinates while only two graph slots are reserved as helpers. -/
theorem initialII_eq_of_sameGraph [Fintype G] [Fintype H] [Nontrivial G] [Nontrivial H]
    (hd : 3 ≤ d) {a : Fin d → GadgetVertex G} {b : Fin d → GadgetVertex H}
    (h : SameGraph a b) (input : Fin k → Coordinate d) (out helper : Fin d)
    (hneq : out ≠ helper) (hout : ∀ i,(input i).1 ≠ out)
    (hhelper : ∀ i,(input i).1 ≠ helper)
    (ha : ∀ i,Usable (a (input i).1)) (hb : ∀ i,Usable (b (input i).1)) :
    initialII k (fun i => read a (input i)) = initialII k (fun i => read b (input i)) := by
  classical
  funext w
  apply decide_eq_decide.mpr
  rw [← wordFormula_correct input out helper hneq hout hhelper w a ha,
    ← wordFormula_correct input out helper hneq hout hhelper w b hb]
  exact Formula.realize_iff hd _ h

end GroupWL.GadgetWords
