import GroupWL.FiniteWordTypes

/-! # Executable generator tests and image expansion using finite subgroup tables

Paired-subgroup saturation avoids recording potentially enormous word expressions.
It stores at most the product of the group orders many pairs, and the existing
finite saturation bound is explicit. No choice of representative words is used.
-/
namespace GroupWL.FiniteImageSearch

open Refinement FiniteWordTypes
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H] {k : ℕ}

/-- A finite test for whether the displayed tuple generates the whole group. -/
def generates (a : Fin k → G) : Bool :=
  decide (∀ x : G, (x,x) ∈ explore a a (Fintype.card (G×G)))

theorem generates_correct (a : Fin k → G) : generates a=true ↔ Generates a := by
  simp only [generates, decide_eq_true_eq]
  constructor
  · intro h x
    obtain ⟨w,hw⟩ := explore_sound a a _ (x,x) (h x)
    exact ⟨w,congrArg Prod.fst hw⟩
  · intro h x
    obtain ⟨w,rfl⟩ := h x
    exact eval_mem_explore a a w

/-- Extend arbitrary proposed generator images by the first matching entry
in a finite paired-subgroup table; use the identity if there is no match. -/
def expand (enum : List H) (a : Fin k → G) (b : Fin k → H) (x : G) : H :=
  (enum.find? (fun y => decide ((x,y) ∈ explore a b (Fintype.card (G×H))))).getD 1

/-- If the images come from a homomorphism, finite expansion recovers that
homomorphism exactly. The search does not assume arbitrary images are consistent. -/
theorem expand_images (enum : List H) (henum : ∀ y,y ∈ enum)
    {a : Fin k → G} (ha : Generates a) (f : G →* H) :
    expand enum a (f ∘ a)=f := by
  funext x
  have hex : (x,f x) ∈ explore a (f ∘ a) (Fintype.card (G×H)) := by
    obtain ⟨w,rfl⟩ := ha x
    simpa only [GroupWord.eval_hom] using eval_mem_explore a (f ∘ a) w
  cases he : enum.find? (fun y => decide ((x,y) ∈ explore a (f ∘ a)
      (Fintype.card (G×H)))) with
  | none =>
      have hn := List.find?_eq_none.mp he (f x) (henum (f x))
      exact False.elim (hn (by simpa only [decide_eq_true_eq] using hex))
  | some y =>
      have hy := List.find?_some he
      simp only [decide_eq_true_eq] at hy
      obtain ⟨w,hw⟩ := explore_sound a (f ∘ a) _ (x,y) hy
      have hx := congrArg Prod.fst hw
      have hz := congrArg Prod.snd hw
      change w.eval a=x at hx
      change w.eval (f ∘ a)=y at hz
      rw [GroupWord.eval_hom,hx] at hz
      simpa only [expand,he,Option.getD_some] using hz.symm

/-- A direct finite multiplication-table check for a proposed expanded map. -/
def Valid (enum : List H) (a : Fin k → G) (b : Fin k → H) : Prop :=
  expand enum a b 1=1 ∧
    (∀ x y,expand enum a b (x*y)=expand enum a b x*expand enum a b y) ∧
    ∀ x y,expand enum a b x=expand enum a b y → x=y

instance validDecidable (enum : List H) (a : Fin k → G) (b : Fin k → H) :
    Decidable (Valid enum a b) :=
  inferInstanceAs (Decidable (_ ∧ (∀ x y,_) ∧ ∀ x y,_ → _))

def search (enum : List H) (a : Fin k → G) : Bool :=
  decide (∃ b : Fin k → H,Valid enum a b)

/-- The executable table search decides isomorphism on equal-order groups. -/
theorem search_correct (enum : List H) (henum : ∀ y,y ∈ enum)
    {a : Fin k → G} (ha : Generates a) (hc : Fintype.card G=Fintype.card H) :
    search enum a=true ↔ Nonempty (G ≃* H) := by
  simp only [search,decide_eq_true_eq]
  constructor
  · rintro ⟨b,h1,hm,hi⟩
    have hb := (Fintype.bijective_iff_injective_and_card (expand enum a b)).mpr ⟨hi,hc⟩
    exact ⟨MulEquiv.ofBijective
      ({toFun := expand enum a b,map_one' := h1,map_mul' := hm} : G →* H) hb⟩
  · rintro ⟨f⟩
    refine ⟨f ∘ a,?_⟩
    unfold Valid
    rw [show expand enum a (f ∘ a)=f from expand_images enum henum ha f.toMonoidHom]
    exact ⟨f.map_one,f.map_mul,fun x y h => f.injective h⟩

end GroupWL.FiniteImageSearch
