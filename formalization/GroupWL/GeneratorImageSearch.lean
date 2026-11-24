import GroupWL.Identification
import GroupWL.TensorGenerators
import Mathlib.Data.Fintype.EquivFin

/-! # Finite isomorphism search through generator images

The candidate space consists of images of the displayed generators. Each
candidate is expanded by recorded source words, then verified directly as a
bijection preserving multiplication. The correctness proof does not assume
that the candidate map is a homomorphism before validation.
-/
namespace GroupWL.GeneratorImageSearch

open Refinement
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] {k : ℕ}

/-- One recorded word for every element of the source group. -/
structure Representatives (a : Fin k → G) where
  word : G → GroupWord k
  evaluates : ∀ x,(word x).eval a=x

noncomputable def Representatives.of_generates {a : Fin k → G} (ha : Generates a) :
    Representatives a where
  word x := Classical.choose (ha x)
  evaluates x := Classical.choose_spec (ha x)

/-- Generator images determine a group homomorphism uniquely. -/
theorem hom_ext {a : Fin k → G} (ha : Generates a) {f g : G →* H}
    (h : ∀ i,f (a i)=g (a i)) : f=g := by
  have he : f ∘ a = g ∘ a := funext h
  ext x
  obtain ⟨w,rfl⟩ := ha x
  rw [← GroupWord.eval_hom,← GroupWord.eval_hom,he]

theorem mulEquiv_ext {a : Fin k → G} (ha : Generates a) {f g : G ≃* H}
    (h : ∀ i,f (a i)=g (a i)) : f=g := by
  have he : f.toMonoidHom=g.toMonoidHom := hom_ext ha h
  ext x
  exact congrArg (fun h : G →* H => h x) he

/-- The injection giving the `|H|^k` isomorphism-count bound. -/
def imagesEmbedding {a : Fin k → G} (ha : Generates a) :
    (G ≃* H) ↪ (Fin k → H) where
  toFun e := e ∘ a
  inj' := fun e f h => mulEquiv_ext ha (congrFun h)

theorem card_isomorphisms_le [Fintype G] [Fintype H] {a : Fin k → G} (ha : Generates a) :
    Nat.card (G ≃* H) ≤ Fintype.card H ^ k := by
  have he := Nat.card_le_card_of_injective (imagesEmbedding (H := H) ha)
    (imagesEmbedding (H := H) ha).injective
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin] using he

/-- Expanding a proposed tuple of images by the recorded words. -/
def candidate {a : Fin k → G} (R : Representatives a) (b : Fin k → H) : G → H :=
  fun x => (R.word x).eval b

def Valid {a : Fin k → G} (R : Representatives a) (b : Fin k → H) : Prop :=
  candidate R b 1=1 ∧
    (∀ x y,candidate R b (x*y)=candidate R b x*candidate R b y) ∧
    Function.Bijective (candidate R b)

noncomputable def toMulEquiv {a : Fin k → G} (R : Representatives a) (b : Fin k → H)
    (h : Valid R b) : G ≃* H :=
  MulEquiv.ofBijective
    ({ toFun := candidate R b, map_one' := h.1,map_mul' := h.2.1 } : G →* H) h.2.2

@[simp] theorem candidate_images {a : Fin k → G} (R : Representatives a)
    (e : G ≃* H) : candidate R (e ∘ a)=e := by
  funext x
  change (R.word x).eval (e.toMonoidHom ∘ a)=e x
  rw [GroupWord.eval_hom,R.evaluates]
  rfl

theorem valid_images {a : Fin k → G} (R : Representatives a) (e : G ≃* H) :
    Valid R (e ∘ a) := by
  unfold Valid
  rw [candidate_images]
  exact ⟨e.map_one,e.map_mul,e.bijective⟩

/-- Every isomorphism occurs in the finite generator-image candidate search. -/
theorem exists_valid_iff {a : Fin k → G} (R : Representatives a) :
    (∃ b : Fin k → H,Valid R b) ↔ Nonempty (G ≃* H) :=
  ⟨fun ⟨b,hb⟩ => ⟨toMulEquiv R b hb⟩,fun ⟨e⟩ => ⟨e ∘ a,valid_images R e⟩⟩

/-- On equal-order groups, injectivity suffices for the direct table check. -/
def ValidEqualOrder {a : Fin k → G} (R : Representatives a) (b : Fin k → H) : Prop :=
  candidate R b 1=1 ∧
    (∀ x y,candidate R b (x*y)=candidate R b x*candidate R b y) ∧
    ∀ x y,candidate R b x=candidate R b y → x=y

theorem validEqualOrder_iff [Fintype G] [Fintype H] (hc : Fintype.card G=Fintype.card H)
    {a : Fin k → G} (R : Representatives a) (b : Fin k → H) :
    ValidEqualOrder R b ↔ Valid R b := by
  constructor
  · rintro ⟨h1,hm,hi⟩
    refine ⟨h1,hm,hi,?_⟩
    exact ((Fintype.bijective_iff_injective_and_card (candidate R b)).mpr ⟨hi,hc⟩).2
  · rintro ⟨h1,hm,hi,_⟩
    exact ⟨h1,hm,hi⟩

instance validEqualOrderDecidable [Fintype G] [DecidableEq G] [DecidableEq H]
    {a : Fin k → G} (R : Representatives a) (b : Fin k → H) : Decidable (ValidEqualOrder R b) :=
  inferInstanceAs (Decidable (_ ∧ (∀ x y,_) ∧ ∀ x y,_ → _))

/-- An executable finite test once source representatives are supplied. -/
def search [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    {a : Fin k → G} (R : Representatives a) : Bool :=
  decide (∃ b : Fin k → H,ValidEqualOrder R b)

theorem search_correct [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H]
    (hc : Fintype.card G=Fintype.card H) {a : Fin k → G} (R : Representatives a) :
    search (H := H) R=true ↔ Nonempty (G ≃* H) := by
  simp only [search,decide_eq_true_eq]
  rw [← exists_valid_iff R]
  exact exists_congr fun b => validEqualOrder_iff hc R b

/-- Search has exactly this many proposed generator-image tuples. -/
theorem candidate_count [Fintype H] :
    Fintype.card (Fin k → H)=Fintype.card H ^ k := by simp

end GroupWL.GeneratorImageSearch
